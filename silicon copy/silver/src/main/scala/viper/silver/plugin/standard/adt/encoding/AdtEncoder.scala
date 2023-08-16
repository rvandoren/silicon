// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt.encoding

import viper.silver.ast._
import viper.silver.ast.utility.rewriter.{StrategyBuilder, Traverse}
import viper.silver.plugin.standard.adt._

import scala.annotation.tailrec


/**
  * This class implement the encoder used to encode ADT AST nodes to ordinary AST nodes.
  *
  * @param program The program containing ADT AST nodes, we want to encode.
  */
class AdtEncoder(val program: Program) extends AdtNameManager {

  /**
    * This is field holding the mappings of the adt constructors tag identifier.
    */
  private val tagMapping: Map[String, Map[String, Int]] = (program.extensions collect {
    case a: Adt => (a.name, a.constructors.map(_.name).sorted.zipWithIndex.toMap)
  }).toMap

  /**
    * This method encodes all ADT related AST nodes to normal AST nodes.
    *
    * @return The encoded program.
    */
  def encode(): Program = {

    // In a first step encode all adt top level declarations and constructor calls
    var newProgram: Program = StrategyBuilder.Slim[Node]({
      case p@Program(domains, fields, functions, predicates, methods, extensions) =>
        val remainingExtensions = extensions filter { case _: Adt => false; case _ => true }
        val encodedAdtsAsDomains: Seq[Domain] = extensions collect { case a: Adt => encodeAdtAsDomain(a) }
        Program(domains ++ encodedAdtsAsDomains, fields, functions, predicates, methods, remainingExtensions)(p.pos, p.info, p.errT)
      case aca: AdtConstructorApp => encodeAdtConstructorApp(aca)
      case ada: AdtDestructorApp => encodeAdtDestructorApp(ada)
      case ada: AdtDiscriminatorApp => encodeAdtDiscriminatorApp(ada)
    }, Traverse.BottomUp).execute(program)

    // In a second step encode all occurrences of AdtType's as DomainType's
    newProgram = encodeAllAdtTypeAsDomainType(newProgram)

    // In a third step generate transitivity axioms if contains function is derived for at least one adt
    if (containsFunctionIsDerived) {
      val domains = newProgram.domains ++ Seq(generateContainsTransitivityDomain(newProgram))
      newProgram = newProgram.copy(domains = domains)(newProgram.pos, newProgram.info, newProgram.errT)
    }

    newProgram
  }

  /**
    * This method return the tag identifier given a adt constructor name and its correpsonding adt name
    *
    * @param adtName   The name of the adt
    * @param contrName The name of the adt constructor we want the tag identifier
    * @return The queried tag identifier
    */
  private def getTag(adtName: String)(contrName: String) = tagMapping(adtName)(contrName)

  /**
    * This method takes an ADT and encodes it as a Domain. Especially it does
    *   1. Maps Adt to Domain
    *   2. Maps AdtConstructor -> DomainFunc
    *   3. Adds destructor declarations encoded as domain functions
    *   4. Adds a tag functions encoded as domain functions
    *   5. Generates corresponding axioms for injectivity, exclusivity and the tag function
    *   6. Generates axioms for derived functions
    *
    * @param adt The ADT to encode
    * @return An the encoded ADT as a domain
    */
  private def encodeAdtAsDomain(adt: Adt): Domain = {
    adt match {
      case Adt(name, constructors, typVars, derivingInfo) =>
        val domain = Domain(name, null, null, typVars)(adt.pos, adt.info, adt.errT)
        val functions: Seq[DomainFunc] = (constructors map encodeAdtConstructorAsDomainFunc(domain)) ++
          (constructors flatMap generateDestructorDeclarations(domain)) ++ Seq(generateTagDeclaration(domain))
        val axioms = (constructors flatMap generateInjectivityAxiom(domain)) ++
          (constructors map generateTagAxiom(domain)) ++ Seq(generateExclusivityAxiom(domain)(constructors))
        val derivingAxioms = if (derivingInfo.contains(getContainsFunctionName))
          constructors filter (_.formalArgs.nonEmpty) map generateContainsAxiom(domain, derivingInfo(getContainsFunctionName)._2) else Seq.empty
        domain.copy(functions = functions, axioms = axioms ++ derivingAxioms)(adt.pos, adt.info, adt.errT)
    }
  }

  /**
    * This method creates a local variable given a type. One can specify the name of the local variable via the optional
    * argument 'name'. By default the name is 't'.
    *
    * @param typ  The type for which one wants to generate a local variable
    * @param name Optional argument specifying the name og the local variable
    * @return A local variable typed as 'typ' and with name 'name', if specified
    */
  private def localVarTFromType(typ: Type, name: Option[String] = None) = {
    name match {
      case Some(str) => LocalVar(str, typ)(_, _, _)
      case None => LocalVar("t", typ)(_, _, _)
    }
  }

  /**
    * This method creates a local variable declaration given a type. One can specify the name of the local variable
    * via the optional argument 'name'. By default the name is 't'.
    *
    * @param typ  The type for which one wants to generate a local variable declaration
    * @param name Optional argument specifying the name og the local variable declaration
    * @return A local variable declaration typed as 'typ' and with name 'name', if specified
    */
  private def localVarTDeclFromType(typ: Type, name: Option[String] = None) = {
    name match {
      case Some(str) => LocalVarDecl(str, typ)(_, _, _)
      case None => LocalVarDecl("t", typ)(_, _, _)
    }
  }

  /**
    * This method encodes an ADT constructor as a domain function
    *
    * @param domain The domain the encoded constructor belongs to
    * @param ac     The ADT constructor to encode
    * @return An encoded ADT constructor as a domain function
    */
  private def encodeAdtConstructorAsDomainFunc(domain: Domain)(ac: AdtConstructor): DomainFunc = {
    ac match {
      case AdtConstructor(name, formalArgs) =>
        DomainFunc(name, formalArgs, encodeAdtTypeAsDomainType(ac.typ))(ac.pos, ac.info, domain.name, ac.errT)
    }
  }

  /**
    * This methods encode an ADT constructor application as a domain function application
    *
    * @param aca The constructor application
    * @return The constructor application encoded as a domain function application
    */
  private def encodeAdtConstructorApp(aca: AdtConstructorApp): DomainFuncApp = {
    DomainFuncApp(
      aca.name,
      aca.args,
      aca.typVarMap
    )(aca.pos, aca.info, aca.typ, aca.adtName, aca.errT)
  }


  /**
    * This method generates destructor declarations for a corresponding ADT constructor
    *
    * @param domain the domain the encoded constructor belongs to
    * @param ac     the adt constructor for which we want to generate destructor declarations
    * @return A sequence of destructor declarations, empty if constructor has no arguments
    */
  private def generateDestructorDeclarations(domain: Domain)(ac: AdtConstructor): Seq[DomainFunc] = {
    assert(domain.name == ac.adtName, "AdtEncoder: An error in the ADT encoding occurred.")
    ac.formalArgs.map { lv =>
      val args = Seq(localVarTDeclFromType(encodeAdtTypeAsDomainType(ac.typ))(ac.pos, ac.info, ac.errT))
      val ttyp = lv.typ match {
        case a: AdtType => encodeAdtTypeAsDomainType(a)
        case d => d
      }
      DomainFunc(
        getDestructorName(ac.adtName, lv.name),
        args,
        ttyp
      )(ac.pos, ac.info, ac.adtName, ac.errT)
    }
  }

  /**
    * This methods encode an ADT destructor application as a domain function application
    *
    * @param ada The destructor application
    * @return The destructor application encoded as a domain function application
    */
  private def encodeAdtDestructorApp(ada: AdtDestructorApp): DomainFuncApp = {
    DomainFuncApp(
      getDestructorName(ada.adtName, ada.name),
      Seq(ada.rcv),
      ada.typVarMap
    )(ada.pos, ada.info, ada.typ, ada.adtName, ada.errT)
  }

  /**
    * This methods encode an ADT discriminator application as an equality expression
    *
    * @param ada The discriminator application
    * @return The discriminator application encoded as an equality expression
    */
  private def encodeAdtDiscriminatorApp(ada: AdtDiscriminatorApp): EqCmp = {
    val tagApp = DomainFuncApp(
      getTagName(ada.adtName),
      Seq(ada.rcv),
      ada.typVarMap
    )(ada.pos, ada.info, Int, ada.adtName, ada.errT)

    EqCmp(tagApp, IntLit(getTag(ada.adtName)(ada.name))(ada.pos, ada.info, ada.errT))(ada.pos, ada.info, ada.errT)
  }

  /**
    * This method generates the corresponding injectivity axiom for an ADT constructor.
    *
    * axiom {
    *     forall p_1: T_1, ..., p_n: T_n :: {C(p_1, ..., p_n)} p_i == D_Ci(C(p_1, ..., p_n))
    * }
    *
    * where C is the ADT constructor, D_i the destructor for i-th argument of C
    *
    * @param domain The domain the encoded constructor belongs to
    * @param ac     The adt constructor for which we want to generate the injectivity axioms
    * @return A sequence of injectivity axiom
    */
  private def generateInjectivityAxiom(domain: Domain)(ac: AdtConstructor): Seq[AnonymousDomainAxiom] = {
    assert(domain.name == ac.adtName, "AdtEncoder: An error in the ADT encoding occurred.")
    val localVarDecl = ac.formalArgs.collect { case l: LocalVarDecl => l }
    val localVars = ac.formalArgs.map { lv =>
      lv.typ match {
        case a: AdtType => localVarTFromType(encodeAdtTypeAsDomainType(a), Some(lv.name))(ac.pos, ac.info, ac.errT)
        case d => localVarTFromType(d, Some(lv.name))(ac.pos, ac.info, ac.errT)
      }
    }
    assert(localVarDecl.size == localVars.size, "AdtEncoder: An error in the ADT encoding occurred.")

    val constructorApp = DomainFuncApp(
      ac.name,
      localVars,
      defaultTypeVarsFromDomain(domain)
    )(ac.pos, ac.info, encodeAdtTypeAsDomainType(ac.typ), ac.adtName, ac.errT)
    val trigger = Trigger(Seq(constructorApp))(ac.pos, ac.info, ac.errT)

    localVars.map { lv =>
      val right = DomainFuncApp(
        getDestructorName(ac.adtName, lv.name),
        Seq(constructorApp),
        defaultTypeVarsFromDomain(domain)
      )(ac.pos, ac.info, lv.typ, ac.adtName, ac.errT)
      val eq = EqCmp(lv, right)(ac.pos, ac.info, ac.errT)
      val forall = Forall(localVarDecl, Seq(trigger), eq)(ac.pos, ac.info, ac.errT)
      AnonymousDomainAxiom(forall)(ac.pos, ac.info, ac.adtName, ac.errT)
    }
  }

  /**
    * This method generates the corresponding exclusivity axioms for a sequence of constructors.
    *
    * axiom {
    * forall t: AdtType :: {tag(t)}{D_11(t)}...{D_nn(t)}
    *       t == C_1(D_11(t), D_1n(t)) || ... || t == C_n(D_n1(t), D_nn(t))
    * }
    *
    * where D_ij is the destructor of the j-th argument of constructor C_i
    *
    * @param domain The domain the encoded ADT constructors belongs to
    * @param acs    The sequence adt constructor for which we want to generate the exclusivity axioms
    * @return The exclusivity axiom
    */
  private def generateExclusivityAxiom(domain: Domain)(acs: Seq[AdtConstructor]): AnonymousDomainAxiom = {
    assert(acs.map(domain.name == _.adtName).forall(identity), "AdtEncoder: An error in the ADT encoding occurred.")

    val localVarDecl = localVarTDeclFromType(domainTypeFromDomain(domain))(domain.pos, domain.info, domain.errT)
    val localVar = localVarTFromType(domainTypeFromDomain(domain))(domain.pos, domain.info, domain.errT)
    val tagApp = DomainFuncApp(
      getTagName(domain.name),
      Seq(localVar),
      (domain.typVars zip domain.typVars).toMap
    )(domain.pos, domain.info, Int, domain.name, domain.errT)

    var destructorCalls: Seq[DomainFuncApp] = Seq()
    val rhss = acs.map { ac =>
      destructorCalls = ac.formalArgs.map { lv =>
        DomainFuncApp(
          getDestructorName(domain.name, lv.name),
          Seq(localVar),
          defaultTypeVarsFromDomain(domain)
        )(domain.pos, domain.info, lv.typ, domain.name, domain.errT)
      }
      DomainFuncApp(
        ac.name,
        destructorCalls,
        defaultTypeVarsFromDomain(domain)
      )(domain.pos, domain.info, ac.typ, domain.name, domain.errT)
    }

    val equalities = rhss.map { rhs =>
      EqCmp(localVar, rhs)(rhs.pos, rhs.info, rhs.errT)
    }
      .foldLeft(FalseLit()(domain.pos, domain.info, domain.errT): Exp)({
        (acc, next) => Or(acc, next)(domain.pos, domain.info, domain.errT)
      })

    val triggers = (Seq(tagApp) ++ destructorCalls).map { t => Trigger(Seq(t))(domain.pos, domain.info, domain.errT) }

    AnonymousDomainAxiom(
      Forall(Seq(localVarDecl), triggers, equalities)(domain.pos, domain.info, domain.errT)
    )(domain.pos, domain.info, domain.name, domain.errT)
  }

  /**
    * This method generates the corresponding tag function for an ADT encoded as a domain
    *
    * @param domain The domain that encodes the ADT for which we want a tag function
    * @return The tag function encoded as a domain function
    */
  private def generateTagDeclaration(domain: Domain): DomainFunc = {
    DomainFunc(
      getTagName(domain.name),
      Seq(localVarTDeclFromType(domainTypeFromDomain(domain))(domain.pos, domain.info, domain.errT)),
      Int
    )(domain.pos, domain.info, domain.name, domain.errT)
  }

  /**
    * This method generates the corresponding tag axiom for a ADT constructor
    *
    * axiom {
    *   forall p_1: T1 , p_2: T2 ,..., p_n: Tn :: {C(p_1,..,p_n)} tag(C(p_1,..,p_n)) = i
    * }
    *
    * where i is specified by the parameter 'tag'.
    *
    * @param domain The domain that encodes the ADT the constructor belongs to for which we want a tag axiom
    * @param ac     An ADT constructor
    * @return The generated tag axiom
    */
  private def generateTagAxiom(domain: Domain)(ac: AdtConstructor): AnonymousDomainAxiom = {
    assert(domain.name == ac.adtName, "AdtEncoder: An error in the ADT encoding occurred.")

    val localVarDecl = ac.formalArgs.collect { case l: LocalVarDecl => l }
    val localVars = ac.formalArgs.map { lv =>
      lv.typ match {
        case a: AdtType => localVarTFromType(encodeAdtTypeAsDomainType(a), Some(lv.name))(ac.pos, ac.info, ac.errT)
        case d => localVarTFromType(d, Some(lv.name))(ac.pos, ac.info, ac.errT)
      }
    }
    assert(localVarDecl.size == localVars.size, "AdtEncoder: An error in the ADT encoding occurred.")

    val constructorApp = DomainFuncApp(
      ac.name,
      localVars,
      defaultTypeVarsFromDomain(domain)
    )(ac.pos, ac.info, encodeAdtTypeAsDomainType(ac.typ), ac.adtName, ac.errT)

    val trigger = Trigger(Seq(constructorApp))(ac.pos, ac.info, ac.errT)

    val tagApp = DomainFuncApp(
      getTagName(ac.adtName),
      Seq(constructorApp),
      defaultTypeVarsFromDomain(domain)
    )(ac.pos, ac.info, Int, ac.adtName, ac.errT)

    val right = IntLit(getTag(domain.name)(ac.name))(ac.pos, ac.info, ac.errT)
    val eq = EqCmp(tagApp, right)(ac.pos, ac.info, ac.errT)
    val forall = Forall(localVarDecl, Seq(trigger), eq)(ac.pos, ac.info, ac.errT)

    if (ac.formalArgs.nonEmpty) {
      AnonymousDomainAxiom(forall)(ac.pos, ac.info, ac.adtName, ac.errT)
    } else {
      AnonymousDomainAxiom(eq)(ac.pos, ac.info, ac.adtName, ac.errT)
    }

  }

  /**
    * This is a helper method to check if the contains function is derived for at least one adt, namely
    *
    * @return Return true if the contains function is derived for at least one adt
    */
  private def containsFunctionIsDerived: Boolean = program.extensions.exists {
    case a: Adt => a.derivingInfo.contains(getContainsFunctionName)
  }

  /**
    * This method generates the corresponding contains axiom for a ADT constructor
    *
    * axiom {
    *   forall p_1: T1, ..., p_n: Tn :: {C(p_1, ..., p_n)} contains(p_1, C′) && ... && contains(p_n, C′)
    * }
    *
    * where C′ =  C(p_1, ..., p_n).
    *
    * @param domain    The domain that encodes the ADT the constructor belongs to for which we want a contains axiom
    * @param blockList A list of destructor identifiers that should not be considered for the contains relations
    * @param ac        An ADT constructor
    * @return The generated contains axiom
    */
  private def generateContainsAxiom(domain: Domain, blockList: Set[String])(ac: AdtConstructor): AnonymousDomainAxiom = {
    assert(domain.name == ac.adtName, "AdtEncoder: An error in the ADT encoding occurred.")
    assert(ac.formalArgs.nonEmpty, "AdtEncoder: An error in the ADT encoding occurred.")

    val localVarDecl = ac.formalArgs.collect { case l: LocalVarDecl => l }
    val localVars = ac.formalArgs.map { lv =>
      lv.typ match {
        case a: AdtType => localVarTFromType(encodeAdtTypeAsDomainType(a), Some(lv.name))(ac.pos, ac.info, ac.errT)
        case d => localVarTFromType(d, Some(lv.name))(ac.pos, ac.info, ac.errT)
      }
    }
    assert(localVarDecl.size == localVars.size, "AdtEncoder: An error in the ADT encoding occurred.")

    val constructorApp = DomainFuncApp(
      ac.name,
      localVars,
      defaultTypeVarsFromDomain(domain)
    )(ac.pos, ac.info, encodeAdtTypeAsDomainType(ac.typ), ac.adtName, ac.errT)

    val trigger = Trigger(Seq(constructorApp))(ac.pos, ac.info, ac.errT)

    val containsApp = (lv: LocalVar) => DomainFuncApp(
      getContainsFunctionName,
      Seq(lv, constructorApp),
      Map(TypeVar("A") -> lv.typ, TypeVar("B") -> constructorApp.typ)
    )(ac.pos, ac.info, Bool, getContainsDomainName, ac.errT)

    val axiomBody = localVars.filter(lv =>
      !blockList.contains(lv.name))
        .map(containsApp)
        .foldLeft[Exp](TrueLit()(ac.pos, ac.info, ac.errT))((a, b) => And(a, b)(ac.pos, ac.info, ac.errT)
    )
    val forall = Forall(localVarDecl, Seq(trigger), axiomBody)(ac.pos, ac.info, ac.errT)

    AnonymousDomainAxiom(forall)(ac.pos, ac.info, ac.adtName, ac.errT)
  }

  /**
    * This method encodes the transitivity of the contains function. Namely it collects arguments types of
    * all contains applications as tuples, computes its transitive closure and finally the corresponding axioms.
    *
    * This ensures that we generate one axiom which encodes the transitivity of contains for each possible
    * triple of concrete types, which are used in calls to contains.
    *
    * @param program The program
    * @return The ContainsTransitivityDomain with axioms that encode transitivity
    */
  private def generateContainsTransitivityDomain(program: Program): Domain = {

    def addTransitive(s: Set[(Type, Type)]): Set[(Type, Type)] =
      s ++ (for ((x1, y1) <- s; (x2, y2) <- s if y1 == x2) yield (x1, y2))

    @tailrec
    def transitiveClosure(s: Set[(Type, Type)]): Set[(Type, Type)] = {
      val t = addTransitive(s)
      if (t.size == s.size) s else transitiveClosure(t)
    }

    def genAxiom(a: Type, b: Type, c: Type): AnonymousDomainAxiom = {
      val aVar = LocalVarDecl("a", a)()
      val bVar = LocalVarDecl("b", b)()
      val cVar = LocalVarDecl("c", c)()

      def containsApp(l: Exp, r: Exp) = DomainFuncApp(
        getContainsFunctionName,
        Seq(l, r),
        Map(
          TypeVar("A") -> l.typ,
          TypeVar("B") -> r.typ
        )
      )(NoPosition, NoInfo, Bool, getContainsDomainName, NoTrafos)

      AnonymousDomainAxiom(
        Forall(
          Seq(aVar, bVar, cVar),
          Seq(
            Trigger(
              Seq(
                containsApp(aVar.localVar, bVar.localVar),
                containsApp(bVar.localVar, cVar.localVar)
              )
            )()
          ),
          Implies(
            And(
              containsApp(aVar.localVar, bVar.localVar),
              containsApp(bVar.localVar, cVar.localVar)
            )(),
            containsApp(aVar.localVar, cVar.localVar)
          )()
        )()
      )(domainName = getContainsTransitivityDomain)
    }

    var tuples: Set[(Type, Type)] = Set.empty
    program.visit({
      case dfa@DomainFuncApp(funcname, args, _) if funcname == getContainsFunctionName && dfa.domainName == getContainsDomainName =>
        assert(args.size == 2, "AdtEncoder: An error in the ADT encoding occurred.")
        if (args.head.typ.isConcrete && args(1).typ.isConcrete) {
          tuples += ((args.head.typ, args(1).typ))
        }
    })

    var triples: Set[(Type, Type, Type)] = Set.empty
    val closure = transitiveClosure(tuples)
    for ((a, b) <- closure) {
      for ((c, d) <- closure) {
        if (b == c)
          triples += ((a, b, d))
      }
    }
    val axioms = triples.toSeq.map(a => genAxiom(a._1, a._2, a._3))

    Domain(
      getContainsTransitivityDomain,
      Seq(),
      axioms
    )()
  }

  /**
    * This method traverses the entire AST and encodes any occurrences of an AdtType as a DomainType. Additionaly
    * it handles DomainFuncApp and FuncApp specially since the argument 'typ' could also be an AdtType.
    *
    * @param program The program to encode
    * @return a program free of AdtType's
    */
  private def encodeAllAdtTypeAsDomainType[A <: Node](program: A, shouldForceCopy: Boolean = true): A = {
    StrategyBuilder.Slim[Node]({
      case at@AdtType(name, partialTypVarsMap) => DomainType(name, partialTypVarsMap)(at.typeParameters)
      case dfa@DomainFuncApp(name, args, typVarMap) =>
        DomainFuncApp(name, args, typVarMap)(dfa.pos, dfa.info, encodeAllAdtTypeAsDomainType(dfa.typ, shouldForceCopy = false), dfa.domainName, dfa.errT)
      case fa@FuncApp(funcname, args) =>
        FuncApp(funcname, args)(fa.pos, fa.info, encodeAllAdtTypeAsDomainType(fa.typ, shouldForceCopy = false), fa.errT)
    }, Traverse.BottomUp).forceCopy(shouldForceCopy).execute(program)
  }

  /** Several helper methods */
  private def encodeAdtTypeAsDomainType(adtType: AdtType): DomainType = DomainType(adtType.adtName, adtType.partialTypVarsMap)(adtType.typeParameters)

  private def domainTypeFromDomain(domain: Domain): DomainType = DomainType(domain, defaultTypeVarsFromDomain(domain))

  private def defaultTypeVarsFromDomain(domain: Domain): Map[TypeVar, Type] = (domain.typVars zip domain.typVars).toMap
}
