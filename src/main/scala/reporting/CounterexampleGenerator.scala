package viper.silicon.reporting

import viper.silver.verifier.{ApplicationEntry, ConstantEntry, MapEntry, Model, ValueEntry}
import viper.silver.ast.{LocalVar, Member, Program, Type, Resource}
import viper.silver.ast
import viper.silicon.{Map, state => st}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, PredicateID}
import viper.silicon.state.{BasicChunk, DefaultSymbolConverter, SimpleIdentifier, State, Store, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.state._
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.reporting.Converter.evaluateTerm
import viper.silver.verifier._
import viper.silver.verifier.Rational



case class CounterexampleGenerator(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, program: ast.Program) {
  println(model.entries.toString())
  val imCE = IntermediateCounterexampleModel(model, store, heap, oldHeaps, program)
  println(imCE.toString)

  val (ceStore, refOcc) = CounterexampleGenerator.detStore(store, imCE.basicVariables, imCE.allCollections)
  var ceHeaps = Seq[(String, HeapCounterexample)]()
  imCE.allBasicHeaps.reverse.foreach {case (n, h) => ceHeaps +:= ((n, CounterexampleGenerator.detHeap(h, program, imCE.allCollections, refOcc, model)))}

  lazy val DomainsAndFunctions = imCE.DomainEntries ++ imCE.nonDomainFunctions
  override def toString: String = {
    var finalString = "      Final Counterexample: \n"
    finalString += "   Store: \n"
    finalString += ceStore.storeEntries.map(x => x.toString).mkString("", "\n", "\n")
    finalString += ceHeaps.map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("")
    finalString += "   Domains: \n"
    finalString += DomainsAndFunctions.map(x => x.toString).mkString("", "\n", "\n")
    finalString
  }
}

case class IntermediateCounterexampleModel(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, program: ast.Program) {
  val basicVariables = IntermediateCounterexampleModel.detBasicVariables(model, store)
  val allSequences = IntermediateCounterexampleModel.detSequences(model)
  val allSets = IntermediateCounterexampleModel.detSets(model)
  val allMultisets = IntermediateCounterexampleModel.detMultisets(model)
  val allCollections = allSequences ++ allSets ++ allMultisets
  var allBasicHeaps = Seq(("return", BasicHeap(IntermediateCounterexampleModel.detHeap(model, heap))))
  oldHeaps.foreach {case (n, h) => allBasicHeaps +:= ((n, BasicHeap(IntermediateCounterexampleModel.detHeap(model, h.values))))}

  val DomainEntries = IntermediateCounterexampleModel.getAllDomains(model, program)
  val nonDomainFunctions = IntermediateCounterexampleModel.getAllFunctions(model, program)

  override def toString: String = {
    var finalString = "      Intermediate Counterexample: \n"
    finalString ++= "   Local Information:\n"
    if (!basicVariables.isEmpty)
      finalString += basicVariables.map(x => x.toString).mkString("", "\n", "\n")
    if (!allCollections.isEmpty)
      finalString += allCollections.map(x => x.toString).mkString("", "\n", "\n")
    if (!allBasicHeaps.filter(y => !y._2.basicHeapEntries.isEmpty).isEmpty)
      finalString += allBasicHeaps.filter(y => !y._2.basicHeapEntries.isEmpty).map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("", "\n", "\n")
    if (!DomainEntries.isEmpty || !nonDomainFunctions.isEmpty)
      finalString ++= "   Domains:\n"
    if (!DomainEntries.isEmpty)
      finalString += DomainEntries.map(x => x.toString).mkString("", "\n", "\n")
    if (!nonDomainFunctions.isEmpty)
      finalString += nonDomainFunctions.map(x => x.toString).mkString("", "\n", "\n")
    finalString
  }
}

object IntermediateCounterexampleModel {

  /**
    * Defines the final value or the indentifier of the final value for every variable in the method containing the
    * verification error.
    */
  def detBasicVariables(model: Model, store: Store): Seq[CEVariable] = {
    var res = Seq[CEVariable]()
    for ((k, v) <- store.values) {
      if (v.toString.contains('@')) {
        model.entries.get(v.toString) match {
          case Some(x) =>
            var varTyp: Option[Type] = None
            if (k.isInstanceOf[LocalVar]) {
              varTyp = Some(k.asInstanceOf[LocalVar].typ)
            }
            if (x.isInstanceOf[ConstantEntry]) {
              res +:= CEVariable(k.name, x, varTyp)
            } else if (x.isInstanceOf[ApplicationEntry]) {
              res +:= CEVariable(k.name, x, varTyp)
            } else {
              println(s"Couldn't find a ConstantEntry or ApplicationEntry for the Variable: ${k.name}")
            }
          case None => //println(s"Couldn't find an entry for the Variable: ${k.name}")
        }
      } else {
        var varTyp: Option[Type] = None
        if (k.isInstanceOf[LocalVar]) {
          varTyp = Some(k.asInstanceOf[LocalVar].typ)
        }
        res +:= CEVariable(k.name, ConstantEntry(v.toString), varTyp)
      }
    }
    if (model.entries.contains("$Ref.null")) {
      val nullRef = model.entries.get("$Ref.null").get
      if (nullRef.isInstanceOf[ConstantEntry]) {
        res +:= CEVariable("null", nullRef, Some(ast.Ref))
      }
    }
    res
  }

  /**
    * Defines every sequence that can be extracted in the model. The entries of the sequences still consist of identifiers
    * and are not assigned to their actual value. Additionally, not every sequence in the output set will be mentioned
    * in the final CE as only sequences that are used in the method containing the verification error will be mentioned there.
    */
  def detSequences(model: Model): Set[CEValue] = {
    var res = Map[String, Seq[String]]()
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq_length") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (k(0).toString -> Seq.fill(v.toString.toInt)("#undefined"))
          }
        }
      } else if (opName == "Seq_empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq())
          }
        }
      } else if (opName != "Seq_singleton" && opName != "Seq_range" && opName.startsWith("Seq_")) {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Seq_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq(k(0).toString))
          }
        }
      }
      if (opName == "Seq_range") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Seq.range(k(0).toString.toInt, k(1).toString.toInt).map(x => x.toString))
          }
        }
      }
    }
    var found = true
    while (found) {
      found = false
      for (((opName, k), v) <- tempMap) {
        if (opName == "Seq_append") {
          (res.get(k(0)), res.get(k(1))) match {
            case (Some(x), Some(y)) =>
              if (!res.contains(v)) {
                res += (v -> (x ++ y))
                tempMap -= ((opName, k))
                found = true
              }
            case (_, _) => //
          }
        } else if (opName == "Seq_take") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.take(k(1).toInt))
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        } else if (opName == "Seq_drop") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.drop(k(1).toInt))
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        } else if (opName == "Seq_index") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (k(0) -> x.updated(k(1).toInt, v))
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        } else if (opName == "Seq_update") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (k(0) -> x.updated(k(1).toInt, v))
              tempMap -= ((opName, k))
              found = true
            case _ => //
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SeqType(x))
          case None => None
        }
        var entries = Map[BigInt, String]()
        var counter = 0
        for (e <- s) {
          if (e != "#undefined") {
            entries += ((BigInt(counter), e))
          }
          counter += 1
        }
        ans += CESequence(n, BigInt(s.length), entries, s, typ)
    }
    ans
  }

  /**
    * Defines every set that can be extracted in the model. The entries of the sets still consist of identifiers
    * and are not assigned to their actual value. Additionally, not every set in the output set will be mentioned
    * in the final CE as only sets that are used in the method containing the verification error will be mentioned there.
    */
  def detSets(model: Model): Set[CEValue] = {
    var res = Map[String, Set[String]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Set())
        }
      }
      if (opName == "Set_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set(k(0).toString))
          }
        }
      }
      if (opName == "Set_card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Set())
            }
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_unionone" || opName == "Set_in") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        if (opName == "Set_unionone") {
          res.get(k(0)) match {
            case Some(x) =>
              res += (v -> x.union(Set(k(1))))
              tempMap -= ((opName, k))
            case None => //
          }
        } else if (opName == "Set_in") {
          res.get(k(1)) match {
            case Some(x) =>
              if (v.toBoolean) {
                res += (k(1) -> x.union(Set(k(0))))
              }
            case None =>
              if (v.toBoolean) {
                res += (k(1) -> Set(k(0)))
              }
          }
          tempMap -= ((opName, k))
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_union" || opName == "Set_difference" || opName == "Set_intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstSet = res.get(k(0))
        val secondSet = res.get(k(1))
        if (firstSet.isDefined && secondSet.isDefined) {
          if (opName == "Set_union") {
            res += (v -> firstSet.get.union(secondSet.get))
            tempMap -= ((opName, k))
          } else if (opName == "Set_intersection") {
            res += (v -> firstSet.get.intersect(secondSet.get))
            tempMap -= ((opName, k))
          } else if (opName == "Set_difference") {
            res += (v -> firstSet.get.diff(secondSet.get))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        var containment = Map[String, Boolean]()
        for (e <- s) {
          if (e != "#undefined") {
            containment += ((e, true))
          }
        }
        ans += CESet(n, BigInt(s.size), containment, s, typ)
    }
    ans
  }

  // a CE generator for Multisets
  def detMultisets(model: Model): Set[CEValue] = {
    var res = Map[String, scala.collection.immutable.Map[String, Int]]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Multiset_empty") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((_, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map[String, Int]())
          }
        } else if (opValues.isInstanceOf[ConstantEntry] && opValues.asInstanceOf[ConstantEntry].value != "false" && opValues.asInstanceOf[ConstantEntry].value != "true") {
          res += (opValues.asInstanceOf[ConstantEntry].value -> Map[String, Int]())
        }
      }
      if (opName == "Multiset_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Map(k(0).toString -> 1))
          }
        }
      }
      if (opName == "Multiset_count") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (!v.toString.startsWith("0")) {
              res += (k(0).toString -> res.getOrElse(k(0).toString, scala.collection.immutable.Map.empty).updated(k(1).toString, v.toString.toInt))
            }
          }
        }
      }
      if (opName == "Multiset_card") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            if (v.toString.startsWith("0")) {
              res += (k(0).toString -> Map[String, Int]())
            }
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Multiset_unionone") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        res.get(k(0)) match {
          case Some(x) =>
            res += (v -> x.updated(k(1), x.getOrElse(k(1), 0) + 1))
            tempMap -= ((opName, k))
          case None => //
        }
      }
    }
    for ((opName, opValues) <- model.entries) {
      if (opName == "Multiset_union" || opName == "Multiset_difference" || opName == "Multiset_intersection") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            tempMap += ((opName, k.map(x => x.toString)) -> v.toString)
          }
        }
      }
    }
    while (!tempMap.isEmpty) {
      for (((opName, k), v) <- tempMap) {
        val firstMultiset = res.get(k(0))
        val secondMultiset = res.get(k(1))
        if ((firstMultiset != None) && (secondMultiset != None)) {
          if (opName == "Multiset_union") {
            res += (v -> (firstMultiset.get.keySet ++ secondMultiset.get.keySet).map { key =>
              (key -> (firstMultiset.get.getOrElse(key, 0) + secondMultiset.get.getOrElse(key, 0)))
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "Multiset_intersection") {
            res += (v -> (firstMultiset.get.keySet & secondMultiset.get.keySet).map { key =>
              key -> Math.min(firstMultiset.get.get(key).get, secondMultiset.get.get(key).get)
            }.toMap)
            tempMap -= ((opName, k))
          } else if (opName == "Multiset_difference") {
            res += (v -> (firstMultiset.get.map { case (key, count) =>
              key -> (count - secondMultiset.get.getOrElse(key, 0))
            }.filter(_._2 > 0) ++ secondMultiset.get.filter { case (key, _) =>
              !firstMultiset.get.contains(key)
            }))
            tempMap -= ((opName, k))
          }
        }
      }
    }
    var ans = Set[CEValue]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        val size = s.values.sum
        ans += CEMultiset(n, BigInt(size), s, typ)
    }
    ans
  }

  /**
    * Translates a string identifier to an actual AST Viper Type.
    */
  def detASTTypeFromString(typ: String): Option[Type] = {
    typ match {
      case "Int" => Some(ast.Int)
      case "Bool" => Some(ast.Bool)
      case "Perm" => Some(ast.Perm)
      case "Ref" => Some(ast.Ref)
      case _ => None
    }
  }

  /**
    * Transforms the Heap Chunks to their Viper heap types.
    */
  def detHeap(model: Model, h: Iterable[Chunk]): Set[BasicHeapEntry] = {
    var heap = Set[BasicHeapEntry]()
    h foreach {
      case c@BasicChunk(FieldID, _, _, _, _) =>
        heap += detField(model, c)
      case c@BasicChunk(PredicateID, _, _, _, _) =>
        heap += detPredicate(model, c)
      case c@BasicChunk(id, _, _, _, _) =>
        println("This Basic Chunk couldn't be matched as a CE heap entry!")
      case c: st.QuantifiedFieldChunk =>
        val fieldName = c.id.name
        val fvf = evaluateTerm(c.snapshotMap, model)
        val possiblePerms = detPermWithInv(c.perm, model)
        model.entries.get(s"$$FVF.lookup_$fieldName") match {
          case Some(x) =>
            for ((k, v) <- x.asInstanceOf[MapEntry].options) {
              if (k(0).toString == fvf.toString) {
                val reference = k(1)
                val value = v.toString
                val tempPerm = possiblePerms.getOrElse(Seq(Seq(reference)), None)
                heap += BasicHeapEntry(Seq(reference.toString), Seq(fieldName), value, tempPerm, QPFieldType)
              }
            }
          case None => println(s"There is not QF with the snapshot: ${c.snapshotMap}")
        }
      case c: st.QuantifiedPredicateChunk =>
        val predName = c.id.name
        val fvf = evaluateTerm(c.snapshotMap, model)
        val possiblePerms = detPermWithInv(c.perm, model)
        for (pp <- possiblePerms) {
          val validBool = pp._1 match {
            case head +: tail => tail.forall(_ == head)
            case _ => true
          }
          if (validBool) {
            heap += BasicHeapEntry(Seq(predName), pp._1.head.map(x => x.toString), "#undefined", pp._2, QPPredicateType)
          }
        }
      case c@MagicWandChunk(_, _, _, _, _) =>
        heap += detMagicWand(model, c)
      case _ => println("This case is not supported in detHeap")
    }
    heap
  }

  def detField(model: Model, chunk: BasicChunk): BasicHeapEntry = {
    val recvVar = evaluateTerm(chunk.args(0), model).toString
    val fieldName = chunk.id.name
    val value = evaluateTerm(chunk.snap, model).toString
    val perm = evalPerm(chunk.perm, model)
    BasicHeapEntry(Seq(recvVar), Seq(fieldName), value, perm, FieldType)
  }

  def detPredicate(model: Model, chunk: BasicChunk): BasicHeapEntry = {
    val predSnap = chunk.snap
    val predName = chunk.id.name
    val references = chunk.args.map(x => evaluateTerm(x, model))
    var insidePredicate = Seq[String]()
    for (sub <- chunk.snap.subterms) {
      if (!sub.toString.startsWith("$t@")) {
        insidePredicate +:= sub.toString
      }
    }
    val perm = evalPerm(chunk.perm, model)
    BasicHeapEntry(Seq(predName), references.map(x => x.toString), insidePredicate.toString(), perm, PredicateType)
  }

  def detPermWithInv(perm: Term, model: Model): Map[Seq[Seq[ValueEntry]], Option[Rational]] = {
    val check = "^inv@[0-9]+@[0-9]+\\([^)]*\\)$"
    val (originals, replacements) = detTermReplacement(perm, check).toSeq.unzip
    val newPerm = perm.replace(originals, replacements)
    var allInvParameters = Map[Term, Map[Seq[ValueEntry], ValueEntry]]()
    for (inv <- replacements) {
      model.entries.get(inv.toString) match {
        case Some(x) =>
          var tempMap = Map[Seq[ValueEntry], ValueEntry]()
          for ((input, output) <- x.asInstanceOf[MapEntry].options) {
            if (input(0).toString != "else") {
              tempMap += (input -> output)
            }
          }
          allInvParameters += (inv -> tempMap)
        case None => println(s"There is no Inverse Function with the name: ${inv.toString}")
      }
    }
    val possibleInvCombinations = allInvFuncCombinations(allInvParameters)
    possibleInvCombinations.foreach {println}
    var inputsAndPerms = Map[Seq[Seq[ValueEntry]], Option[Rational]]()
    for (combination <- possibleInvCombinations) {
      val (tempOriginals, predicateInputs, tempReplacements) = combination.map { case x => (x._1, x._2, Var(SimpleIdentifier(x._3.asInstanceOf[ConstantEntry].value), x._1.sort)) }.unzip3
      val tempPerm = newPerm.replace(tempOriginals, tempReplacements)
      val evaluatedTempPerm = evalPerm(tempPerm, model)
      inputsAndPerms += (predicateInputs -> evaluatedTempPerm)
    }
    inputsAndPerms
  }

  def detTermReplacement(term: Term, pattern: String): Map[Term, Term] = {
    if (pattern.r.matches(term.toString)) {
      val outIdentifier = SimpleIdentifier(term.toString.split("\\(")(0))
      val outSort = term.asInstanceOf[App].applicable.resultSort
      Map(term -> Var(outIdentifier, outSort))
    } else {
      term.subterms.foldLeft(Map[Term, Term]()) {(acc, x) => (acc ++ detTermReplacement(x, pattern))}
    }
  }

  def allInvFuncCombinations(allInvParameters: Map[Term, Map[Seq[ValueEntry], ValueEntry]]): Seq[Seq[(Term, Seq[ValueEntry], ValueEntry)]] = {
    if (allInvParameters.isEmpty) {
      Seq(Seq())
    } else {
      val (invFun, inputOutputMap) = allInvParameters.head
      val remainingMap = allInvParameters.tail
      val remainingCombinations = allInvFuncCombinations(remainingMap)
      inputOutputMap.flatMap { inputOutput => remainingCombinations.map((invFun, inputOutput._1, inputOutput._2) +: _)}.toSeq
    }
  }

  def detMagicWand(model: Model, chunk: MagicWandChunk): BasicHeapEntry = {
    val name = chunk.id.toString
    var args = Seq[String]()
    for (x <- chunk.args) {
      val tempArg = evaluateTerm(x, model)
      var arg = tempArg.toString
      if (tempArg.isInstanceOf[OtherEntry]) {
        if (evalTermToModelEntry(x, model).isDefined) {
          arg = evalTermToModelEntry(x, model).get.toString
        } else if (evalPerm(x, model).isDefined) {
          arg = evalPerm(x, model).get.toString
        } else {
          arg = x.toString
        }
      }
      args ++= Seq(x.toString, arg)
    }
    val perm = evalPerm(chunk.perm, model)
    BasicHeapEntry(Seq(name), args, "#undefined", perm, MagicWandType)
  }

  def evalPerm(value: Term, model: Model): Option[Rational] = {
    println(value.toString)
    println(value.getClass)
    value match {
      case _: Var => evaluateTerm(value, model) match {
        case LitPermEntry(value) => Some(Rational.apply(value.numerator, value.denominator))
        case _ => None
      }
      case App(applicable, argsSeq) => None
      case IntLiteral(n) => Some(Rational.apply(n, 1))
      case NoPerm => Some(Rational.zero)
      case FullPerm => Some(Rational.one)
      case Null => None
      case a:BooleanLiteral => if (a.value) Some(Rational.apply(1, 1)) else Some(Rational.apply(0, 1))
      case _: Quantification => None //not done yet
      case Plus(v1, v2) =>
        val pr1 = evalPerm(v1, model)
        val pr2 = evalPerm(v2, model)
        if (pr1 != None && pr2 != None) {
          val num = pr1.get.numerator*pr2.get.denominator + pr2.get.numerator*pr1.get.denominator
          val den = pr1.get.denominator*pr2.get.denominator
          Some(Rational.apply(num, den))
        } else {
          None
        }
      case Minus(v1, v2) =>
        val pr1 = evalPerm(v1, model)
        val pr2 = evalPerm(v2, model)
        if (pr1 != None && pr2 != None) {
          val num = pr1.get.numerator * pr2.get.denominator - pr2.get.numerator * pr1.get.denominator
          val den = pr1.get.denominator * pr2.get.denominator
          Some(Rational.apply(num, den))
        } else {
          None
        }
      case Times(v1, v2) =>
        val pr1 = evalPerm(v1, model)
        val pr2 = evalPerm(v2, model)
        if (pr1 != None && pr2 != None) {
          val num = pr1.get.numerator * pr2.get.numerator
          val den = pr1.get.denominator * pr2.get.denominator
          Some(Rational.apply(num, den))
        } else {
          None
        }
      case Div(v1, v2) =>
        val pr1 = evalPerm(v1, model)
        val pr2 = evalPerm(v2, model)
        if (pr1 != None && pr2 != None) {
          val num = pr1.get.numerator * pr2.get.denominator
          val den = pr1.get.denominator * pr2.get.numerator
          Some(Rational.apply(num, den))
        } else {
          None
        }
      case Not(v) =>
        val pr = evalPerm(v, model)
        if (pr != None) {
          Some(Rational.apply(1-pr.get.numerator, pr.get.denominator))
        } else {
          None
        }
      case Or(t) =>
        val evalSeq = t.map(st =>
          if (evalPerm(st, model) != None) {
            Some(evalPerm(st, model).get.numerator)
          } else {
            None
          })
        if (evalSeq.contains(None)) {
          None
        } else if (evalSeq.contains(Some(BigInt(1)))) {
          Some(Rational.one)
        } else {
          Some(Rational.zero)
        }
      case And(t) =>
        val evalSeq = t.map(st =>
          if (evalPerm(st, model) != None) {
            Some(evalPerm(st, model).get.numerator)
          } else {
            None
          })
        if (evalSeq.contains(None)) {
          None
        } else if (evalSeq.contains(Some(BigInt(0)))) {
          Some(Rational.zero)
        } else {
          Some(Rational.one)
        }
      case FractionPermLiteral(r) => Some(Rational.apply(r.numerator, r.denominator))
      case FractionPerm(v1, v2) => if (v1.isInstanceOf[IntLiteral] && v2.isInstanceOf[IntLiteral]) Some(Rational(v1.asInstanceOf[IntLiteral].n, v2.asInstanceOf[IntLiteral].n)) else None
      case IsValidPermVar(v) => evalPerm(v, model)
      case IsReadPermVar(v) => evalPerm(v, model)
      case Let(_) => None
      case BuiltinEquals(t0, t1) =>
        val first = evalTermToModelEntry(t0, model)
        println(first)
        val second = evalTermToModelEntry(t1, model)
        println(second)
        if (first.toString == second.toString) {
          Some(Rational.one)
        } else {
          Some(Rational.zero)
        }
      case Less(t0, t1) =>
        val first =
          if (evalTermToModelEntry(t0, model).isDefined && evalTermToModelEntry(t0, model).get.toString.forall(Character.isDigit)) {
            Some(evalTermToModelEntry(t0, model).get.toString.toInt)
          } else {
            None
          }
        val second =
          if (evalTermToModelEntry(t1, model).isDefined && evalTermToModelEntry(t1, model).get.toString.forall(Character.isDigit)) {
            Some(evalTermToModelEntry(t1, model).get.toString.toInt)
          } else {
            None
          }
        if (first.isDefined && second.isDefined && first.get < second.get) {
          Some(Rational.one)
        } else if (first.isDefined && second.isDefined) {
          Some(Rational.zero)
        } else {
          None
        }
      case AtMost(t0, t1) =>
        val first =
          if (evalTermToModelEntry(t0, model).isDefined && evalTermToModelEntry(t0, model).get.toString.forall(Character.isDigit)) {
            Some(evalTermToModelEntry(t0, model).get.toString.toInt)
          } else {
            None
          }
        val second =
          if (evalTermToModelEntry(t1, model).isDefined && evalTermToModelEntry(t1, model).get.toString.forall(Character.isDigit)) {
            Some(evalTermToModelEntry(t1, model).get.toString.toInt)
          } else {
            None
          }
        if (first.isDefined && second.isDefined && first.get <= second.get) {
          Some(Rational.one)
        } else if (first.isDefined && second.isDefined) {
          Some(Rational.zero)
        } else {
          None
        }
      case AtLeast(t0, t1) =>
        val first =
          if (evalTermToModelEntry(t0, model).isDefined && evalTermToModelEntry(t0, model).get.toString.forall(Character.isDigit)) {
            Some(evalTermToModelEntry(t0, model).get.toString.toInt)
          } else {
            None
          }
        val second =
          if (evalTermToModelEntry(t1, model).isDefined && evalTermToModelEntry(t1, model).get.toString.forall(Character.isDigit)) {
            Some(evalTermToModelEntry(t1, model).get.toString.toInt)
          } else {
            None
          }
        if (first.isDefined && second.isDefined && first.get >= second.get) {
          Some(Rational.one)
        } else if (first.isDefined && second.isDefined) {
          Some(Rational.zero)
        } else {
          None
        }
      case PermTimes(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x * y))
      case IntPermTimes(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x * y))
      case PermIntDiv(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x / y))
      case PermPlus(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x + y))
      case PermMinus(v1, v2) =>
        evalPerm(v1, model).flatMap(x => evalPerm(v2, model).map(y => x - y))
      case PermLess(_, _) => None
      case PermAtMost(_, _) => None
      case PermMin(_, _) => None
      case SortWrapper(t, _) => evalPerm(t, model)
      case Distinct(domainFunSet) => None
      case Let(bindings, body) => None
      // Term cases that are not handled: MagicWandChunkTerm, MagicWandSnapshot,
      // PredicateTrigger, PredicateDomain, PredicatePermLookup, PredicateLookup,
      // FieldTrigger, Domain, PermLookup, Lookup,
      // trait Decl, Applicable, Function
      // trait SnapshotTerm
      // trait SetTerm, MapTerm, MultisetTerm
      case Ite(t, _, _) => evalPerm(t, model)
      case SetIn(v, s) =>
        if (model.entries.get("Set_in").get.isInstanceOf[MapEntry]) {
          val setInEntry = model.entries.get("Set_in").get.asInstanceOf[MapEntry]
          val lookupEntry = Seq(ConstantEntry(model.entries.getOrElse(v.toString, v).toString), ConstantEntry(model.entries.getOrElse(s.toString, s).toString))
          if (setInEntry.options.contains(lookupEntry)) {
            if (setInEntry.options.get(lookupEntry).get.toString.toBoolean) {
              Some(Rational.one)
            } else {
              Some(Rational.zero)
            }
          } else {
            None
          }
        } else {
          None
        }
      case _ => None
    }
  }

  def evalTermToModelEntry(value: Term, model: Model): Option[ModelEntry] = {
    value match {
      case v: Var =>
        if (v.id.name.contains("@")) {
          model.entries.get(v.id.name)
        } else {
          Some(ConstantEntry(v.id.name))
        }
      case a: App =>
        if (model.entries.get(a.applicable.id.toString).isDefined && model.entries.get(a.applicable.id.toString).get.isInstanceOf[MapEntry]) {
          val tempMap = model.entries.get(a.applicable.id.toString).get.asInstanceOf[MapEntry].options
          tempMap.get(a.args.map(t => ConstantEntry(t.toString)))
        } else {
          None
        }
      case SeqLength(t) =>
        val seqName = model.entries.get(t.toString)
        val tempMap = model.entries.get("Seq_length")
        if (seqName.isDefined && tempMap.isDefined && tempMap.get.isInstanceOf[MapEntry]) {
          tempMap.get.asInstanceOf[MapEntry].options.get(Seq(ConstantEntry(seqName.get.toString)))
        } else {
          None
        }
      case IntLiteral(t) => Some(ConstantEntry(t.intValue.toString))
      case SeqTake(t0, t1) =>
        if (evalTermToModelEntry(t0, model).isDefined) {
          Some(ConstantEntry(evalTermToModelEntry(t0, model).toString ++ " at idx " ++ t1.toString))
        } else {
          None
        }
      case SeqAt(t0, t1) => None
      case _ => None
    }
  }

  lazy val termconverter: TermConverter[String, String, String] = {
    val conv = new TermToSMTLib2Converter()
    conv.start()
    conv
  }
  lazy val symbolConverter: SymbolConverter = new DefaultSymbolConverter
  lazy val snapUnitId: String = termconverter.convert(Unit)
  lazy val nullRefId: String = termconverter.convert(Null)

  /**
    * extracts domains from a program. only the ones that are used in the program... no generics
    * it also extracts all instances (translates the generics to concrete values)
    */
  def getAllDomains(model: Model, program: ast.Program): Seq[BasicDomainEntry] = {
    var domains = Seq[ast.Domain]()
    var concreteDomains = Seq[(String, scala.collection.immutable.Map[ast.TypeVar, Type])]()
    for (el <- program) {
      el match {
        case d: ast.Domain => domains +:= d
        case ast.DomainType(name, map) =>
          if (!map.values.toSeq.exists(x => x.isInstanceOf[ast.TypeVar])) {
            concreteDomains +:= (name, map)
          }
        case ast.DomainFuncApp(name, _, map) =>
          if (!map.values.toSeq.exists(x => x.isInstanceOf[ast.TypeVar])) {
            concreteDomains +:= (name, map)
          }
        case _ => //
      }
    }
    val doms: Seq[(ast.Domain, scala.collection.immutable.Map[ast.TypeVar, Type])] = domains.flatMap(x =>
      if (x.typVars == Nil) {
        Seq((x, Map.empty[ast.TypeVar, ast.Type]))
      } else {
        concreteDomains.filter(_._1 == x.name).map(y => (x, y._2))
      })
    var domainEntries = Seq[BasicDomainEntry]()
    for ((dom, typeMap) <- doms) {
      val types = try {
        dom.typVars.map(typeMap)
      } catch {
        case _: Throwable => Seq()
      }
      val translatedFunctions = dom.functions.map(y => detFunction(model, y, typeMap, program, false))
      domainEntries +:= BasicDomainEntry(dom.name, types, translatedFunctions)
    }
    domainEntries
  }

  // extract all non domain internal functions
  def getAllFunctions(model: Model, program: ast.Program): Seq[BasicFunction] = {
    val funcs = program.collect {
      case f: ast.Function => f
    }
    funcs.map(x => detFunction(model, x, Map.empty, program, true)).toSeq
  }

  /**
    * extracts the function instances by searching for the most likely match translating the values in the internal rep
    */
  def detFunction(model: Model, func: ast.FuncLike, genmap: scala.collection.immutable.Map[ast.TypeVar, ast.Type], program: ast.Program, hd: Boolean): BasicFunction = {
    val fname = func.name
    val resTyp: ast.Type = func.typ
    val argTyp: Seq[ast.Type] = func.formalArgs.map(x => x.typ)
    model.entries.get(fname) match {
      case Some(MapEntry(m, els)) =>
        var options = Map[Seq[String], String]()
        if (hd) {
          for ((k, v) <- m) {
            options += (k.map(x => x.toString) -> v.toString)
          }
        } else {
          for ((k, v) <- m) {
            options += (k.tail.map(x => x.toString) -> v.toString)
          }
        }
        BasicFunction(fname, argTyp, resTyp, options, els.toString)
      case Some(ConstantEntry(t)) => BasicFunction(fname, argTyp, resTyp, Map.empty, t)
      case Some(ApplicationEntry(n, args)) => BasicFunction(fname, argTyp, resTyp, Map.empty, ApplicationEntry(n, args).toString)
      case Some(x) => BasicFunction(fname, argTyp, resTyp, Map.empty, x.toString)
      case None => BasicFunction(fname, argTyp, resTyp, Map.empty, "#undefined")
    }
  }
}

object CounterexampleGenerator {
  def detStore(store: Store, variables: Seq[CEVariable], collections: Set[CEValue]): (StoreCounterexample, Map[String, (String, Int)])  = {
    var refOccurences = Map[String, (String, Int)]()
    var ans = Seq[StoreEntry]()
    for ((k, _) <- store.values) {
      for (vari <- variables) {
        if (k.name == vari.name) {
          if (k.typ == ast.Ref) {
            if (refOccurences.get(vari.entryValue.toString).isDefined) {
              val (n, i) = refOccurences.get(vari.entryValue.toString).get
              if (n != k.name) {
                refOccurences += (vari.entryValue.toString -> (k.name, i + 1))
              }
            } else {
              refOccurences += (vari.entryValue.toString -> (k.name, 1))
            }
          }
          var found = false
          for (coll <- collections) {
            if (vari.entryValue.toString == coll.id) {
              ans +:= StoreEntry(k, coll)
              found = true
            }
          }
          if (!found) {
            ans +:= StoreEntry(k, vari)
          }
        }
      }
    }
    (StoreCounterexample(ans), refOccurences)
  }

  def detHeap(basicHeap: BasicHeap, program: Program, collections: Set[CEValue], refOcc: Map[String, (String, Int)], model: Model): HeapCounterexample = {
    var ans = Seq[(Resource, FinalHeapEntry)]()
    for (bhe <- basicHeap.basicHeapEntries) {
      bhe.het match {
        case FieldType | QPFieldType =>
          for ((fn, fv) <- program.fieldsByName) {
            if (fn == bhe.field.head) {
              var found = false
              for (coll <- collections) {
                if (bhe.valueID == coll.id) {
                  if (refOcc.get(bhe.reference.head).isDefined && refOcc.get(bhe.reference.head).get._2 == 1) {
                    ans +:= (fv, FieldFinalEntry(refOcc.get(bhe.reference.head).get._1, bhe.field.head, coll, bhe.perm, fv.typ))
                  } else {
                    ans +:= (fv, FieldFinalEntry(bhe.reference.head, bhe.field.head, coll, bhe.perm, fv.typ))
                  }
                  found = true
                }
              }
              if (!found) {
                if (refOcc.get(bhe.reference.head).isDefined && refOcc.get(bhe.reference.head).get._2 == 1) {
                  ans +:= (fv, FieldFinalEntry(refOcc.get(bhe.reference.head).get._1, bhe.field.head, CEVariable("#undefined", ConstantEntry(bhe.valueID), Some(fv.typ)), bhe.perm, fv.typ))
                } else {
                  ans +:= (fv, FieldFinalEntry(bhe.reference.head, bhe.field.head, CEVariable("#undefined", ConstantEntry(bhe.valueID), Some(fv.typ)), bhe.perm, fv.typ))
                }
              }
            }
          }
        case PredicateType | QPPredicateType =>
          for ((pn, pv) <- program.predicatesByName) {
            if (pn == bhe.reference.head) {
              val refNames = bhe.field.map(x =>
                if (refOcc.get(x).isDefined && refOcc.get(x).get._2 == 1) {
                  refOcc.get(x).get._1
                } else {
                  x
                })
              ans +:= (pv, PredFinalEntry(bhe.reference.head, refNames, bhe.perm))
            }
          }
        case MagicWandType | QPMagicWandType =>
          val translatedArgs = bhe.field.grouped(2).map {
            case Seq(first, second) =>
              val ceValue = collections.find(s => (s.value.toString == second || s.id == second)).getOrElse(CEVariable("#undefined", ConstantEntry(second), None))
              (first, ceValue)
          }.toMap
          for ((mw, idx) <- program.magicWandStructures.zipWithIndex) {
            val wandName = "wand@" ++ idx.toString
            if (bhe.reference(0) == wandName) {
              ans +:= (mw, WandFinalEntry(wandName, mw.left, mw.right, translatedArgs, bhe.perm))
            }
          }
        case _ => println("This type of heap entry could not be matched correctly!")
      }
    }
    HeapCounterexample(ans)
  }
}