package viper.silicon.reporting
import viper.silicon

import scala.util.{Success, Try}
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, MapEntry, Model, ModelEntry, ValueEntry}
import viper.silver.ast.{AbstractLocalVar, AtomicType, CollectionType, IntLit, LocalVar, Program, Type, utility, Member}
import viper.silver.ast
import viper.silicon.{Map, state => st}
import viper.silicon.interfaces.state.Chunk
import viper.silicon.resources.{FieldID, MagicWandID, PredicateID}
import viper.silicon.state.{BasicChunk, DefaultSymbolConverter, Identifier, SimpleIdentifier, State, Store, SymbolConverter}
import viper.silicon.state.terms._
import viper.silicon.state._
import viper.silicon.decider.TermToSMTLib2Converter
import viper.silicon.interfaces.decider.TermConverter
import viper.silicon.reporting.Converter.{evaluateTerm, getFunctionValue}
import viper.silicon.resources
import viper.silicon.state.terms.sorts.UserSort
import viper.silicon.state.terms.sorts.Snap



case class CounterexampleGenerator(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, program: ast.Program) {
  val imCE = IntermediateCounterexampleModel(model, store, heap, oldHeaps, program)
  //println(model.entries.toString())
  println(imCE.toString)

  val ceStore = CounterexampleGenerator.detStore(store, imCE.basicVariables, imCE.allCollections)
  var ceHeaps = Seq[(String, HeapCounterexample)]()
  imCE.allBasicHeaps.reverse.foreach {case (n, h) => ceHeaps +:= ((n, CounterexampleGenerator.detHeap(h, program, imCE.allCollections)))}

  override def toString: String = {
    var finalString = "      Final Counterexample: \n"
    finalString += "   Store: \n"
    finalString += ceStore.storeEntries.map(x => x.toString).mkString("", "\n", "\n")
    finalString += ceHeaps.map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("")
    finalString += "   Domains: \n"
    finalString
  }
}

case class IntermediateCounterexampleModel(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, program: ast.Program) {
  val basicVariables = IntermediateCounterexampleModel.detBasicVariables(model, store)
  val allSequences = IntermediateCounterexampleModel.detSequences(model)
  val allSets = IntermediateCounterexampleModel.detSets(model)
  val allCollections = allSequences ++ allSets

  var allBasicHeaps = Seq(("return", BasicHeap(IntermediateCounterexampleModel.detHeap(model, heap))))
  oldHeaps.foreach {case (n, h) => allBasicHeaps +:= ((n, BasicHeap(IntermediateCounterexampleModel.detHeap(model, h.values))))}

  override def toString: String = {
    var finalString = "      Intermediate Counterexample: \n"
    finalString ++= "   Local Information: \n"
    if (!basicVariables.isEmpty) finalString += basicVariables.map(x => x.toString).mkString("", "\n", "\n")
    if (!allCollections.isEmpty) finalString += allCollections.map(x => x.toString).mkString("", "\n", "\n")
    finalString += allBasicHeaps.map(x => "   " + x._1 + " Heap: \n" + x._2.toString).mkString("", "\n", "\n")
    finalString ++= "   Domains: \n"
    finalString
  }
}

case class StoreCounterexample(storeEntries: Seq[StoreEntry]) {
  var finalString = ""
  storeEntries.foreach { se => finalString ++= se.toString + "\n"}
  override lazy val toString = finalString
}

case class StoreEntry(id: AbstractLocalVar, entry: CEValue) {
  override lazy val toString = {
    entry match {
      case CEVariable(_, _, _) => s"Variable Name: ${id.name}, Value: ${entry.value.toString}, Type: ${id.typ.toString}"
      case _ => s"  Collection variable ${id.name} of type ${id.typ.toString}: \n ${entry.toString}"
    }
  }
}

case class HeapCounterexample(heapEntries: Seq[(Member, FinalHeapEntry)]) {
  var finalString = ""
  heapEntries.foreach { se => finalString ++= se._2.toString ++ "\n" }
  override lazy val toString = finalString
}

sealed trait FinalHeapEntry

case class FieldFinalEntry(ref: String, field: String, entry: CEValue, perm: Option[Rational], typ: Type) extends FinalHeapEntry {
  override lazy val toString = s"Field Entry: $ref.$field --> (Value: ${entry.value.toString}, Type: ${typ}, Perm: ${perm.getOrElse("#undefined").toString})"
}

case class PredFinalEntry(name: String, args: Seq[String], perm: Option[Rational]) extends FinalHeapEntry {
  override lazy val toString = s"Predicate Entry: $name(${args.mkString("(", ", ", ")")} --> (Perm: ${perm.getOrElse("#undefined").toString})"
}

case class WandFinalEntry(firstPart: String, secondPart: String, args: Seq[String], perm: Option[Rational]) extends FinalHeapEntry {
  override lazy val toString = "to do"
}

sealed trait CEValue {
  val id : String
  val value : Any
  val valueType : Option[ast.Type]
}

case class CEVariable(name: String, entryValue: ModelEntry, typ: Option[Type]) extends CEValue {
  val id = name
  val value = entryValue
  val valueType = typ
  override lazy val toString = s"Variable Name: ${name}, Value: ${value.toString}, Type: ${typ.getOrElse("None").toString}"
}

case class CESequence(name: String, length: BigInt, entries: Map[BigInt, String], sequence: Seq[String], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = sequence
  val valueType = memberTypes
  val size = length
  val inside = entries
  override lazy val toString = {
    var finalString = s"Set $name of size ${size.toString()} with entries:"
    for ((k,v) <- inside)
      finalString ++= s"\n $v at index ${k.toString()}"
    finalString
  }

}

case class CESet(name: String, cardinality: BigInt, containment: Map[String, Boolean], set: Set[String], memberTypes: Option[Type]) extends CEValue {
  val id = name
  val value = set
  val valueType = memberTypes
  val size = cardinality
  val inside = containment
  override lazy val toString = {
    var finalString = s"Set $name of size ${size.toString()} with entries: {"
    for ((k, v) <- inside) {
      if (v) {
        finalString ++= s" $k,"
      }
    }
    finalString ++ "}"
  }
}

case class CEMultiset(name: String, multiset: Set[String], memberTypes: Option[Type]) extends CEValue {
  // TODO: Multisets are not evaluated yet
  val id = name
  val value = multiset
  val valueType = memberTypes
  override lazy val toString = s"Multiset: $name --> $multiset, Type: Multiset($memberTypes)"
}

case class BasicHeap(basicHeapEntries: Set[BasicHeapEntry]) {
  override lazy val toString = basicHeapEntries.map(x => x.toString).mkString("", "\n", "")
}

case class BasicHeapEntry(reference: Seq[String], field: Seq[String], valueID: String, perm: Option[Rational], het: HeapEntryType) {
  override lazy val toString = s"Basic heap entry: ${reference.mkString("(", ", ", ")")} + ${field.mkString("(", ", ", ")")} --> (Value: $valueID, Permission: ${perm.getOrElse("None")})"
}

object IntermediateCounterexampleModel {

  /**
    * Defines the final value or the indentifier of the final value for every variable in the method containing the
    * verification error.
    */
  def detBasicVariables(model: Model, store: Store): Seq[CEVariable] = {
    var res = Seq[CEVariable]()
    for ((k, v) <- store.values) {
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
        }
      }
      if (opName == "Set_singleton") {
        if (opValues.isInstanceOf[MapEntry]) {
          for ((k, v) <- opValues.asInstanceOf[MapEntry].options) {
            res += (v.toString -> Set(k(0).toString))
          }
        }
      }
    }
    var tempMap = Map[(String, Seq[String]), String]()
    for ((opName, opValues) <- model.entries) {
      if (opName == "Set_unionOne") {
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
            res += (v -> x.union(Set(k(1))))
            tempMap -= ((opName, k))
          case None => //
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
        if ((firstSet != None) && (secondSet != None)) {
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
        heap ++= detPredicate(model, c)
      case c@BasicChunk(id, _, _, _, _) =>
        println("This Basic Chunk couldn't be matched as a CE heap entry!")
      case c: st.QuantifiedFieldChunk =>
        println("QF Field Chunk:")
        val fieldName = c.id.name
        val fvf = evaluateTerm(c.snapshotMap, model)
        val possiblePerms = detPermWithInv(c.perm, model)
        model.entries.get(s"$$FVF.lookup_$fieldName") match {
          case Some(x) =>
            //TODO: determine the permission
            for ((k, v) <- x.asInstanceOf[MapEntry].options) {
              if (k(0).toString == fvf.toString) {
                val reference = k(1)
                val value = v.toString
                val tempPerm = possiblePerms.get(Seq(Seq(reference)))
                println(s"Reference: ${reference.toString}")
                println(s"Field Name: $fieldName")
                println(s"Value: $value")
                println(s"Perm: ${c.perm}")
                println(s"New Perm: $tempPerm")
                heap += BasicHeapEntry(Seq(reference.toString), Seq(fieldName), value, None, QPPredicateType)
              }
            }
          case None => println(s"There is not QF with the snapshot: ${c.snapshotMap}")
        }
      case c: st.QuantifiedPredicateChunk =>
        val predName = c.id.name
        val fvf = evaluateTerm(c.snapshotMap, model)
        println(s"Pred Name: $predName")
        println(s"fvf: $fvf")
        val fname = s"$$PSF.lookup_$predName"
        println(s"Perm: ${c.perm}")
        val possiblePerms = detPermWithInv(c.perm, model)
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

  def detPredicate(model: Model, chunk: BasicChunk): Set[BasicHeapEntry] = {
    var retMap = Set[BasicHeapEntry]()
    println("Predicate Chunk:")
    val predSnap = chunk.snap
    println(s"Snap: $predSnap")
    val predName = chunk.id.name
    val references = chunk.args.map(x => evaluateTerm(x, model))
    var insidePredicate = Seq[String]()
    for (sub <- chunk.snap.subterms) {
      if (!sub.toString.startsWith("$t@")) {
        insidePredicate +:= sub.toString
      }
    }
    val perm = evalPerm(chunk.perm, model)
    val sort = chunk.snap.sort
    retMap += BasicHeapEntry(Seq(predName), references.map(x => x.toString), insidePredicate.toString(), perm, PredicateType)
    retMap
  }


  // TODO: when the same combination is not evaluate till the end it is false
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
    var inputsAndPerms = Map[Seq[Seq[ValueEntry]], Option[Rational]]()
    for (combination <- possibleInvCombinations) {
      val (tempOriginals, predicateInputs, tempReplacements) = combination.map { case x => (x._1, x._2, Var(SimpleIdentifier(x._3.asInstanceOf[ConstantEntry].value), x._1.sort)) }.unzip3
//      val tempPerm = newPerm.replace(tempOriginals, tempReplacements)
//      val evaluatedTempPerm = evalPerm(tempPerm, model)
//      inputsAndPerms += (predicateInputs -> evaluatedTempPerm)
//      println(tempPerm.toString)
//      println(s"Inputs ${predicateInputs.toString()} have perm ${evaluatedTempPerm.toString}")
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


  def detMagicWand(model: Model, chunk: BasicChunk): BasicHeapEntry = {
    //TODO
    BasicHeapEntry(Seq("recvVar.toString"), Seq("fieldName"), "value", None, MagicWandType)
  }

  def evalPerm(value: Term, model: Model): Option[Rational] = {
    value match {
      case _: Var => evaluateTerm(value, model) match {
        case LitPermEntry(value) => Some(value)
        case _ => None
      }
      case App(applicable, argsSeq) => None
      // case PermLiteral(x) => Some(x)
      case IntLiteral(n) => Some(Rational.apply(n, 1))
      case NoPerm => Some(Rational.zero)
      case FullPerm => Some(Rational.one)
      case Null => None
      case a:BooleanLiteral => if (a.value) Some(Rational.apply(1, 1)) else Some(Rational.apply(0, 1))
      case _: Quantification => None //TODO
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
      case Mod(v1, v2) => None //TODO
      case Not(v) =>
        val pr = evalPerm(v, model)
        if (pr != None) {
          Some(Rational.apply(1-pr.get.numerator, pr.get.denominator)
        } else {
          None
        }
      case Or(valueSeq) => //TODO: doesn't work yet
        def detPermGreaterZero(perm: Option[Rational]): Option[Rational] = {
          if (perm != None) {
            if (perm.get.numerator > 0) {
              Some(Rational.one)
            } else {
              Some(Rational.zero)
            }
          } else {
            None
          }
        }
        valueSeq.foldLeft[](detPermGreaterZero(evalPerm(valueSeq.head, model)), valueSeq.tail.map(x => detPermGreaterZero(evalPerm(x, model))))
      case FractionPermLiteral(r) => Some(r)
      case FractionPerm(v1, v2) => if (v1.isInstanceOf[IntLiteral] && v2.isInstanceOf[IntLiteral]) Some(Rational(v1.asInstanceOf[IntLiteral].n, v2.asInstanceOf[IntLiteral].n)) else None
      case IsValidPermVar(v) => evalPerm(v, model)
      case IsReadPermVar(v) => evalPerm(v, model)
      case Let(_) => None
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

//  def evaluateTerm(term: Term, model: Model): BasicEntryCounterexample = {
//    term match {
//      case Unit => BasicVariableCounterexample("Unit", snapUnitId, "#undefined", "Unit", false)
//      case IntLiteral(x) => BasicVariableCounterexample(x.toString(), x.toString(), x.toString(), "Int", true)
//      case t: BooleanLiteral => BasicVariableCounterexample(t.toString, t.toString, t.toString, "Bool", true)
//      case Null => BasicVariableCounterexample("Null", model.entries(nullRefId).toString, "#undefined", "Ref", true)
//      case Var(_, sort) =>
//        // TODO:
//        val entry: Option[ModelEntry] = model.entries.get(term.toString)
//        entry.map(x => getConstantEntry(sort, x)).getOrElse(OtherEntry(term.toString, "variable not found in model"))
//      case App(app, args) =>
//        // TODO: replace these String literals generated by other parts of silicon
//        // once they are directly available (e.g. from TermToSMTLib2Converter)
//        // also in several other places
//        var fname = s"${app.id}%limited"
//        if (!model.entries.contains(fname)) {
//          fname = app.id.toString
//          if (!model.entries.contains(fname)) {
//            fname = fname.replace("[", "<").replace("]", ">")
//          }
//        }
//        val toSort = app.resultSort
//        val argEntries: Seq[BasicVariableCounterexample] = args.map(t => evaluateTerm(t, model))
//        val argsFinal = argEntries.map {
//          case BasicVariableCounterexample(_, entry, _, _, false) => ConstantEntry(entry)
//          case BasicVariableCounterexample(_, entry, _, _, true) => ConstantEntry(entry)
//        }
//        getFunctionValue(model, fname, argsFinal, toSort)
//
//      case Combine(p0, p1) =>
//        val p0Eval = evaluateTerm(p0, model)
//        val p0VE = ConstantEntry(p0Eval.toString)
//        val p1Eval = evaluateTerm(p1, model)
//        val p1VE = ConstantEntry(p1Eval.toString)
//        val entry = ApplicationEntry("$Snap.combine", Seq(p0VE, p1VE))
//          BasicVariableCounterexample("$Snap.combine", entry.toString, Seq(p0VE, p1VE).toString(), "$Snap.combine", true)
//
//      case First(p) =>
//        val sub = evaluateTerm(p, model)
//        sub match {
//          case BasicVariableCounterexample(_, internalName, args, "ApplicationEntry", false) =>
//            if (internalName == "$Snap.combine") {
//              BasicVariableCounterexample("#undefined", "$Snap.combine", args(0), "ApplicationEntry", false)
//            } else {
//              BasicVariableCounterexample(s"First($p)", "unapplicable", Seq("#undefined"), "OtherEntry", true)
//            }
//          case BasicVariableCounterexample(name, _, _, "OtherEntry", true) =>
//            BasicVariableCounterexample(s"First($name)", "unapplicable", Seq("#undefined"), "OtherEntry", true)
//          case _ => BasicVariableCounterexample(s"First($sub)", "unapplicable", Seq("#undefined"), "OtherEntry", true)
//        }
//      case Second(p) =>
//        val sub = evaluateTerm(p, model)
//        sub match {
//          case BasicVariableCounterexample(_, internalName, args, "ApplicationEntry", false) =>
//            if (internalName == "$Snap.combine") {
//              BasicVariableCounterexample("#undefined", "$Snap.combine", args(1), "ApplicationEntry", false)
//            } else {
//              BasicVariableCounterexample(s"Second($p)", "unapplicable", Seq("#undefined"), "OtherEntry", true)
//            }
//          case BasicVariableCounterexample(name, _, m, "OtherEntry", true) =>
//            BasicVariableCounterexample(s"Second($name)$m", "unapplicable", Seq("#undefined"), "OtherEntry", true)
//          case _ => BasicVariableCounterexample(s"Second($sub)", "unapplicable", Seq("#undefined"), "OtherEntry", true)
//        }
//      case SortWrapper(t, to) =>
//        val sub = evaluateTerm(t, model)
//        val fromSortName: String = termconverter.convert(t.sort)
//        val toSortName: String = termconverter.convert(to)
//        val fname = s"$$SortWrappers.${fromSortName}To$toSortName"
//        sub match {
//          case UnprocessedModelEntry(entry) =>
//            getFunctionValue(model, fname, Seq(entry), to)
//          case OtherEntry(t, _) =>
//            OtherEntry(s"SortWrapper($t)", "unapplicable")
//          case _ => OtherEntry(s"SortWrapper($t)", "unapplicable")
//        }
//
//      case PredicateLookup(predname, psf, args) =>
//        val lookupFuncName: String = s"$$PSF.lookup_$predname"
//        val snap = toSnapTree.apply(args)
//        val snapVal = evaluateTerm(snap, model).asValueEntry
//        val psfVal = evaluateTerm(psf, model).asValueEntry
//        val arg = Seq(psfVal, snapVal)
//        getFunctionValue(model, lookupFuncName, arg, sorts.Snap)
//      case _ => OtherEntry(term.toString, "unhandled")
//    }
//  }
}

object CounterexampleGenerator {
  def detStore(store: Store, variables: Seq[CEVariable], collections: Set[CEValue]): StoreCounterexample = {
    var ans = Seq[StoreEntry]()
    for ((k,v) <- store.values) {
      for (vari <- variables) {
        if (k.name == vari.name) {
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
    StoreCounterexample(ans)
  }

  def detHeap(basicHeap: BasicHeap, program: Program, collections: Set[CEValue]): HeapCounterexample = {
    var ans = Seq[(Member, FinalHeapEntry)]()
    for (bhe <- basicHeap.basicHeapEntries) {
      bhe.het match {
        case FieldType | QPPredicateType =>
          for ((fn, fv) <- program.fieldsByName) {
            if (fn == bhe.field(0)) {
              var found = false
              for (coll <- collections) {
                if (bhe.valueID == coll.id) {
                  ans +:= (fv, FieldFinalEntry(bhe.reference(0), bhe.field(0), coll, bhe.perm, fv.typ))
                  found = true
                }
              }
              if (!found) {
                ans +:= (fv, FieldFinalEntry(bhe.reference(0), bhe.field(0), CEVariable("#undefined", ConstantEntry(bhe.valueID), Some(fv.typ)), bhe.perm, fv.typ))
              }
            }
          }
        case PredicateType | QPPredicateType =>
          for ((pn, pv) <- program.predicatesByName) {
            if (pn == bhe.reference(0)) {
              ans +:= (pv, PredFinalEntry(bhe.reference(0), bhe.field, bhe.perm))
            }
          }
      }
    }
    HeapCounterexample(ans)
  }
}

sealed trait HeapEntryType
case object FieldType extends HeapEntryType
case object PredicateType extends HeapEntryType
case object QPFieldType extends HeapEntryType
case object QPPredicateType extends HeapEntryType
case object MagicWandType extends HeapEntryType
case object QPMagicWandType extends HeapEntryType