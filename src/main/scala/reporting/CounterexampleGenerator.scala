package viper.silicon.reporting
import viper.silicon

import scala.util.{Success, Try}
import viper.silver.verifier.{ApplicationEntry, ConstantEntry, MapEntry, Model, ModelEntry, ValueEntry}
import viper.silver.ast.{AbstractLocalVar, AtomicType, CollectionType, LocalVar, Type, utility}
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

case class IntermediateCounterexampleModel(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, program: ast.Program) {
  lazy val basicVariables = IntermediateCounterexampleModel.detBasicVariables(model, store)
  lazy val allSequences = IntermediateCounterexampleModel.detSequences(model)
  lazy val allSets = IntermediateCounterexampleModel.detSets(model)
  lazy val allCollections = allSequences ++ allSets
  lazy val basicHeap = IntermediateCounterexampleModel.detHeap(model, heap)
}

case class BasicCEVariable(variable: AbstractLocalVar, value: ModelEntry, typ: Option[Type]) {
  override lazy val toString = s"Variable Name: ${variable.toString()}, Value: ${value.toString}, Type: ${typ.toString()}"
}

case class allCollectionEntries(entries: Set[BasicCollectionCEEntry])

sealed trait BasicCollectionCEEntry

case class BasicCESequence(variable: String, sequence: Seq[String], memberTypes: Option[Type]) extends BasicCollectionCEEntry {
  override lazy val toString = s"Sequence: $variable --> $sequence, Type: Seq($memberTypes)"
}

case class BasicCESet(variable: String, set: Set[String], memberTypes: Option[Type]) extends BasicCollectionCEEntry {
  override lazy val toString = s"Set: $variable --> $set, Type: Set($memberTypes)"
}

case class BasicCEMultiset(variable: String, set: Set[String], memberTypes: Option[Type]) extends BasicCollectionCEEntry {
  override lazy val toString = s"Multiset: $variable --> $set, Type: Multiset($memberTypes)"
}

//case class BasicCounterexampleHeap(heapEntries: Set[BasicHeapEntry]) {
//  override lazy val toString = {
//    var out = s"Heap: \n"
//    for (k <- heapEntries) {
//      if (k.isInstanceOf[BasicFieldCounterexample]) {
//        out += s"Field -> ${k.asInstanceOf[BasicFieldCounterexample].toString}\n"
//      } else if (k.isInstanceOf[BasicPredicateCounterexample]) {
//        out += s"Predicate -> ${k.asInstanceOf[BasicPredicateCounterexample].toString}\n"
//      }
//    }
//    out
//  }
//}

sealed trait BasicHeapEntry

case class BasicFieldCounterexample(reference: String, field: String, value: String, permission: Option[Rational], valueType: String) extends BasicHeapEntry {
  override lazy val toString = s"Ref: $reference, Field: $field, Value: $value, perm: $permission, Type: $valueType"
}

case class BasicPredicateCounterexample(name: String, references: Seq[ExtractedModelEntry], values: Seq[String], permission: Option[Rational], valueType: String) extends BasicHeapEntry {
  override lazy val toString = s"Name: $name, References: ${references.map(x => x.toString)}, Values: $values, Perm: $permission, Type: $valueType"
}

object IntermediateCounterexampleModel {

  def detBasicVariables(model: Model, store: Store): Seq[BasicCEVariable] = {
    var res = Seq[BasicCEVariable]()
    for ((k, v) <- store.values) {
      model.entries.get(v.toString) match {
        case Some(x) =>
          var varTyp: Option[Type] = None
          if (k.isInstanceOf[LocalVar]) {
            varTyp = Some(x.asInstanceOf[LocalVar].typ)
          }
          if (x.isInstanceOf[ConstantEntry]) {
            res +:= BasicCEVariable(k, x, varTyp)
          } else if (x.isInstanceOf[ApplicationEntry]) {
            res +:= BasicCEVariable(k, x, varTyp)
          } else {
            println(s"Couldn't find a ConstantEntry or ApplicationEntry for the Variable: ${k.name}")
          }
        case None => println(s"Couldn't find an entry for the Variable: ${k.name}")
      }
    }
    res
  }

  // a CE generator for sequences
  def detSequences(model: Model): Set[BasicCESequence] = {
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
              res += (v -> (x ++ y))
              tempMap -= ((opName, k))
              found = true
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
        } else if (opName == "Seq_upadte") {
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
    var ans = Set[BasicCESequence]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SeqType(x))
          case None => None
        }
        ans += BasicCESequence(n, s, typ)
    }
    ans
  }

  def detSets(model: Model): Set[BasicCESet] = {
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
    var ans = Set[BasicCESet]()
    res.foreach {
      case (n, s) =>
        val typ: Option[Type] = detASTTypeFromString(n.replaceAll(".*?<(.*)>.*", "$1")) match {
          case Some(x) => Some(ast.SetType(x))
          case None => None
        }
        ans += BasicCESet(n, s, typ)
    }
    ans
  }

  def detASTTypeFromString(typ: String): Option[Type] = {
    typ match {
      case "Int" => Some(ast.Int)
      case "Bool" => Some(ast.Bool)
      case "Perm" => Some(ast.Perm)
      case "Ref" => Some(ast.Ref)
      case _ => None
    }
  }

  def detHeap(model: Model, h: Iterable[Chunk]): BasicCounterexampleHeap = {
    var heap = Set[BasicHeapEntry]()
    h foreach {
      case c@BasicChunk(FieldID, _, _, _, _) =>
        heap += detField(model, c)
      case c@BasicChunk(PredicateID, _, _, _, _) =>
        heap ++= detPredicate(model, c)
      case c@BasicChunk(id, _, _, _, _) =>
        println("This Basic Chunk is weird!")
      case c: st.QuantifiedFieldChunk =>
        println("QF Field Chunk:")
        val fieldName = c.id.name
        val fvf = evaluateTerm(c.snapshotMap, model)
        val possiblePerms = detPermWithInv(c.perm, model)
        model.entries.get(s"$$FVF.lookup_$fieldName") match {
          case Some(x) =>
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
                heap += BasicFieldCounterexample(reference.toString, fieldName, value, None, "typ.toString")
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
    BasicCounterexampleHeap(heap)
  }

  def detField(model: Model, chunk: BasicChunk): BasicFieldCounterexample = {
    println("Field Chunk:")
    println(chunk.toString)
    println(chunk.args.toString())
    val recvVar = evaluateTerm(chunk.args(0), model)
    val fieldName = chunk.id.name
    val value = evaluateTerm(chunk.snap, model).toString
    val perm = evalPerm(chunk.perm, model)
    val typ = chunk.snap.sort
    BasicFieldCounterexample(recvVar.toString, fieldName, value, perm, typ.toString)
  }

  def detPredicate(model: Model, chunk: BasicChunk): Set[BasicPredicateCounterexample] = {
    var retMap = Set[BasicPredicateCounterexample]()
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
    retMap += BasicPredicateCounterexample(predName, references, insidePredicate, perm, sort.toString)
    retMap
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
    var inputsAndPerms = Map[Seq[Seq[ValueEntry]], Option[Rational]]()
    for (combination <- possibleInvCombinations) {
      val (tempOriginals, predicateInputs, tempReplacements) = combination.map { x => (x._1, x._2, Var(SimpleIdentifier(x._3.asInstanceOf[ConstantEntry].value), x._1.sort)) }.unzip3
      val tempPerm = newPerm.replace(tempOriginals, tempReplacements)
      val evaluatedTempPerm = evalPerm(tempPerm, model)
      inputsAndPerms += (predicateInputs -> evaluatedTempPerm)
      println(tempPerm.toString)
      println(s"Inputs ${predicateInputs.toString()} have perm ${evaluatedTempPerm.toString}")
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


  def detMagicWand(model: Model, chunk: BasicChunk): BasicFieldCounterexample = {
    BasicFieldCounterexample("recvVar.toString", "fieldName", "value", None, "typ.toString")
  }

  def evalPerm(value: Term, model: Model): Option[Rational] = {
    value match {
      case _: Var => evaluateTerm(value, model) match {
        case LitPermEntry(value) => Some(value)
        case _ => None
      }
      case App(_, _) => None
      case NoPerm => Some(Rational.zero)
      case FullPerm => Some(Rational.one)
      case FractionPermLiteral(r) => Some(r)
      case _: FractionPerm => None
      case IsValidPermVar(_) => None
      case IsReadPermVar(_) => None
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

case class CounterexampleGenerator(model: Model, store: Store, heap: Iterable[Chunk], oldHeaps: State.OldHeaps, program: ast.Program) {
  println("Currently in the CounterexampleGenerator class")
}

object CounterexampleGenerator {

}