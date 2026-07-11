import integration.FoundationCompactNumericSyntaxValueParser
import integration.FoundationCompactParserDirectTrace
import Mathlib.Computability.Primrec.List

/-!
# Local traces for compact sequent-value repetition

The sequent value parser reads a leading formula count and iterates the real
`compactFormulaTokenValuesStep`.  This module exposes that bounded iteration as
an initial/step/final tableau.  The formula parser called inside one step is the
next trace boundary.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactSequentValueDirectTrace

open FoundationCompactNumericSyntaxValueParser
open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachine

def compactFormulaValuesStateAt
    (start : CompactFormulaTokenValuesResult) (stepIndex : Nat) :
    CompactFormulaTokenValuesResult :=
  (compactFormulaTokenValuesStep^[stepIndex]) start

theorem compactFormulaValuesStateAt_primrec :
    Primrec₂ compactFormulaValuesStateAt := by
  apply Primrec₂.mk
  have hstep : Primrec₂
      (fun (_input : CompactFormulaTokenValuesResult × Nat)
          (state : CompactFormulaTokenValuesResult) =>
        compactFormulaTokenValuesStep state) :=
    compactFormulaTokenValuesStep_primrec.comp Primrec₂.right
  exact
    (Primrec.nat_iterate Primrec.snd Primrec.fst hstep).of_eq
      fun input => by rfl

def compactFormulaValuesStateTrace
    (count : Nat) (start : CompactFormulaTokenValuesResult) :
    List CompactFormulaTokenValuesResult :=
  (List.range (count + 1)).map fun stepIndex =>
    compactFormulaValuesStateAt start stepIndex

theorem compactFormulaValuesStateTrace_primrec :
    Primrec₂ compactFormulaValuesStateTrace := by
  apply Primrec₂.mk
  let Input := Nat × CompactFormulaTokenValuesResult
  have hindices : Primrec (fun input : Input =>
      List.range (input.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have hstate : Primrec₂
      (fun (input : Input) (stepIndex : Nat) =>
        compactFormulaValuesStateAt input.2 stepIndex) :=
    compactFormulaValuesStateAt_primrec.comp₂
      (Primrec.snd.comp Primrec₂.left) Primrec₂.right
  exact
    (Primrec.list_map hindices hstate).of_eq fun input => by rfl

def compactFormulaValuesTraceState?
    (states : List CompactFormulaTokenValuesResult) (stepIndex : Nat) :
    Option CompactFormulaTokenValuesResult :=
  states[stepIndex]?

theorem compactFormulaValuesTraceState?_primrec :
    Primrec₂ compactFormulaValuesTraceState? :=
  Primrec.list_getElem?

def compactFormulaValuesStepOption
    (state : Option CompactFormulaTokenValuesResult) :
    Option CompactFormulaTokenValuesResult :=
  state.map compactFormulaTokenValuesStep

theorem compactFormulaValuesStepOption_primrec :
    Primrec compactFormulaValuesStepOption := by
  refine (Primrec.option_map Primrec.id ?_).of_eq fun state => by rfl
  apply Primrec₂.mk
  exact compactFormulaTokenValuesStep_primrec.comp Primrec.snd

@[simp] theorem compactFormulaValuesStateTrace_length
    (count : Nat) (start : CompactFormulaTokenValuesResult) :
    (compactFormulaValuesStateTrace count start).length = count + 1 := by
  simp [compactFormulaValuesStateTrace]

theorem compactFormulaValuesStateTrace_getElem?
    (count stepIndex : Nat) (start : CompactFormulaTokenValuesResult)
    (hstepIndex : stepIndex <= count) :
    compactFormulaValuesTraceState?
        (compactFormulaValuesStateTrace count start) stepIndex =
      some (compactFormulaValuesStateAt start stepIndex) := by
  simp [compactFormulaValuesTraceState?, compactFormulaValuesStateTrace,
    hstepIndex]

theorem compactFormulaValuesStateTrace_final
    (count : Nat) (start : CompactFormulaTokenValuesResult) :
    compactFormulaValuesTraceState?
        (compactFormulaValuesStateTrace count start) count =
      some ((compactFormulaTokenValuesStep^[count]) start) := by
  simpa [compactFormulaValuesStateAt] using
    compactFormulaValuesStateTrace_getElem? count count start (by rfl)

def CompactFormulaValuesCanonicalTraceValid
    (count : Nat) (start : CompactFormulaTokenValuesResult)
    (states : List CompactFormulaTokenValuesResult) : Prop :=
  states = compactFormulaValuesStateTrace count start

theorem compactFormulaValuesCanonicalTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × CompactFormulaTokenValuesResult) ×
          List CompactFormulaTokenValuesResult =>
      CompactFormulaValuesCanonicalTraceValid
        input.1.1 input.1.2 input.2) := by
  have hcanonical : Primrec (fun input :
      (Nat × CompactFormulaTokenValuesResult) ×
        List CompactFormulaTokenValuesResult =>
      compactFormulaValuesStateTrace input.1.1 input.1.2) :=
    compactFormulaValuesStateTrace_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  exact
    (Primrec.eq.comp Primrec.snd hcanonical).of_eq fun input => by
      simp [CompactFormulaValuesCanonicalTraceValid]

def CompactFormulaValuesLocalTraceValid
    (count : Nat) (start : CompactFormulaTokenValuesResult)
    (states : List CompactFormulaTokenValuesResult) : Prop :=
  states.length = count + 1 ∧
    compactFormulaValuesTraceState? states 0 = some start ∧
    ∀ stepIndex < count,
      compactFormulaValuesTraceState? states (stepIndex + 1) =
        compactFormulaValuesStepOption
          (compactFormulaValuesTraceState? states stepIndex)

@[simp] theorem compactFormulaValuesStateTrace_localValid
    (count : Nat) (start : CompactFormulaTokenValuesResult) :
    CompactFormulaValuesLocalTraceValid count start
      (compactFormulaValuesStateTrace count start) := by
  refine ⟨compactFormulaValuesStateTrace_length count start, ?_, ?_⟩
  · simpa [compactFormulaValuesStateAt] using
      compactFormulaValuesStateTrace_getElem?
        count 0 start (Nat.zero_le count)
  · intro stepIndex hstepIndex
    rw [compactFormulaValuesStateTrace_getElem? count (stepIndex + 1)
      start (by omega)]
    rw [compactFormulaValuesStateTrace_getElem? count stepIndex
      start (Nat.le_of_lt hstepIndex)]
    simp [compactFormulaValuesStateAt, compactFormulaValuesStepOption,
      Function.iterate_succ_apply']

theorem compactFormulaValuesLocalTraceValid_stateAt
    {count : Nat} {start : CompactFormulaTokenValuesResult}
    {states : List CompactFormulaTokenValuesResult}
    (hvalid : CompactFormulaValuesLocalTraceValid count start states)
    {stepIndex : Nat} (hstepIndex : stepIndex <= count) :
    compactFormulaValuesTraceState? states stepIndex =
      some (compactFormulaValuesStateAt start stepIndex) := by
  induction stepIndex with
  | zero =>
      simpa [compactFormulaValuesStateAt] using hvalid.2.1
  | succ stepIndex ih =>
      have hlt : stepIndex < count := by omega
      have hprevious := ih (by omega)
      rw [show stepIndex + 1 = stepIndex.succ by omega,
        hvalid.2.2 stepIndex hlt, hprevious]
      simp [compactFormulaValuesStateAt,
        compactFormulaValuesStepOption,
        Function.iterate_succ_apply']

theorem compactFormulaValuesLocalTraceValid_eq_canonical
    {count : Nat} {start : CompactFormulaTokenValuesResult}
    {states : List CompactFormulaTokenValuesResult}
    (hvalid : CompactFormulaValuesLocalTraceValid count start states) :
    states = compactFormulaValuesStateTrace count start := by
  apply List.ext_getElem?
  intro stepIndex
  by_cases hstepIndex : stepIndex <= count
  · change
      compactFormulaValuesTraceState? states stepIndex =
        compactFormulaValuesTraceState?
          (compactFormulaValuesStateTrace count start) stepIndex
    rw [compactFormulaValuesLocalTraceValid_stateAt hvalid hstepIndex]
    rw [compactFormulaValuesStateTrace_getElem?
      count stepIndex start hstepIndex]
  · have hstatesLength : states.length = count + 1 := hvalid.1
    have hcanonicalLength :=
      compactFormulaValuesStateTrace_length count start
    have houtside : count + 1 <= stepIndex := by omega
    rw [List.getElem?_eq_none (by omega : states.length <= stepIndex)]
    rw [List.getElem?_eq_none (by omega :
      (compactFormulaValuesStateTrace count start).length <= stepIndex)]

theorem compactFormulaValuesLocalTraceValid_iff_canonical
    (count : Nat) (start : CompactFormulaTokenValuesResult)
    (states : List CompactFormulaTokenValuesResult) :
    CompactFormulaValuesLocalTraceValid count start states ↔
      CompactFormulaValuesCanonicalTraceValid count start states := by
  constructor
  · exact compactFormulaValuesLocalTraceValid_eq_canonical
  · intro hvalid
    rw [hvalid]
    exact compactFormulaValuesStateTrace_localValid count start

theorem compactFormulaValuesLocalTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × CompactFormulaTokenValuesResult) ×
          List CompactFormulaTokenValuesResult =>
      CompactFormulaValuesLocalTraceValid
        input.1.1 input.1.2 input.2) := by
  exact compactFormulaValuesCanonicalTraceValid_primrec.of_eq fun input =>
    (compactFormulaValuesLocalTraceValid_iff_canonical
      input.1.1 input.1.2 input.2).symm

abbrev CompactFormulaValuesRepeatDirectTrace :=
  List CompactFormulaTokenValuesResult

def CompactFormulaValuesRepeatDirectTraceValid
    (count : Nat) (tokens : List Nat)
    (values : List (List Nat)) (suffix : List Nat)
    (states : CompactFormulaValuesRepeatDirectTrace) : Prop :=
  CompactFormulaValuesLocalTraceValid count
      (compactFormulaTokenValuesInitial tokens) states ∧
    compactFormulaValuesTraceState? states count =
      some (some (values, suffix))

theorem compactFormulaValuesRepeatDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × List Nat) ×
          ((List (List Nat) × List Nat) ×
            CompactFormulaValuesRepeatDirectTrace) =>
      CompactFormulaValuesRepeatDirectTraceValid
        input.1.1 input.1.2 input.2.1.1 input.2.1.2 input.2.2) := by
  let Input :=
    (Nat × List Nat) ×
      ((List (List Nat) × List Nat) ×
        CompactFormulaValuesRepeatDirectTrace)
  have hcount : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have htokens : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hvalues : Primrec (fun input : Input => input.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hsuffix : Primrec (fun input : Input => input.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hstates : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hstart : Primrec (fun input : Input =>
      compactFormulaTokenValuesInitial input.1.2) :=
    compactFormulaTokenValuesInitial_primrec.comp htokens
  have hlocal : PrimrecPred (fun input : Input =>
      CompactFormulaValuesLocalTraceValid input.1.1
        (compactFormulaTokenValuesInitial input.1.2) input.2.2) :=
    compactFormulaValuesLocalTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hcount hstart) hstates
  have hfinalState : Primrec (fun input : Input =>
      compactFormulaValuesTraceState? input.2.2 input.1.1) :=
    compactFormulaValuesTraceState?_primrec.comp hstates hcount
  have hexpected : Primrec (fun input : Input =>
      some (some (input.2.1.1, input.2.1.2))) :=
    Primrec.option_some.comp
      (Primrec.option_some.comp (Primrec.pair hvalues hsuffix))
  have hfinal : PrimrecPred (fun input : Input =>
      compactFormulaValuesTraceState? input.2.2 input.1.1 =
        some (some (input.2.1.1, input.2.1.2))) :=
    Primrec.eq.comp hfinalState hexpected
  exact
    (hlocal.and hfinal).of_eq fun input => by
      simp only [CompactFormulaValuesRepeatDirectTraceValid]

theorem compactFormulaTokenValuesRepeat_eq_some_iff_exists_directTrace
    (count : Nat) (tokens : List Nat)
    (values : List (List Nat)) (suffix : List Nat) :
    compactFormulaTokenValuesRepeat count tokens = some (values, suffix) ↔
      ∃ states : CompactFormulaValuesRepeatDirectTrace,
        CompactFormulaValuesRepeatDirectTraceValid
          count tokens values suffix states := by
  constructor
  · intro hrun
    let start := compactFormulaTokenValuesInitial tokens
    let states := compactFormulaValuesStateTrace count start
    refine ⟨states,
      compactFormulaValuesStateTrace_localValid count start, ?_⟩
    rw [compactFormulaValuesStateTrace_final]
    simpa [compactFormulaTokenValuesRepeat, start] using hrun
  · rintro ⟨states, hlocal, hfinal⟩
    have hstates := compactFormulaValuesLocalTraceValid_eq_canonical hlocal
    rw [hstates, compactFormulaValuesStateTrace_final] at hfinal
    simpa [compactFormulaTokenValuesRepeat] using hfinal

theorem compactFormulaTokenValueParser_eq_some_iff
    (binderArity : Nat) (tokens value suffix : List Nat) :
    compactFormulaTokenValueParser binderArity tokens =
        some (value, suffix) ↔
      compactFormulaTokenParser binderArity tokens = some suffix ∧
        value = consumedTokenPrefix tokens suffix := by
  cases hparser : compactFormulaTokenParser binderArity tokens with
  | none =>
      simp [compactFormulaTokenValueParser, hparser]
  | some parsedSuffix =>
      simp only [compactFormulaTokenValueParser, hparser, Option.map_some,
        Option.some.injEq, Prod.mk.injEq]
      constructor
      · rintro ⟨hvalue, rfl⟩
        exact ⟨rfl, hvalue.symm⟩
      · rintro ⟨rfl, hvalue⟩
        exact ⟨hvalue.symm, rfl⟩

def CompactFormulaValuesConcreteNestedTransitionValid
    (current next : List (List Nat) × List Nat)
    (parserTrace : CompactFormulaTokenParserDirectTrace) : Prop :=
  CompactFormulaTokenParserDirectTraceValid
      0 current.2 next.2 parserTrace ∧
    next.1 = current.1 ++ [consumedTokenPrefix current.2 next.2]

theorem compactFormulaValuesConcreteNestedTransitionValid_primrec :
    PrimrecPred (fun input :
        ((List (List Nat) × List Nat) ×
          (List (List Nat) × List Nat)) ×
            CompactFormulaTokenParserDirectTrace =>
      CompactFormulaValuesConcreteNestedTransitionValid
        input.1.1 input.1.2 input.2) := by
  let Parsed := List (List Nat) × List Nat
  let Input := (Parsed × Parsed) × CompactFormulaTokenParserDirectTrace
  have hcurrent : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hnext : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hparserTrace : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hcurrentValues : Primrec (fun input : Input => input.1.1.1) :=
    Primrec.fst.comp hcurrent
  have hcurrentTokens : Primrec (fun input : Input => input.1.1.2) :=
    Primrec.snd.comp hcurrent
  have hnextValues : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp hnext
  have hnextTokens : Primrec (fun input : Input => input.1.2.2) :=
    Primrec.snd.comp hnext
  have hparser : PrimrecPred (fun input : Input =>
      CompactFormulaTokenParserDirectTraceValid
        0 input.1.1.2 input.1.2.2 input.2) :=
    compactFormulaTokenParserDirectTraceValid_primrec.comp <|
      Primrec.pair
        (Primrec.pair
          (Primrec.pair (Primrec.const 0) hcurrentTokens)
          hnextTokens)
        hparserTrace
  have hconsumed : Primrec (fun input : Input =>
      consumedTokenPrefix input.1.1.2 input.1.2.2) :=
    consumedTokenPrefix_primrec.comp hcurrentTokens hnextTokens
  have happended : Primrec (fun input : Input =>
      input.1.1.1 ++ [consumedTokenPrefix input.1.1.2 input.1.2.2]) :=
    Primrec.list_concat.comp hcurrentValues hconsumed
  have hvalues : PrimrecPred (fun input : Input =>
      input.1.2.1 =
        input.1.1.1 ++
          [consumedTokenPrefix input.1.1.2 input.1.2.2]) :=
    Primrec.eq.comp hnextValues happended
  exact
    (hparser.and hvalues).of_eq fun input => by
      simp only [CompactFormulaValuesConcreteNestedTransitionValid]

abbrev CompactFormulaValuesParserTraceList :=
  List CompactFormulaTokenParserDirectTrace

def compactFormulaValuesParserTrace?
    (parserTraces : CompactFormulaValuesParserTraceList)
    (stepIndex : Nat) : Option CompactFormulaTokenParserDirectTrace :=
  parserTraces[stepIndex]?

theorem compactFormulaValuesParserTrace?_primrec :
    Primrec₂ compactFormulaValuesParserTrace? :=
  Primrec.list_getElem?

def CompactFormulaValuesNestedTransitionAt
    (stepIndex : Nat)
    (traceData : CompactFormulaValuesRepeatDirectTrace ×
      CompactFormulaValuesParserTraceList) : Prop :=
  let currentState :=
    (compactFormulaValuesTraceState? traceData.1 stepIndex).getD none
  let nextState :=
    (compactFormulaValuesTraceState?
      traceData.1 (stepIndex + 1)).getD none
  let parserTrace? :=
    compactFormulaValuesParserTrace? traceData.2 stepIndex
  currentState ≠ none ∧
    nextState ≠ none ∧
    parserTrace? ≠ none ∧
    CompactFormulaValuesConcreteNestedTransitionValid
      (currentState.getD (([] : List (List Nat)), ([] : List Nat)))
      (nextState.getD (([] : List (List Nat)), ([] : List Nat)))
      (parserTrace?.getD [])

theorem compactFormulaValuesNestedTransitionAt_primrec :
    PrimrecRel CompactFormulaValuesNestedTransitionAt := by
  let Parsed := List (List Nat) × List Nat
  let TraceData := CompactFormulaValuesRepeatDirectTrace ×
    CompactFormulaValuesParserTraceList
  let Input := Nat × TraceData
  have hindex : Primrec (fun input : Input => input.1) :=
    Primrec.fst
  have hstates : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hparserTraces : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcurrentOption : Primrec (fun input : Input =>
      compactFormulaValuesTraceState? input.2.1 input.1) :=
    compactFormulaValuesTraceState?_primrec.comp hstates hindex
  have hnextIndex : Primrec (fun input : Input => input.1 + 1) :=
    Primrec.succ.comp hindex
  have hnextOption : Primrec (fun input : Input =>
      compactFormulaValuesTraceState? input.2.1 (input.1 + 1)) :=
    compactFormulaValuesTraceState?_primrec.comp hstates hnextIndex
  have htraceOption : Primrec (fun input : Input =>
      compactFormulaValuesParserTrace? input.2.2 input.1) :=
    compactFormulaValuesParserTrace?_primrec.comp hparserTraces hindex
  have hcurrentState : Primrec (fun input : Input =>
      (compactFormulaValuesTraceState? input.2.1 input.1).getD none) :=
    Primrec.option_getD.comp hcurrentOption (Primrec.const none)
  have hnextState : Primrec (fun input : Input =>
      (compactFormulaValuesTraceState?
        input.2.1 (input.1 + 1)).getD none) :=
    Primrec.option_getD.comp hnextOption (Primrec.const none)
  have hcurrentPresent : PrimrecPred (fun input : Input =>
      (compactFormulaValuesTraceState?
        input.2.1 input.1).getD none ≠ none) :=
    (Primrec.eq.comp hcurrentState (Primrec.const none)).not
  have hnextPresent : PrimrecPred (fun input : Input =>
      (compactFormulaValuesTraceState?
        input.2.1 (input.1 + 1)).getD none ≠ none) :=
    (Primrec.eq.comp hnextState (Primrec.const none)).not
  have htracePresent : PrimrecPred (fun input : Input =>
      compactFormulaValuesParserTrace? input.2.2 input.1 ≠ none) :=
    (Primrec.eq.comp htraceOption (Primrec.const none)).not
  have hcurrent : Primrec (fun input : Input =>
      ((compactFormulaValuesTraceState?
        input.2.1 input.1).getD none).getD
          (([] : List (List Nat)), ([] : List Nat))) :=
    Primrec.option_getD.comp hcurrentState
      (Primrec.const (([] : List (List Nat)), ([] : List Nat)))
  have hnext : Primrec (fun input : Input =>
      ((compactFormulaValuesTraceState?
        input.2.1 (input.1 + 1)).getD none).getD
          (([] : List (List Nat)), ([] : List Nat))) :=
    Primrec.option_getD.comp hnextState
      (Primrec.const (([] : List (List Nat)), ([] : List Nat)))
  have hparserTrace : Primrec (fun input : Input =>
      (compactFormulaValuesParserTrace?
        input.2.2 input.1).getD []) :=
    Primrec.option_getD.comp htraceOption (Primrec.const [])
  have hconcrete : PrimrecPred (fun input : Input =>
      CompactFormulaValuesConcreteNestedTransitionValid
        (((compactFormulaValuesTraceState?
          input.2.1 input.1).getD none).getD
            (([] : List (List Nat)), ([] : List Nat)))
        (((compactFormulaValuesTraceState?
          input.2.1 (input.1 + 1)).getD none).getD
            (([] : List (List Nat)), ([] : List Nat)))
        ((compactFormulaValuesParserTrace?
          input.2.2 input.1).getD [])) :=
    compactFormulaValuesConcreteNestedTransitionValid_primrec.comp <|
      Primrec.pair (Primrec.pair hcurrent hnext) hparserTrace
  exact
    (hcurrentPresent.and
      (hnextPresent.and (htracePresent.and hconcrete))).of_eq
        fun input => by
          simp only [CompactFormulaValuesNestedTransitionAt]

abbrev CompactFormulaValuesNestedLocalTraceInput :=
  (Nat × CompactFormulaTokenValuesResult) ×
    (CompactFormulaValuesRepeatDirectTrace ×
      CompactFormulaValuesParserTraceList)

def CompactFormulaValuesNestedLocalTraceValid
    (count : Nat) (start : CompactFormulaTokenValuesResult)
    (states : CompactFormulaValuesRepeatDirectTrace)
    (parserTraces : CompactFormulaValuesParserTraceList) : Prop :=
  states.length = count + 1 ∧
    parserTraces.length = count ∧
    compactFormulaValuesTraceState? states 0 = some start ∧
    ∀ stepIndex < count,
      CompactFormulaValuesNestedTransitionAt
        stepIndex (states, parserTraces)

theorem compactFormulaValuesNestedLocalTraceValid_primrec :
    PrimrecPred (fun input : CompactFormulaValuesNestedLocalTraceInput =>
      CompactFormulaValuesNestedLocalTraceValid
        input.1.1 input.1.2 input.2.1 input.2.2) := by
  let Input := CompactFormulaValuesNestedLocalTraceInput
  have hcount : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hstart : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hstates : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hparserTraces : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hstateLength : PrimrecPred (fun input : Input =>
      input.2.1.length = input.1.1 + 1) :=
    Primrec.eq.comp (Primrec.list_length.comp hstates)
      (Primrec.succ.comp hcount)
  have hparserLength : PrimrecPred (fun input : Input =>
      input.2.2.length = input.1.1) :=
    Primrec.eq.comp (Primrec.list_length.comp hparserTraces) hcount
  have hinitial : PrimrecPred (fun input : Input =>
      compactFormulaValuesTraceState? input.2.1 0 = some input.1.2) :=
    Primrec.eq.comp
      (compactFormulaValuesTraceState?_primrec.comp
        hstates (Primrec.const 0))
      (Primrec.option_some.comp hstart)
  have htraceData : Primrec (fun input : Input =>
      (input.2.1, input.2.2)) :=
    Primrec.pair hstates hparserTraces
  have hbounded : PrimrecRel (fun (indices : List Nat)
      (traceData : CompactFormulaValuesRepeatDirectTrace ×
        CompactFormulaValuesParserTraceList) =>
      ∀ stepIndex ∈ indices,
        CompactFormulaValuesNestedTransitionAt stepIndex traceData) :=
    PrimrecRel.forall_mem_list
      compactFormulaValuesNestedTransitionAt_primrec
  have hall : PrimrecPred (fun input : Input =>
      ∀ stepIndex < input.1.1,
        CompactFormulaValuesNestedTransitionAt
          stepIndex (input.2.1, input.2.2)) :=
    (hbounded.comp (Primrec.list_range.comp hcount) htraceData).of_eq
      fun input => by simp
  exact
    (hstateLength.and
      (hparserLength.and (hinitial.and hall))).of_eq fun input => by
        simp only [CompactFormulaValuesNestedLocalTraceValid]

theorem compactFormulaValuesNestedTransitionAt_implies_step
    {stepIndex : Nat}
    {states : CompactFormulaValuesRepeatDirectTrace}
    {parserTraces : CompactFormulaValuesParserTraceList}
    (hvalid : CompactFormulaValuesNestedTransitionAt
      stepIndex (states, parserTraces)) :
    compactFormulaValuesTraceState? states (stepIndex + 1) =
      compactFormulaValuesStepOption
        (compactFormulaValuesTraceState? states stepIndex) := by
  unfold CompactFormulaValuesNestedTransitionAt at hvalid
  dsimp only at hvalid
  rcases hvalid with
    ⟨hcurrentPresent, hnextPresent, htracePresent, hconcrete⟩
  cases hcurrent : compactFormulaValuesTraceState? states stepIndex with
  | none =>
      simp [hcurrent] at hcurrentPresent
  | some currentState =>
      cases currentState with
      | none =>
          simp [hcurrent] at hcurrentPresent
      | some current =>
          cases hnext :
              compactFormulaValuesTraceState? states (stepIndex + 1) with
          | none =>
              simp [hnext] at hnextPresent
          | some nextState =>
              cases nextState with
              | none =>
                  simp [hnext] at hnextPresent
              | some next =>
                  cases htrace :
                      compactFormulaValuesParserTrace?
                        parserTraces stepIndex with
                  | none =>
                      simp [htrace] at htracePresent
                  | some parserTrace =>
                      simp only [hcurrent, hnext, htrace,
                        Option.getD_some] at hconcrete
                      rcases hconcrete with
                        ⟨hparserTrace, hnextValues⟩
                      have hparserResult :
                          compactFormulaTokenParser 0 current.2 =
                            some next.2 :=
                        (compactFormulaTokenParser_eq_some_iff_exists_directTrace
                          0 current.2 next.2).mpr
                            ⟨parserTrace, hparserTrace⟩
                      have hvalueResult :
                          compactFormulaTokenValueParser 0 current.2 =
                            some
                              (consumedTokenPrefix current.2 next.2,
                                next.2) :=
                        (compactFormulaTokenValueParser_eq_some_iff
                          0 current.2
                            (consumedTokenPrefix current.2 next.2)
                            next.2).mpr ⟨hparserResult, rfl⟩
                      simp only [compactFormulaValuesStepOption,
                        Option.map_some,
                        compactFormulaTokenValuesStep,
                        Option.bind_some, hvalueResult,
                        Option.some.injEq]
                      exact Prod.ext hnextValues rfl

theorem compactFormulaValuesNestedLocalTraceValid_implies_local
    {count : Nat} {start : CompactFormulaTokenValuesResult}
    {states : CompactFormulaValuesRepeatDirectTrace}
    {parserTraces : CompactFormulaValuesParserTraceList}
    (hvalid : CompactFormulaValuesNestedLocalTraceValid
      count start states parserTraces) :
    CompactFormulaValuesLocalTraceValid count start states := by
  refine ⟨hvalid.1, hvalid.2.2.1, ?_⟩
  intro stepIndex hstepIndex
  exact compactFormulaValuesNestedTransitionAt_implies_step
    (hvalid.2.2.2 stepIndex hstepIndex)

theorem compactFormulaValuesStateAt_eq_some_of_final
    {count : Nat} {start : CompactFormulaTokenValuesResult}
    {output : List (List Nat) × List Nat}
    (hfinal : compactFormulaValuesStateAt start count = some output)
    {stepIndex : Nat} (hstepIndex : stepIndex <= count) :
    ∃ state : List (List Nat) × List Nat,
      compactFormulaValuesStateAt start stepIndex = some state := by
  cases hstate : compactFormulaValuesStateAt start stepIndex with
  | none =>
      have hsplit : (count - stepIndex) + stepIndex = count :=
        Nat.sub_add_cancel hstepIndex
      have hfinalNone :
          compactFormulaValuesStateAt start count = none := by
        unfold compactFormulaValuesStateAt at hstate ⊢
        rw [← hsplit, Function.iterate_add_apply, hstate,
          compactFormulaTokenValuesStep_iterate_none]
      rw [hfinal] at hfinalNone
      contradiction
  | some state =>
      exact ⟨state, rfl⟩

def CompactFormulaValuesStateAtNestedTransitionValid
    (start : CompactFormulaTokenValuesResult) (stepIndex : Nat)
    (parserTrace : CompactFormulaTokenParserDirectTrace) : Prop :=
  match compactFormulaValuesStateAt start stepIndex,
      compactFormulaValuesStateAt start (stepIndex + 1) with
  | some current, some next =>
      CompactFormulaValuesConcreteNestedTransitionValid
        current next parserTrace
  | _, _ => False

theorem compactFormulaValuesStateAt_nestedTransition_exists
    {count : Nat} {start : CompactFormulaTokenValuesResult}
    {output : List (List Nat) × List Nat}
    (hfinal : compactFormulaValuesStateAt start count = some output)
    (stepIndex : Nat) (hstepIndex : stepIndex < count) :
    ∃ parserTrace : CompactFormulaTokenParserDirectTrace,
      CompactFormulaValuesStateAtNestedTransitionValid
        start stepIndex parserTrace := by
  obtain ⟨current, hcurrent⟩ :=
    compactFormulaValuesStateAt_eq_some_of_final hfinal
      (Nat.le_of_lt hstepIndex)
  obtain ⟨next, hnext⟩ :=
    compactFormulaValuesStateAt_eq_some_of_final hfinal (by omega :
      stepIndex + 1 <= count)
  have hstep :
      compactFormulaTokenValuesStep (some current) = some next := by
    rw [← hcurrent, ← hnext]
    simp [compactFormulaValuesStateAt,
      Function.iterate_succ_apply']
  cases hvalue : compactFormulaTokenValueParser 0 current.2 with
  | none =>
      simp [compactFormulaTokenValuesStep, hvalue] at hstep
  | some formulaResult =>
      rcases formulaResult with ⟨formulaValue, afterFormula⟩
      have hnextEq :
          next =
            (current.1 ++ [formulaValue], afterFormula) := by
        simpa [compactFormulaTokenValuesStep, hvalue] using hstep.symm
      obtain ⟨hparserResult, hformulaValue⟩ :=
        (compactFormulaTokenValueParser_eq_some_iff
          0 current.2 formulaValue afterFormula).mp hvalue
      obtain ⟨parserTrace, hparserTrace⟩ :=
        (compactFormulaTokenParser_eq_some_iff_exists_directTrace
          0 current.2 afterFormula).mp hparserResult
      refine ⟨parserTrace, ?_⟩
      simp only [CompactFormulaValuesStateAtNestedTransitionValid,
        hcurrent, hnext]
      refine ⟨?_, ?_⟩
      · simpa [hnextEq] using hparserTrace
      rw [hnextEq]
      simp [hformulaValue]

theorem compactFormulaValuesCanonicalNestedLocalTrace_exists
    {count : Nat} {start : CompactFormulaTokenValuesResult}
    {output : List (List Nat) × List Nat}
    (hfinal : compactFormulaValuesStateAt start count = some output) :
    ∃ parserTraces : CompactFormulaValuesParserTraceList,
      CompactFormulaValuesNestedLocalTraceValid count start
        (compactFormulaValuesStateTrace count start) parserTraces := by
  have hexists (index : Fin count) :
      ∃ parserTrace : CompactFormulaTokenParserDirectTrace,
        CompactFormulaValuesStateAtNestedTransitionValid
          start index.1 parserTrace :=
    compactFormulaValuesStateAt_nestedTransition_exists
      hfinal index.1 index.2
  let parserTraceAt (index : Fin count) :
      CompactFormulaTokenParserDirectTrace :=
    Classical.choose (hexists index)
  have hparserTraceAt (index : Fin count) :
      CompactFormulaValuesStateAtNestedTransitionValid
        start index.1 (parserTraceAt index) :=
    Classical.choose_spec (hexists index)
  let parserTraces : CompactFormulaValuesParserTraceList :=
    List.ofFn parserTraceAt
  refine ⟨parserTraces,
    compactFormulaValuesStateTrace_length count start, ?_, ?_, ?_⟩
  · simp [parserTraces]
  · simpa [compactFormulaValuesStateAt] using
      compactFormulaValuesStateTrace_getElem?
        count 0 start (Nat.zero_le count)
  · intro stepIndex hstepIndex
    have hcurrent := compactFormulaValuesStateTrace_getElem?
      count stepIndex start (Nat.le_of_lt hstepIndex)
    have hnext := compactFormulaValuesStateTrace_getElem?
      count (stepIndex + 1) start (by omega)
    have htrace :
        compactFormulaValuesParserTrace? parserTraces stepIndex =
          some (parserTraceAt ⟨stepIndex, hstepIndex⟩) := by
      simp [compactFormulaValuesParserTrace?, parserTraces, hstepIndex]
    have hchosen := hparserTraceAt ⟨stepIndex, hstepIndex⟩
    cases hcurrentAt : compactFormulaValuesStateAt start stepIndex with
    | none =>
        simp [CompactFormulaValuesStateAtNestedTransitionValid,
          hcurrentAt] at hchosen
    | some current =>
        cases hnextAt :
            compactFormulaValuesStateAt start (stepIndex + 1) with
        | none =>
            simp [CompactFormulaValuesStateAtNestedTransitionValid,
              hcurrentAt, hnextAt] at hchosen
        | some next =>
            unfold CompactFormulaValuesNestedTransitionAt
            rw [hcurrent, hnext, htrace]
            simp [hcurrentAt, hnextAt]
            simpa [CompactFormulaValuesStateAtNestedTransitionValid,
              hcurrentAt, hnextAt] using hchosen

abbrev CompactFormulaValuesNestedDirectTrace :=
  CompactFormulaValuesRepeatDirectTrace ×
    CompactFormulaValuesParserTraceList

def CompactFormulaValuesNestedDirectTraceValid
    (count : Nat) (tokens : List Nat)
    (values : List (List Nat)) (suffix : List Nat)
    (trace : CompactFormulaValuesNestedDirectTrace) : Prop :=
  CompactFormulaValuesNestedLocalTraceValid count
      (compactFormulaTokenValuesInitial tokens) trace.1 trace.2 ∧
    compactFormulaValuesTraceState? trace.1 count =
      some (some (values, suffix))

theorem compactFormulaValuesNestedDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × List Nat) ×
          ((List (List Nat) × List Nat) ×
            CompactFormulaValuesNestedDirectTrace) =>
      CompactFormulaValuesNestedDirectTraceValid
        input.1.1 input.1.2 input.2.1.1 input.2.1.2 input.2.2) := by
  let Input :=
    (Nat × List Nat) ×
      ((List (List Nat) × List Nat) ×
        CompactFormulaValuesNestedDirectTrace)
  have hcount : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have htokens : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hvalues : Primrec (fun input : Input => input.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hsuffix : Primrec (fun input : Input => input.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have htrace : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hstates : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp htrace
  have hparserTraces : Primrec (fun input : Input => input.2.2.2) :=
    Primrec.snd.comp htrace
  have hstart : Primrec (fun input : Input =>
      compactFormulaTokenValuesInitial input.1.2) :=
    compactFormulaTokenValuesInitial_primrec.comp htokens
  have hnested : PrimrecPred (fun input : Input =>
      CompactFormulaValuesNestedLocalTraceValid input.1.1
        (compactFormulaTokenValuesInitial input.1.2)
        input.2.2.1 input.2.2.2) :=
    compactFormulaValuesNestedLocalTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hcount hstart)
        (Primrec.pair hstates hparserTraces)
  have hfinalState : Primrec (fun input : Input =>
      compactFormulaValuesTraceState? input.2.2.1 input.1.1) :=
    compactFormulaValuesTraceState?_primrec.comp hstates hcount
  have hexpected : Primrec (fun input : Input =>
      some (some (input.2.1.1, input.2.1.2))) :=
    Primrec.option_some.comp
      (Primrec.option_some.comp (Primrec.pair hvalues hsuffix))
  have hfinal : PrimrecPred (fun input : Input =>
      compactFormulaValuesTraceState? input.2.2.1 input.1.1 =
        some (some (input.2.1.1, input.2.1.2))) :=
    Primrec.eq.comp hfinalState hexpected
  exact
    (hnested.and hfinal).of_eq fun input => by
      simp only [CompactFormulaValuesNestedDirectTraceValid]

theorem compactFormulaTokenValuesRepeat_eq_some_iff_exists_nestedDirectTrace
    (count : Nat) (tokens : List Nat)
    (values : List (List Nat)) (suffix : List Nat) :
    compactFormulaTokenValuesRepeat count tokens = some (values, suffix) ↔
      ∃ trace : CompactFormulaValuesNestedDirectTrace,
        CompactFormulaValuesNestedDirectTraceValid
          count tokens values suffix trace := by
  constructor
  · intro hrun
    let start := compactFormulaTokenValuesInitial tokens
    let states := compactFormulaValuesStateTrace count start
    have hfinalAt : compactFormulaValuesStateAt start count =
        some (values, suffix) := by
      simpa [compactFormulaValuesStateAt,
        compactFormulaTokenValuesRepeat, start] using hrun
    obtain ⟨parserTraces, hnested⟩ :=
      compactFormulaValuesCanonicalNestedLocalTrace_exists hfinalAt
    refine ⟨(states, parserTraces), hnested, ?_⟩
    rw [compactFormulaValuesStateTrace_final]
    exact congrArg some hfinalAt
  · rintro ⟨⟨states, parserTraces⟩, hnested, hfinal⟩
    have hlocal :=
      compactFormulaValuesNestedLocalTraceValid_implies_local hnested
    have hstates := compactFormulaValuesLocalTraceValid_eq_canonical hlocal
    rw [hstates, compactFormulaValuesStateTrace_final] at hfinal
    simpa [compactFormulaTokenValuesRepeat] using hfinal

abbrev CompactSequentTokenValueDirectTrace :=
  CompactFormulaValuesNestedDirectTrace

def CompactSequentTokenValueDirectTraceValid
    (tokens : List Nat) (values : List (List Nat)) (suffix : List Nat)
    (states : CompactSequentTokenValueDirectTrace) : Prop :=
  match tokens with
  | [] => False
  | count :: tail =>
      CompactFormulaValuesNestedDirectTraceValid
        count tail values suffix states

theorem compactSequentTokenValueParser_eq_some_iff_exists_directTrace
    (tokens : List Nat) (values : List (List Nat)) (suffix : List Nat) :
    compactSequentTokenValueParser tokens = some (values, suffix) ↔
      ∃ states : CompactSequentTokenValueDirectTrace,
        CompactSequentTokenValueDirectTraceValid
          tokens values suffix states := by
  cases tokens with
  | nil =>
      simp [compactSequentTokenValueParser,
        CompactSequentTokenValueDirectTraceValid]
  | cons count tail =>
      simpa [compactSequentTokenValueParser,
        CompactSequentTokenValueDirectTraceValid] using
        compactFormulaTokenValuesRepeat_eq_some_iff_exists_nestedDirectTrace
          count tail values suffix

theorem compactSequentTokenValueDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (List Nat × (List (List Nat) × List Nat)) ×
          CompactSequentTokenValueDirectTrace =>
      CompactSequentTokenValueDirectTraceValid
        input.1.1 input.1.2.1 input.1.2.2 input.2) := by
  let Input :=
    (List Nat × (List (List Nat) × List Nat)) ×
      CompactSequentTokenValueDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hvalues : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hsuffix : Primrec (fun input : Input => input.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hstates : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hnonempty : PrimrecPred (fun input : Input => input.1.1 ≠ []) :=
    (Primrec.eq.comp htokens (Primrec.const [])).not
  have hcount : Primrec (fun input : Input =>
      input.1.1.head?.getD 0) :=
    Primrec.option_getD.comp
      (Primrec.list_head?.comp htokens) (Primrec.const 0)
  have htail : Primrec (fun input : Input => input.1.1.tail) :=
    Primrec.list_tail.comp htokens
  have hrepeat : PrimrecPred (fun input : Input =>
      CompactFormulaValuesNestedDirectTraceValid
        (input.1.1.head?.getD 0) input.1.1.tail
        input.1.2.1 input.1.2.2 input.2) :=
    compactFormulaValuesNestedDirectTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hcount htail)
        (Primrec.pair (Primrec.pair hvalues hsuffix) hstates)
  exact
    (hnonempty.and hrepeat).of_eq fun input => by
      cases input.1.1 <;>
        simp [CompactSequentTokenValueDirectTraceValid]

#print axioms compactFormulaValuesStateAt_primrec
#print axioms compactFormulaValuesLocalTraceValid_primrec
#print axioms compactFormulaValuesRepeatDirectTraceValid_primrec
#print axioms compactFormulaTokenValuesRepeat_eq_some_iff_exists_directTrace
#print axioms compactFormulaValuesNestedTransitionAt_primrec
#print axioms compactFormulaValuesNestedLocalTraceValid_primrec
#print axioms compactFormulaValuesNestedLocalTraceValid_implies_local
#print axioms compactFormulaValuesNestedDirectTraceValid_primrec
#print axioms compactFormulaTokenValuesRepeat_eq_some_iff_exists_nestedDirectTrace
#print axioms compactSequentTokenValueDirectTraceValid_primrec
#print axioms compactSequentTokenValueParser_eq_some_iff_exists_directTrace

end FoundationCompactSequentValueDirectTrace
