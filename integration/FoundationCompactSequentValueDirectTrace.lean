import integration.FoundationCompactNumericSyntaxValueParser
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

abbrev CompactSequentTokenValueDirectTrace :=
  CompactFormulaValuesRepeatDirectTrace

def CompactSequentTokenValueDirectTraceValid
    (tokens : List Nat) (values : List (List Nat)) (suffix : List Nat)
    (states : CompactSequentTokenValueDirectTrace) : Prop :=
  match tokens with
  | [] => False
  | count :: tail =>
      CompactFormulaValuesRepeatDirectTraceValid
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
        compactFormulaTokenValuesRepeat_eq_some_iff_exists_directTrace
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
      CompactFormulaValuesRepeatDirectTraceValid
        (input.1.1.head?.getD 0) input.1.1.tail
        input.1.2.1 input.1.2.2 input.2) :=
    compactFormulaValuesRepeatDirectTraceValid_primrec.comp <|
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
#print axioms compactSequentTokenValueDirectTraceValid_primrec
#print axioms compactSequentTokenValueParser_eq_some_iff_exists_directTrace

end FoundationCompactSequentValueDirectTrace
