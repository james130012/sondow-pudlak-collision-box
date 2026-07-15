import integration.FoundationCompactNumericFormulaFree
import integration.FoundationCompactNumericFormulaShift
import integration.FoundationCompactNumericFormulaSubstitution
import integration.FoundationCompactNumericFormulaNegation
import integration.FoundationCompactNumericFormulaFvSup
import integration.FoundationCompactNumericFormulaFixitr
import Mathlib.Computability.Primrec.List

/-!
# Shared finite traces for the six numeric formula transforms

The public verifier uses six syntax-directed token machines.  This module
places their genuine executable steps behind one finite mode selector and
records every intermediate `(parser state, emitted output)` pair.  Local
initial/step/length validity is proved equivalent to the canonical iterate;
no transformation result is supplied as an assumption.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericFormulaTransformTrace

open FoundationCompactSyntaxTokenMachine

abbrev CompactFormulaTransformState :=
  CompactSyntaxParserState × List Nat

/-- `0 = free`, `1 = shift`, `2 = substitution`, `3 = negation`,
`4 = free-variable list`, and `5 = fixitr`.  Substitution reads the witness;
fixitr uses its length as the capture count.  Other modes fall back to
negation. -/
abbrev CompactFormulaTransformControl := Nat × List Nat

def compactFormulaTransformStep
    (control : CompactFormulaTransformControl)
    (state : CompactFormulaTransformState) : CompactFormulaTransformState :=
  if control.1 = 0 then
    FoundationCompactNumericFormulaFree.compactFormulaFreeStep state
  else if control.1 = 1 then
    FoundationCompactNumericFormulaShift.compactFormulaShiftStep state
  else if control.1 = 2 then
    FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionStep
      control.2 state
  else if control.1 = 4 then
    FoundationCompactNumericFormulaFvSup.compactFormulaFvListStep state
  else if control.1 = 5 then
    FoundationCompactNumericFormulaFixitr.compactFormulaFixitrStep
      control.2.length state
  else
    FoundationCompactNumericFormulaNegation.compactFormulaNegationStep state

theorem compactFormulaTransformStep_primrec :
    Primrec₂ compactFormulaTransformStep := by
  apply Primrec₂.mk
  let Input := CompactFormulaTransformControl × CompactFormulaTransformState
  have hmode : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hwitness : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hstate : Primrec (fun input : Input => input.2) := Primrec.snd
  have hzero : PrimrecPred (fun input : Input => input.1.1 = 0) :=
    Primrec.eq.comp hmode (Primrec.const 0)
  have hone : PrimrecPred (fun input : Input => input.1.1 = 1) :=
    Primrec.eq.comp hmode (Primrec.const 1)
  have htwo : PrimrecPred (fun input : Input => input.1.1 = 2) :=
    Primrec.eq.comp hmode (Primrec.const 2)
  have hfour : PrimrecPred (fun input : Input => input.1.1 = 4) :=
    Primrec.eq.comp hmode (Primrec.const 4)
  have hfive : PrimrecPred (fun input : Input => input.1.1 = 5) :=
    Primrec.eq.comp hmode (Primrec.const 5)
  have hfree : Primrec (fun input : Input =>
      FoundationCompactNumericFormulaFree.compactFormulaFreeStep input.2) :=
    FoundationCompactNumericFormulaFree.compactFormulaFreeStep_primrec.comp
      hstate
  have hshift : Primrec (fun input : Input =>
      FoundationCompactNumericFormulaShift.compactFormulaShiftStep input.2) :=
    FoundationCompactNumericFormulaShift.compactFormulaShiftStep_primrec.comp
      hstate
  have hsubstitution : Primrec (fun input : Input =>
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionStep
        input.1.2 input.2) :=
    FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionStep_primrec.comp
      hwitness hstate
  have hfvList : Primrec (fun input : Input =>
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListStep input.2) :=
    FoundationCompactNumericFormulaFvSup.compactFormulaFvListStep_primrec.comp
      hstate
  have hfixitr : Primrec (fun input : Input =>
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrStep
        input.1.2.length input.2) :=
    FoundationCompactNumericFormulaFixitr.compactFormulaFixitrStep_primrec.comp
      (Primrec.list_length.comp hwitness) hstate
  have hnegation : Primrec (fun input : Input =>
      FoundationCompactNumericFormulaNegation.compactFormulaNegationStep input.2) :=
    FoundationCompactNumericFormulaNegation.compactFormulaNegationStep_primrec.comp
      hstate
  exact
    (Primrec.ite hzero hfree
      (Primrec.ite hone hshift
        (Primrec.ite htwo hsubstitution
          (Primrec.ite hfour hfvList
            (Primrec.ite hfive hfixitr hnegation))))).of_eq fun input => by
          simp [compactFormulaTransformStep]

@[simp] theorem compactFormulaTransformStep_free
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactFormulaTransformStep (0, witness) state =
      FoundationCompactNumericFormulaFree.compactFormulaFreeStep state := by
  simp [compactFormulaTransformStep]

@[simp] theorem compactFormulaTransformStep_shift
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactFormulaTransformStep (1, witness) state =
      FoundationCompactNumericFormulaShift.compactFormulaShiftStep state := by
  simp [compactFormulaTransformStep]

@[simp] theorem compactFormulaTransformStep_substitution
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactFormulaTransformStep (2, witness) state =
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionStep
        witness state := by
  simp [compactFormulaTransformStep]

@[simp] theorem compactFormulaTransformStep_negation
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactFormulaTransformStep (3, witness) state =
      FoundationCompactNumericFormulaNegation.compactFormulaNegationStep state := by
  simp [compactFormulaTransformStep]

@[simp] theorem compactFormulaTransformStep_fvList
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactFormulaTransformStep (4, witness) state =
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListStep state := by
  simp [compactFormulaTransformStep]

@[simp] theorem compactFormulaTransformStep_fixitr
    (witness : List Nat) (state : CompactFormulaTransformState) :
    compactFormulaTransformStep (5, witness) state =
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrStep
        witness.length state := by
  simp [compactFormulaTransformStep]

def compactFormulaTransformInitialState
    (binderArity : Nat) (tokens : List Nat) : CompactFormulaTransformState :=
  (compactFormulaParserInitialState binderArity tokens, [])

theorem compactFormulaTransformInitialState_primrec :
    Primrec₂ compactFormulaTransformInitialState := by
  exact Primrec₂.pair.comp₂
    compactFormulaParserInitialState_primrec (Primrec₂.const [])

/-- The second argument is `(binder arity, source tokens)`. -/
def compactFormulaTransformRun
    (control : CompactFormulaTransformControl)
    (binderAndTokens : Nat × List Nat) : CompactFormulaTransformState :=
  ((compactFormulaTransformStep control)^[
      compactSyntaxRunFuelBound binderAndTokens.2])
    (compactFormulaTransformInitialState
      binderAndTokens.1 binderAndTokens.2)

theorem compactFormulaTransformRun_primrec :
    Primrec₂ compactFormulaTransformRun := by
  apply Primrec₂.mk
  let Input := CompactFormulaTransformControl × (Nat × List Nat)
  have hfuel : Primrec (fun input : Input =>
      compactSyntaxRunFuelBound input.2.2) :=
    compactSyntaxRunFuelBound_primrec.comp
      (Primrec.snd.comp Primrec.snd)
  have hinitial : Primrec (fun input : Input =>
      compactFormulaTransformInitialState input.2.1 input.2.2) :=
    compactFormulaTransformInitialState_primrec.comp
      (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  have hstep : Primrec₂
      (fun (input : Input) (state : CompactFormulaTransformState) =>
        compactFormulaTransformStep input.1 state) :=
    compactFormulaTransformStep_primrec.comp₂
      (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right
  exact
    (Primrec.nat_iterate hfuel hinitial hstep).of_eq fun input => by
      rfl

@[simp] theorem compactFormulaTransformRun_free
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformRun (0, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaFree.compactFormulaFreeRun
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformRun_shift
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformRun (1, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaShift.compactFormulaShiftRun
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformRun_substitution
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformRun (2, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionRun
        binderArity (witness, tokens) := by
  rfl

@[simp] theorem compactFormulaTransformRun_negation
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformRun (3, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaNegation.compactFormulaNegationRun
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformRun_fvList
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformRun (4, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListRun
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformRun_fixitr
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformRun (5, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrRun
        binderArity (witness.length, tokens) := by
  rfl

def compactFormulaTransformStateOutput
    (state : CompactFormulaTransformState) :
    Option (List Nat × List Nat) :=
  state.1.2.2.bind fun result =>
    result.map fun suffix => (state.2, suffix)

theorem compactFormulaTransformStateOutput_primrec :
    Primrec compactFormulaTransformStateOutput := by
  have hstatus : Primrec
      (fun state : CompactFormulaTransformState => state.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hinner : Primrec₂
      (fun (state : CompactFormulaTransformState)
          (result : Option (List Nat)) =>
        result.map fun suffix => (state.2, suffix)) := by
    apply Primrec₂.mk
    let Input := CompactFormulaTransformState × Option (List Nat)
    have hresult : Primrec (fun input : Input => input.2) := Primrec.snd
    have hpair : Primrec₂
        (fun (input : Input) (suffix : List Nat) =>
          (input.1.2, suffix)) :=
      Primrec₂.pair.comp₂
        ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).to₂)
        Primrec₂.right
    exact Primrec.option_map hresult hpair
  exact
    (Primrec.option_bind hstatus hinner).of_eq fun state => by rfl

def compactFormulaTransformResult
    (control : CompactFormulaTransformControl)
    (binderAndTokens : Nat × List Nat) : Option (List Nat × List Nat) :=
  compactFormulaTransformStateOutput
    (compactFormulaTransformRun control binderAndTokens)

theorem compactFormulaTransformResult_primrec :
    Primrec₂ compactFormulaTransformResult := by
  exact compactFormulaTransformStateOutput_primrec.comp₂
    compactFormulaTransformRun_primrec

@[simp] theorem compactFormulaTransformResult_free
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformResult (0, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaFree.compactFormulaFreeTokenTransform
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformResult_shift
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformResult (1, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaShift.compactFormulaShiftTokenTransform
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformResult_substitution
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformResult (2, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaSubstitution.compactFormulaSubstitutionTokenTransform
        binderArity (witness, tokens) := by
  rfl

@[simp] theorem compactFormulaTransformResult_negation
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformResult (3, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaNegation.compactFormulaNegationTokenTransform
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformResult_fvList
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformResult (4, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaFvSup.compactFormulaFvListTokenTransform
        binderArity tokens := by
  rfl

@[simp] theorem compactFormulaTransformResult_fixitr
    (binderArity : Nat) (witness tokens : List Nat) :
    compactFormulaTransformResult (5, witness) (binderArity, tokens) =
      FoundationCompactNumericFormulaFixitr.compactFormulaFixitrTokenTransform
        binderArity (witness.length, tokens) := by
  rfl

/-- State reached after exactly `stepIndex` genuine transform steps. -/
def compactFormulaTransformStateAt
    (control : CompactFormulaTransformControl)
    (start : CompactFormulaTransformState) (stepIndex : Nat) :
    CompactFormulaTransformState :=
  ((compactFormulaTransformStep control)^[stepIndex]) start

/-- Canonical non-minimizing trace from time `0` through `fuel`. -/
def compactFormulaTransformStateTrace
    (control : CompactFormulaTransformControl) (fuel : Nat)
    (start : CompactFormulaTransformState) :
    List CompactFormulaTransformState :=
  (List.range (fuel + 1)).map fun stepIndex =>
    compactFormulaTransformStateAt control start stepIndex

def compactFormulaTransformTraceState?
    (states : List CompactFormulaTransformState) (stepIndex : Nat) :
    Option CompactFormulaTransformState :=
  states[stepIndex]?

@[simp] theorem compactFormulaTransformStateTrace_length
    (control : CompactFormulaTransformControl) (fuel : Nat)
    (start : CompactFormulaTransformState) :
    (compactFormulaTransformStateTrace control fuel start).length =
      fuel + 1 := by
  simp [compactFormulaTransformStateTrace]

theorem compactFormulaTransformStateTrace_getElem?
    (control : CompactFormulaTransformControl) (fuel stepIndex : Nat)
    (start : CompactFormulaTransformState) (hstepIndex : stepIndex <= fuel) :
    compactFormulaTransformTraceState?
        (compactFormulaTransformStateTrace control fuel start) stepIndex =
      some (compactFormulaTransformStateAt control start stepIndex) := by
  simp [compactFormulaTransformTraceState?,
    compactFormulaTransformStateTrace, hstepIndex]

def CompactFormulaTransformTraceValid
    (control : CompactFormulaTransformControl) (fuel : Nat)
    (start : CompactFormulaTransformState)
    (states : List CompactFormulaTransformState) : Prop :=
  states = compactFormulaTransformStateTrace control fuel start

/-- Locally checkable length, initial row, and every adjacent transform step. -/
def CompactFormulaTransformLocalTraceValid
    (control : CompactFormulaTransformControl) (fuel : Nat)
    (start : CompactFormulaTransformState)
    (states : List CompactFormulaTransformState) : Prop :=
  states.length = fuel + 1 ∧
    compactFormulaTransformTraceState? states 0 = some start ∧
    ∀ stepIndex < fuel,
      compactFormulaTransformTraceState? states (stepIndex + 1) =
        (compactFormulaTransformTraceState? states stepIndex).map
          (compactFormulaTransformStep control)

theorem compactFormulaTransformStateTrace_localValid
    (control : CompactFormulaTransformControl) (fuel : Nat)
    (start : CompactFormulaTransformState) :
    CompactFormulaTransformLocalTraceValid control fuel start
      (compactFormulaTransformStateTrace control fuel start) := by
  refine ⟨compactFormulaTransformStateTrace_length control fuel start,
    ?_, ?_⟩
  · simpa [compactFormulaTransformStateAt] using
      compactFormulaTransformStateTrace_getElem?
        control fuel 0 start (Nat.zero_le fuel)
  · intro stepIndex hstepIndex
    rw [compactFormulaTransformStateTrace_getElem?
      control fuel (stepIndex + 1) start (by omega)]
    rw [compactFormulaTransformStateTrace_getElem?
      control fuel stepIndex start (Nat.le_of_lt hstepIndex)]
    simp [compactFormulaTransformStateAt,
      Function.iterate_succ_apply']

theorem CompactFormulaTransformLocalTraceValid.stateAt
    {control : CompactFormulaTransformControl} {fuel : Nat}
    {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hvalid : CompactFormulaTransformLocalTraceValid
      control fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex <= fuel) :
    compactFormulaTransformTraceState? states stepIndex =
      some (compactFormulaTransformStateAt control start stepIndex) := by
  induction stepIndex with
  | zero =>
      simpa [compactFormulaTransformStateAt] using hvalid.2.1
  | succ stepIndex ih =>
      have hlt : stepIndex < fuel := by omega
      have hprevious := ih (by omega)
      rw [show stepIndex + 1 = stepIndex.succ by omega,
        hvalid.2.2 stepIndex hlt, hprevious]
      simp [compactFormulaTransformStateAt,
        Function.iterate_succ_apply']

theorem CompactFormulaTransformLocalTraceValid.eq_canonical
    {control : CompactFormulaTransformControl} {fuel : Nat}
    {start : CompactFormulaTransformState}
    {states : List CompactFormulaTransformState}
    (hvalid : CompactFormulaTransformLocalTraceValid
      control fuel start states) :
    states = compactFormulaTransformStateTrace control fuel start := by
  apply List.ext_getElem?
  intro stepIndex
  by_cases hstepIndex : stepIndex <= fuel
  · change
      compactFormulaTransformTraceState? states stepIndex =
        compactFormulaTransformTraceState?
          (compactFormulaTransformStateTrace control fuel start) stepIndex
    rw [hvalid.stateAt hstepIndex]
    rw [compactFormulaTransformStateTrace_getElem?
      control fuel stepIndex start hstepIndex]
  · have hstatesLength : states.length = fuel + 1 := hvalid.1
    have hcanonicalLength :=
      compactFormulaTransformStateTrace_length control fuel start
    have houtside : fuel + 1 <= stepIndex := by omega
    rw [List.getElem?_eq_none (by omega : states.length <= stepIndex)]
    rw [List.getElem?_eq_none (by omega :
      (compactFormulaTransformStateTrace control fuel start).length <=
        stepIndex)]

theorem compactFormulaTransformLocalTraceValid_iff_canonical
    (control : CompactFormulaTransformControl) (fuel : Nat)
    (start : CompactFormulaTransformState)
    (states : List CompactFormulaTransformState) :
    CompactFormulaTransformLocalTraceValid control fuel start states ↔
      CompactFormulaTransformTraceValid control fuel start states := by
  constructor
  · exact CompactFormulaTransformLocalTraceValid.eq_canonical
  · intro hvalid
    rw [hvalid]
    exact compactFormulaTransformStateTrace_localValid control fuel start

#print axioms compactFormulaTransformStep_primrec
#print axioms compactFormulaTransformRun_primrec
#print axioms compactFormulaTransformResult_primrec
#print axioms compactFormulaTransformStateTrace_localValid
#print axioms CompactFormulaTransformLocalTraceValid.stateAt
#print axioms CompactFormulaTransformLocalTraceValid.eq_canonical
#print axioms compactFormulaTransformLocalTraceValid_iff_canonical

end FoundationCompactNumericFormulaTransformTrace
