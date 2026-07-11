import integration.FoundationCompactProofTokenMachine
import integration.FoundationCompactCertificateTokenMachine
import integration.FoundationCompactNumericSyntaxValueParser
import Mathlib.Computability.Primrec.List

/-!
# Shared local traces for compact token parsers

The syntax, proof, and structural-certificate parsers use the same concrete
state shape.  This module supplies one initial/step/final tableau framework
and instantiates it at each real parser step.  It opens the bounded outer
iterators; atomic subparsers called by a step remain a later audit boundary.
-/

namespace FoundationCompactParserDirectTrace

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericSyntaxValueParser

abbrev CompactUnifiedParserState := CompactSyntaxParserState

def compactParserStateAt
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (start : CompactUnifiedParserState) (stepIndex : Nat) :
    CompactUnifiedParserState :=
  (step^[stepIndex]) start

theorem compactParserStateAt_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    Primrec₂ (compactParserStateAt step) := by
  apply Primrec₂.mk
  have hiterateStep : Primrec₂
      (fun (_input : CompactUnifiedParserState × Nat)
          (state : CompactUnifiedParserState) => step state) := by
    apply Primrec₂.mk
    exact hstep.comp Primrec.snd
  exact
    (Primrec.nat_iterate Primrec.snd Primrec.fst hiterateStep).of_eq
      fun input => by rfl

def compactParserStateTrace
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState) :
    List CompactUnifiedParserState :=
  (List.range (fuel + 1)).map fun stepIndex =>
    compactParserStateAt step start stepIndex

theorem compactParserStateTrace_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    Primrec₂ (compactParserStateTrace step) := by
  apply Primrec₂.mk
  let Input := Nat × CompactUnifiedParserState
  have hindices : Primrec (fun input : Input =>
      List.range (input.1 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.fst)
  have hstate : Primrec₂
      (fun (input : Input) (stepIndex : Nat) =>
        compactParserStateAt step input.2 stepIndex) :=
    (compactParserStateAt_primrec hstep).comp₂
      (Primrec.snd.comp Primrec₂.left) Primrec₂.right
  exact
    (Primrec.list_map hindices hstate).of_eq fun input => by rfl

def compactParserTraceState?
    (states : List CompactUnifiedParserState) (stepIndex : Nat) :
    Option CompactUnifiedParserState :=
  states[stepIndex]?

theorem compactParserTraceState?_primrec :
    Primrec₂ compactParserTraceState? :=
  Primrec.list_getElem?

def compactParserStepOption
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (state : Option CompactUnifiedParserState) :
    Option CompactUnifiedParserState :=
  state.map step

theorem compactParserStepOption_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    Primrec (compactParserStepOption step) := by
  refine (Primrec.option_map Primrec.id ?_).of_eq fun state => by rfl
  apply Primrec₂.mk
  exact hstep.comp Primrec.snd

@[simp] theorem compactParserStateTrace_length
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState) :
    (compactParserStateTrace step fuel start).length = fuel + 1 := by
  simp [compactParserStateTrace]

theorem compactParserStateTrace_getElem?
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel stepIndex : Nat) (start : CompactUnifiedParserState)
    (hstepIndex : stepIndex <= fuel) :
    compactParserTraceState?
        (compactParserStateTrace step fuel start) stepIndex =
      some (compactParserStateAt step start stepIndex) := by
  simp [compactParserTraceState?, compactParserStateTrace, hstepIndex]

theorem compactParserStateTrace_final
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState) :
    compactParserTraceState?
        (compactParserStateTrace step fuel start) fuel =
      some ((step^[fuel]) start) := by
  simpa [compactParserStateAt] using
    compactParserStateTrace_getElem? step fuel fuel start (by rfl)

def CompactParserCanonicalTraceValid
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState)
    (states : List CompactUnifiedParserState) : Prop :=
  states = compactParserStateTrace step fuel start

theorem compactParserCanonicalTraceValid_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    PrimrecPred (fun input :
        (Nat × CompactUnifiedParserState) ×
          List CompactUnifiedParserState =>
      CompactParserCanonicalTraceValid step
        input.1.1 input.1.2 input.2) := by
  have hcanonical : Primrec (fun input :
      (Nat × CompactUnifiedParserState) ×
        List CompactUnifiedParserState =>
      compactParserStateTrace step input.1.1 input.1.2) :=
    (compactParserStateTrace_primrec hstep).comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  exact
    (Primrec.eq.comp Primrec.snd hcanonical).of_eq fun input => by
      simp [CompactParserCanonicalTraceValid]

def CompactParserLocalTraceValid
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState)
    (states : List CompactUnifiedParserState) : Prop :=
  states.length = fuel + 1 ∧
    compactParserTraceState? states 0 = some start ∧
    ∀ stepIndex < fuel,
      compactParserTraceState? states (stepIndex + 1) =
        compactParserStepOption step
          (compactParserTraceState? states stepIndex)

abbrev CompactParserLocalTraceInput :=
  (Nat × CompactUnifiedParserState) ×
    List CompactUnifiedParserState

def CompactParserTransitionAt
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (stepIndex : Nat) (input : CompactParserLocalTraceInput) : Prop :=
  compactParserTraceState? input.2 (stepIndex + 1) =
    compactParserStepOption step
      (compactParserTraceState? input.2 stepIndex)

theorem compactParserTransitionAt_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    PrimrecRel (CompactParserTransitionAt step) := by
  have hindex : Primrec
      (fun pair : Nat × CompactParserLocalTraceInput => pair.1) :=
    Primrec.fst
  have hstates : Primrec
      (fun pair : Nat × CompactParserLocalTraceInput => pair.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcurrent : Primrec
      (fun pair : Nat × CompactParserLocalTraceInput =>
        compactParserTraceState? pair.2.2 pair.1) :=
    compactParserTraceState?_primrec.comp hstates hindex
  have hnextIndex : Primrec
      (fun pair : Nat × CompactParserLocalTraceInput => pair.1 + 1) :=
    Primrec.succ.comp hindex
  have hnext : Primrec
      (fun pair : Nat × CompactParserLocalTraceInput =>
        compactParserTraceState? pair.2.2 (pair.1 + 1)) :=
    compactParserTraceState?_primrec.comp hstates hnextIndex
  have hstepped : Primrec
      (fun pair : Nat × CompactParserLocalTraceInput =>
        compactParserStepOption step
          (compactParserTraceState? pair.2.2 pair.1)) :=
    (compactParserStepOption_primrec hstep).comp hcurrent
  exact
    (Primrec.eq.comp hnext hstepped).of_eq fun pair => by
      simp [CompactParserTransitionAt]

theorem compactParserStateTrace_localValid
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState) :
    CompactParserLocalTraceValid step fuel start
      (compactParserStateTrace step fuel start) := by
  refine ⟨compactParserStateTrace_length step fuel start, ?_, ?_⟩
  · simpa [compactParserStateAt] using
      compactParserStateTrace_getElem?
        step fuel 0 start (Nat.zero_le fuel)
  · intro stepIndex hstepIndex
    rw [compactParserStateTrace_getElem? step fuel (stepIndex + 1)
      start (by omega)]
    rw [compactParserStateTrace_getElem? step fuel stepIndex
      start (Nat.le_of_lt hstepIndex)]
    simp [compactParserStateAt, compactParserStepOption,
      Function.iterate_succ_apply']

theorem compactParserLocalTraceValid_stateAt
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    {fuel : Nat} {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid step fuel start states)
    {stepIndex : Nat} (hstepIndex : stepIndex <= fuel) :
    compactParserTraceState? states stepIndex =
      some (compactParserStateAt step start stepIndex) := by
  induction stepIndex with
  | zero =>
      simpa [compactParserStateAt] using hvalid.2.1
  | succ stepIndex ih =>
      have hlt : stepIndex < fuel := by omega
      have hprevious := ih (by omega)
      rw [show stepIndex + 1 = stepIndex.succ by omega,
        hvalid.2.2 stepIndex hlt, hprevious]
      simp [compactParserStateAt, compactParserStepOption,
        Function.iterate_succ_apply']

theorem compactParserLocalTraceValid_eq_canonical
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    {fuel : Nat} {start : CompactUnifiedParserState}
    {states : List CompactUnifiedParserState}
    (hvalid : CompactParserLocalTraceValid step fuel start states) :
    states = compactParserStateTrace step fuel start := by
  apply List.ext_getElem?
  intro stepIndex
  by_cases hstepIndex : stepIndex <= fuel
  · change
      compactParserTraceState? states stepIndex =
        compactParserTraceState?
          (compactParserStateTrace step fuel start) stepIndex
    rw [compactParserLocalTraceValid_stateAt hvalid hstepIndex]
    rw [compactParserStateTrace_getElem?
      step fuel stepIndex start hstepIndex]
  · have hstatesLength : states.length = fuel + 1 := hvalid.1
    have hcanonicalLength :=
      compactParserStateTrace_length step fuel start
    have houtside : fuel + 1 <= stepIndex := by omega
    rw [List.getElem?_eq_none (by omega : states.length <= stepIndex)]
    rw [List.getElem?_eq_none (by omega :
      (compactParserStateTrace step fuel start).length <= stepIndex)]

theorem compactParserLocalTraceValid_iff_canonical
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState)
    (states : List CompactUnifiedParserState) :
    CompactParserLocalTraceValid step fuel start states ↔
      CompactParserCanonicalTraceValid step fuel start states := by
  constructor
  · exact compactParserLocalTraceValid_eq_canonical
  · intro hvalid
    rw [hvalid]
    exact compactParserStateTrace_localValid step fuel start

theorem compactParserLocalTraceValid_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    PrimrecPred (fun input : CompactParserLocalTraceInput =>
      CompactParserLocalTraceValid step
        input.1.1 input.1.2 input.2) := by
  exact (compactParserCanonicalTraceValid_primrec hstep).of_eq
    fun input =>
      (compactParserLocalTraceValid_iff_canonical step
        input.1.1 input.1.2 input.2).symm

def compactParserStateOutputOption
    (state : Option CompactUnifiedParserState) :
    Option (Option (List Nat)) :=
  state.map compactSyntaxParserStateOutput

theorem compactParserStateOutputOption_primrec :
    Primrec compactParserStateOutputOption := by
  refine (Primrec.option_map Primrec.id ?_).of_eq fun state => by rfl
  apply Primrec₂.mk
  exact compactSyntaxParserStateOutput_primrec.comp Primrec.snd

def CompactParserOutputLocalTraceValid
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState)
    (expected : Option (List Nat))
    (states : List CompactUnifiedParserState) : Prop :=
  CompactParserLocalTraceValid step fuel start states ∧
    compactParserStateOutputOption
      (compactParserTraceState? states fuel) = some expected

theorem compactParserOutputLocalTraceValid_primrec
    {step : CompactUnifiedParserState -> CompactUnifiedParserState}
    (hstep : Primrec step) :
    PrimrecPred (fun input :
        (Nat × CompactUnifiedParserState) ×
          (Option (List Nat) × List CompactUnifiedParserState) =>
      CompactParserOutputLocalTraceValid step
        input.1.1 input.1.2 input.2.1 input.2.2) := by
  let Input :=
    (Nat × CompactUnifiedParserState) ×
      (Option (List Nat) × List CompactUnifiedParserState)
  have hfuel : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hstart : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hexpected : Primrec (fun input : Input => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hstates : Primrec (fun input : Input => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hlocal : PrimrecPred (fun input : Input =>
      CompactParserLocalTraceValid step
        input.1.1 input.1.2 input.2.2) :=
    (compactParserLocalTraceValid_primrec hstep).comp <|
      Primrec.pair (Primrec.pair hfuel hstart) hstates
  have hfinalState : Primrec (fun input : Input =>
      compactParserTraceState? input.2.2 input.1.1) :=
    compactParserTraceState?_primrec.comp hstates hfuel
  have houtput : Primrec (fun input : Input =>
      compactParserStateOutputOption
        (compactParserTraceState? input.2.2 input.1.1)) :=
    compactParserStateOutputOption_primrec.comp hfinalState
  have htarget : Primrec (fun input : Input => some input.2.1) :=
    Primrec.option_some.comp hexpected
  have hfinal : PrimrecPred (fun input : Input =>
      compactParserStateOutputOption
          (compactParserTraceState? input.2.2 input.1.1) =
        some input.2.1) :=
    Primrec.eq.comp houtput htarget
  exact
    (hlocal.and hfinal).of_eq fun input => by
      simp only [CompactParserOutputLocalTraceValid]

theorem compactParserOutput_eq_iff_exists_localTrace
    (step : CompactUnifiedParserState -> CompactUnifiedParserState)
    (fuel : Nat) (start : CompactUnifiedParserState)
    (expected : Option (List Nat)) :
    compactSyntaxParserStateOutput ((step^[fuel]) start) = expected ↔
      ∃ states : List CompactUnifiedParserState,
        CompactParserOutputLocalTraceValid
          step fuel start expected states := by
  constructor
  · intro houtput
    refine ⟨compactParserStateTrace step fuel start,
      compactParserStateTrace_localValid step fuel start, ?_⟩
    rw [compactParserStateTrace_final]
    simpa [compactParserStateOutputOption] using houtput
  · rintro ⟨states, hlocal, houtput⟩
    have hstates := compactParserLocalTraceValid_eq_canonical hlocal
    rw [hstates, compactParserStateTrace_final] at houtput
    simpa [compactParserStateOutputOption] using houtput

abbrev CompactProofTokenParserDirectTrace :=
  List CompactUnifiedParserState

def CompactProofTokenParserDirectTraceValid
    (tokens suffix : List Nat)
    (states : CompactProofTokenParserDirectTrace) : Prop :=
  CompactParserOutputLocalTraceValid compactProofParserStep
    (compactProofParserFuelBound tokens)
    (compactProofParserInitialState tokens) (some suffix) states

theorem compactProofTokenParserDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (List Nat × List Nat) × CompactProofTokenParserDirectTrace =>
      CompactProofTokenParserDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (List Nat × List Nat) × CompactProofTokenParserDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hsuffix : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hstates : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hfuel : Primrec (fun input : Input =>
      compactProofParserFuelBound input.1.1) :=
    compactProofParserFuelBound_primrec.comp htokens
  have hstart : Primrec (fun input : Input =>
      compactProofParserInitialState input.1.1) :=
    compactProofParserInitialState_primrec.comp htokens
  have hexpected : Primrec (fun input : Input => some input.1.2) :=
    Primrec.option_some.comp hsuffix
  exact
    ((compactParserOutputLocalTraceValid_primrec
      compactProofParserStep_primrec).comp <|
        Primrec.pair (Primrec.pair hfuel hstart)
          (Primrec.pair hexpected hstates)).of_eq fun input => by
            simp only [CompactProofTokenParserDirectTraceValid]

theorem compactProofTokenParser_eq_some_iff_exists_directTrace
    (tokens suffix : List Nat) :
    compactProofTokenParser tokens = some suffix ↔
      ∃ states : CompactProofTokenParserDirectTrace,
        CompactProofTokenParserDirectTraceValid tokens suffix states := by
  simpa [CompactProofTokenParserDirectTraceValid,
    compactProofTokenParser, compactProofTokenParserRun] using
      compactParserOutput_eq_iff_exists_localTrace
        compactProofParserStep (compactProofParserFuelBound tokens)
        (compactProofParserInitialState tokens) (some suffix)

abbrev CompactCertificateTokenParserDirectTrace :=
  List CompactUnifiedParserState

def CompactCertificateTokenParserDirectTraceValid
    (tokens suffix : List Nat)
    (states : CompactCertificateTokenParserDirectTrace) : Prop :=
  CompactParserOutputLocalTraceValid compactCertificateParserStep
    (compactCertificateParserFuelBound tokens)
    (compactCertificateParserInitialState tokens) (some suffix) states

theorem compactCertificateTokenParserDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (List Nat × List Nat) × CompactCertificateTokenParserDirectTrace =>
      CompactCertificateTokenParserDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (List Nat × List Nat) × CompactCertificateTokenParserDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hsuffix : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hstates : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hfuel : Primrec (fun input : Input =>
      compactCertificateParserFuelBound input.1.1) :=
    compactCertificateParserFuelBound_primrec.comp htokens
  have hstart : Primrec (fun input : Input =>
      compactCertificateParserInitialState input.1.1) :=
    compactCertificateParserInitialState_primrec.comp htokens
  have hexpected : Primrec (fun input : Input => some input.1.2) :=
    Primrec.option_some.comp hsuffix
  exact
    ((compactParserOutputLocalTraceValid_primrec
      compactCertificateParserStep_primrec).comp <|
        Primrec.pair (Primrec.pair hfuel hstart)
          (Primrec.pair hexpected hstates)).of_eq fun input => by
            simp only [CompactCertificateTokenParserDirectTraceValid]

theorem compactCertificateTokenParser_eq_some_iff_exists_directTrace
    (tokens suffix : List Nat) :
    compactStructuralCertificateTokenParser tokens = some suffix ↔
      ∃ states : CompactCertificateTokenParserDirectTrace,
        CompactCertificateTokenParserDirectTraceValid
          tokens suffix states := by
  simpa [CompactCertificateTokenParserDirectTraceValid,
    compactStructuralCertificateTokenParser,
    compactStructuralCertificateTokenParserRun] using
      compactParserOutput_eq_iff_exists_localTrace
        compactCertificateParserStep
        (compactCertificateParserFuelBound tokens)
        (compactCertificateParserInitialState tokens) (some suffix)

abbrev CompactFormulaTokenParserDirectTrace :=
  List CompactUnifiedParserState

def CompactFormulaTokenParserDirectTraceValid
    (binderArity : Nat) (tokens suffix : List Nat)
    (states : CompactFormulaTokenParserDirectTrace) : Prop :=
  CompactParserOutputLocalTraceValid compactSyntaxParserStep
    (compactSyntaxRunFuelBound tokens)
    (compactFormulaParserInitialState binderArity tokens)
    (some suffix) states

theorem compactFormulaTokenParserDirectTraceValid_primrec :
    PrimrecPred (fun input :
        ((Nat × List Nat) × List Nat) ×
          CompactFormulaTokenParserDirectTrace =>
      CompactFormulaTokenParserDirectTraceValid
        input.1.1.1 input.1.1.2 input.1.2 input.2) := by
  let Input :=
    ((Nat × List Nat) × List Nat) ×
      CompactFormulaTokenParserDirectTrace
  have hbinder : Primrec (fun input : Input => input.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htokens : Primrec (fun input : Input => input.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hsuffix : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hstates : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hfuel : Primrec (fun input : Input =>
      compactSyntaxRunFuelBound input.1.1.2) :=
    compactSyntaxRunFuelBound_primrec.comp htokens
  have hstart : Primrec (fun input : Input =>
      compactFormulaParserInitialState input.1.1.1 input.1.1.2) :=
    compactFormulaParserInitialState_primrec.comp hbinder htokens
  have hexpected : Primrec (fun input : Input => some input.1.2) :=
    Primrec.option_some.comp hsuffix
  exact
    ((compactParserOutputLocalTraceValid_primrec
      compactSyntaxParserStep_primrec).comp <|
        Primrec.pair (Primrec.pair hfuel hstart)
          (Primrec.pair hexpected hstates)).of_eq fun input => by
            simp only [CompactFormulaTokenParserDirectTraceValid]

theorem compactFormulaTokenParser_eq_some_iff_exists_directTrace
    (binderArity : Nat) (tokens suffix : List Nat) :
    compactFormulaTokenParser binderArity tokens = some suffix ↔
      ∃ states : CompactFormulaTokenParserDirectTrace,
        CompactFormulaTokenParserDirectTraceValid
          binderArity tokens suffix states := by
  simpa [CompactFormulaTokenParserDirectTraceValid,
    compactFormulaTokenParser, compactFormulaTokenParserRun] using
      compactParserOutput_eq_iff_exists_localTrace
        compactSyntaxParserStep (compactSyntaxRunFuelBound tokens)
        (compactFormulaParserInitialState binderArity tokens) (some suffix)

#print axioms compactParserTransitionAt_primrec
#print axioms compactParserLocalTraceValid_primrec
#print axioms compactProofTokenParserDirectTraceValid_primrec
#print axioms compactProofTokenParser_eq_some_iff_exists_directTrace
#print axioms compactCertificateTokenParserDirectTraceValid_primrec
#print axioms compactCertificateTokenParser_eq_some_iff_exists_directTrace
#print axioms compactFormulaTokenParserDirectTraceValid_primrec
#print axioms compactFormulaTokenParser_eq_some_iff_exists_directTrace

end FoundationCompactParserDirectTrace
