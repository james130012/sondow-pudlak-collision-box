import integration.FoundationCompactNumericListedPublicVerifier
import Mathlib.Computability.Primrec.List

/-!
# Direct accepted traces for the compact numeric listed verifier

This module exposes a finite, non-minimizing execution witness for the exact
numeric public verifier.  The witness records the two token streams, the
parsed certified parts, the parsed conclusion formula, and every state of the
bounded synchronized task machine.

No existential witness is found by `projection` or `rfind`: an accepting run
itself constructs the canonical finite state list.  This closes the external
trace semantics only.  A later module must give the trace relation a direct
arithmetic formula and compile valid instances into short PA derivations.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTrace

open FoundationCompactListedVerifierArithmeticInput
open FoundationCompactListedPackedBitTokenSynchronization
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedPublicVerifier

/-- State reached after exactly `stepIndex` transitions. -/
def compactNumericVerifierStateAt
    (start : CompactNumericVerifierState) (stepIndex : Nat) :
    CompactNumericVerifierState :=
  (compactNumericVerifierStep^[stepIndex]) start

theorem compactNumericVerifierStateAt_primrec :
    Primrec₂ compactNumericVerifierStateAt := by
  apply Primrec₂.mk
  have hstep : Primrec₂
      (fun (_input : CompactNumericVerifierState × Nat)
          (state : CompactNumericVerifierState) =>
        compactNumericVerifierStep state) :=
    compactNumericVerifierStep_primrec.comp Primrec₂.right
  exact
    (Primrec.nat_iterate Primrec.snd Primrec.fst hstep).of_eq
      fun input => by
        rfl

/-- The canonical non-minimizing list of all states from time `0` through
time `fuel`. -/
def compactNumericVerifierStateTrace
    (fuel : Nat) (start : CompactNumericVerifierState) :
    List CompactNumericVerifierState :=
  (List.range (fuel + 1)).map fun stepIndex =>
    compactNumericVerifierStateAt start stepIndex

theorem compactNumericVerifierStateTrace_primrec :
    Primrec₂ compactNumericVerifierStateTrace := by
  apply Primrec₂.mk
  let Input := Nat × CompactNumericVerifierState
  have hindices : Primrec (fun input : Input =>
      List.range (input.1 + 1)) :=
    Primrec.list_range.comp
      (Primrec.succ.comp Primrec.fst)
  have hstate : Primrec₂
      (fun (input : Input) (stepIndex : Nat) =>
        compactNumericVerifierStateAt input.2 stepIndex) :=
    compactNumericVerifierStateAt_primrec.comp₂
      (Primrec.snd.comp Primrec₂.left) Primrec₂.right
  exact
    (Primrec.list_map hindices hstate).of_eq fun input => by
      rfl

def compactNumericTraceState?
    (states : List CompactNumericVerifierState) (stepIndex : Nat) :
    Option CompactNumericVerifierState :=
  states[stepIndex]?

theorem compactNumericTraceState?_primrec :
    Primrec₂ compactNumericTraceState? := by
  exact Primrec.list_getElem?

@[simp] theorem compactNumericVerifierStateTrace_length
    (fuel : Nat) (start : CompactNumericVerifierState) :
    (compactNumericVerifierStateTrace fuel start).length = fuel + 1 := by
  simp [compactNumericVerifierStateTrace]

theorem compactNumericVerifierStateTrace_getElem?
    (fuel stepIndex : Nat) (start : CompactNumericVerifierState)
    (hstepIndex : stepIndex <= fuel) :
    compactNumericTraceState?
        (compactNumericVerifierStateTrace fuel start) stepIndex =
      some (compactNumericVerifierStateAt start stepIndex) := by
  simp [compactNumericTraceState?, compactNumericVerifierStateTrace,
    hstepIndex]

theorem compactNumericVerifierStateTrace_final
    (fuel : Nat) (start : CompactNumericVerifierState) :
    compactNumericTraceState?
        (compactNumericVerifierStateTrace fuel start) fuel =
      some ((compactNumericVerifierStep^[fuel]) start) := by
  simpa [compactNumericVerifierStateAt] using
    compactNumericVerifierStateTrace_getElem? fuel fuel start (by rfl)

/-- Exact validity of a supplied finite task-machine trace.  The definition
is deliberately deterministic and contains no search for a least witness. -/
def CompactNumericVerifierTraceValid
    (fuel : Nat) (start : CompactNumericVerifierState)
    (states : List CompactNumericVerifierState) : Prop :=
  states = compactNumericVerifierStateTrace fuel start

theorem compactNumericVerifierTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × CompactNumericVerifierState) ×
          List CompactNumericVerifierState =>
      CompactNumericVerifierTraceValid input.1.1 input.1.2 input.2) := by
  have hcanonical : Primrec (fun input :
      (Nat × CompactNumericVerifierState) ×
        List CompactNumericVerifierState =>
      compactNumericVerifierStateTrace input.1.1 input.1.2) :=
    compactNumericVerifierStateTrace_primrec.comp
      (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst)
  exact
    (Primrec.eq.comp Primrec.snd hcanonical).of_eq fun input => by
      simp [CompactNumericVerifierTraceValid]

/-- All data needed to audit one accepting public-verifier run. -/
abbrev CompactNumericListedDirectTrace :=
  List Nat ×
    (List Nat ×
      (CompactNumericCertifiedParts ×
        (List Nat × List CompactNumericVerifierState)))

def compactNumericDirectTraceCertifiedTokens
    (trace : CompactNumericListedDirectTrace) : List Nat :=
  trace.1

def compactNumericDirectTraceFormulaTokens
    (trace : CompactNumericListedDirectTrace) : List Nat :=
  trace.2.1

def compactNumericDirectTraceParts
    (trace : CompactNumericListedDirectTrace) :
    CompactNumericCertifiedParts :=
  trace.2.2.1

def compactNumericDirectTraceFormulaValue
    (trace : CompactNumericListedDirectTrace) : List Nat :=
  trace.2.2.2.1

def compactNumericDirectTraceStates
    (trace : CompactNumericListedDirectTrace) :
    List CompactNumericVerifierState :=
  trace.2.2.2.2

def compactNumericVerifierStateResult
    (state : CompactNumericVerifierState) : Bool :=
  state.2.getD false

theorem compactNumericVerifierStateResult_primrec :
    Primrec compactNumericVerifierStateResult := by
  exact
    (Primrec.option_getD.comp Primrec.snd
      (Primrec.const false)).of_eq fun state => by
        rfl

/-- Direct acceptance witness for the exact two-input public verifier. -/
def CompactNumericListedDirectTraceValid
    (code formulaCode : Nat)
    (trace : CompactNumericListedDirectTrace) : Prop :=
  let certifiedTokens := compactNumericDirectTraceCertifiedTokens trace
  let formulaTokens := compactNumericDirectTraceFormulaTokens trace
  let parts := compactNumericDirectTraceParts trace
  let formulaValue := compactNumericDirectTraceFormulaValue trace
  let states := compactNumericDirectTraceStates trace
  let fuel := compactNumericVerifierFuelBound parts.1 parts.2.1
  let start := compactNumericVerifierInitialState parts.1 parts.2.1
  compactPackedTokenStream code = some certifiedTokens ∧
    compactPackedTokenStream formulaCode = some formulaTokens ∧
    compactNumericCertifiedPartsParser certifiedTokens = some parts ∧
    compactNumericWholeFormulaValue formulaTokens = some formulaValue ∧
    CompactNumericVerifierTraceValid fuel start states ∧
    (compactNumericTraceState? states fuel).map
        compactNumericVerifierStateResult = some true ∧
    tokenFormulaSetEq parts.2.2 [formulaValue] = true ∧
    compactNumericFormulaPayloadMatches formulaCode formulaValue = true

theorem compactNumericListedDirectTraceValid_primrec :
    PrimrecPred (fun input :
        (Nat × Nat) × CompactNumericListedDirectTrace =>
      CompactNumericListedDirectTraceValid
        input.1.1 input.1.2 input.2) := by
  let Input := (Nat × Nat) × CompactNumericListedDirectTrace
  have hcode : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hformulaCode : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have htrace : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hcertifiedTokens : Primrec (fun input : Input =>
      compactNumericDirectTraceCertifiedTokens input.2) :=
    Primrec.fst.comp htrace
  have hformulaTokens : Primrec (fun input : Input =>
      compactNumericDirectTraceFormulaTokens input.2) :=
    Primrec.fst.comp (Primrec.snd.comp htrace)
  have hparts : Primrec (fun input : Input =>
      compactNumericDirectTraceParts input.2) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp htrace))
  have hformulaValue : Primrec (fun input : Input =>
      compactNumericDirectTraceFormulaValue input.2) :=
    Primrec.fst.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp htrace)))
  have hstates : Primrec (fun input : Input =>
      compactNumericDirectTraceStates input.2) :=
    Primrec.snd.comp
      (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp htrace)))
  have hproofTokens : Primrec (fun input : Input =>
      (compactNumericDirectTraceParts input.2).1) :=
    Primrec.fst.comp hparts
  have hcertificateTokens : Primrec (fun input : Input =>
      (compactNumericDirectTraceParts input.2).2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hparts)
  have hconclusion : Primrec (fun input : Input =>
      (compactNumericDirectTraceParts input.2).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hparts)
  have hfuel : Primrec (fun input : Input =>
      compactNumericVerifierFuelBound
        (compactNumericDirectTraceParts input.2).1
        (compactNumericDirectTraceParts input.2).2.1) :=
    compactNumericVerifierFuelBound_primrec.comp
      hproofTokens hcertificateTokens
  have hstart : Primrec (fun input : Input =>
      compactNumericVerifierInitialState
        (compactNumericDirectTraceParts input.2).1
        (compactNumericDirectTraceParts input.2).2.1) :=
    compactNumericVerifierInitialState_primrec.comp
      hproofTokens hcertificateTokens
  have hcodeStream : PrimrecPred (fun input : Input =>
      compactPackedTokenStream input.1.1 =
        some (compactNumericDirectTraceCertifiedTokens input.2)) :=
    Primrec.eq.comp
      (compactPackedTokenStream_primrec.comp hcode)
      (Primrec.option_some.comp hcertifiedTokens)
  have hformulaStream : PrimrecPred (fun input : Input =>
      compactPackedTokenStream input.1.2 =
        some (compactNumericDirectTraceFormulaTokens input.2)) :=
    Primrec.eq.comp
      (compactPackedTokenStream_primrec.comp hformulaCode)
      (Primrec.option_some.comp hformulaTokens)
  have hpartsParse : PrimrecPred (fun input : Input =>
      compactNumericCertifiedPartsParser
          (compactNumericDirectTraceCertifiedTokens input.2) =
        some (compactNumericDirectTraceParts input.2)) :=
    Primrec.eq.comp
      (compactNumericCertifiedPartsParser_primrec.comp hcertifiedTokens)
      (Primrec.option_some.comp hparts)
  have hformulaParse : PrimrecPred (fun input : Input =>
      compactNumericWholeFormulaValue
          (compactNumericDirectTraceFormulaTokens input.2) =
        some (compactNumericDirectTraceFormulaValue input.2)) :=
    Primrec.eq.comp
      (compactNumericWholeFormulaValue_primrec.comp hformulaTokens)
      (Primrec.option_some.comp hformulaValue)
  have hmachineTrace : PrimrecPred (fun input : Input =>
      CompactNumericVerifierTraceValid
        (compactNumericVerifierFuelBound
          (compactNumericDirectTraceParts input.2).1
          (compactNumericDirectTraceParts input.2).2.1)
        (compactNumericVerifierInitialState
          (compactNumericDirectTraceParts input.2).1
          (compactNumericDirectTraceParts input.2).2.1)
        (compactNumericDirectTraceStates input.2)) :=
    compactNumericVerifierTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hfuel hstart) hstates
  have hfinalState : Primrec (fun input : Input =>
      compactNumericTraceState?
        (compactNumericDirectTraceStates input.2)
        (compactNumericVerifierFuelBound
          (compactNumericDirectTraceParts input.2).1
          (compactNumericDirectTraceParts input.2).2.1)) :=
    compactNumericTraceState?_primrec.comp hstates hfuel
  have hfinalResult : Primrec (fun input : Input =>
      (compactNumericTraceState?
        (compactNumericDirectTraceStates input.2)
        (compactNumericVerifierFuelBound
          (compactNumericDirectTraceParts input.2).1
          (compactNumericDirectTraceParts input.2).2.1)).map
            compactNumericVerifierStateResult) :=
    Primrec.option_map hfinalState
      (compactNumericVerifierStateResult_primrec.comp Primrec₂.right)
  have hfinal : PrimrecPred (fun input : Input =>
      (compactNumericTraceState?
        (compactNumericDirectTraceStates input.2)
        (compactNumericVerifierFuelBound
          (compactNumericDirectTraceParts input.2).1
          (compactNumericDirectTraceParts input.2).2.1)).map
            compactNumericVerifierStateResult = some true) :=
    Primrec.eq.comp hfinalResult (Primrec.const (some true))
  have hsingleton : Primrec (fun input : Input =>
      [compactNumericDirectTraceFormulaValue input.2]) :=
    Primrec.list_cons.comp hformulaValue (Primrec.const [])
  have hconclusionCheck : PrimrecPred (fun input : Input =>
      tokenFormulaSetEq
        (compactNumericDirectTraceParts input.2).2.2
        [compactNumericDirectTraceFormulaValue input.2] = true) :=
    Primrec.eq.comp
      (tokenFormulaSetEq_primrec.comp hconclusion hsingleton)
      (Primrec.const true)
  have hpayloadCheck : PrimrecPred (fun input : Input =>
      compactNumericFormulaPayloadMatches input.1.2
          (compactNumericDirectTraceFormulaValue input.2) = true) :=
    Primrec.eq.comp
      (compactNumericFormulaPayloadMatches_primrec.comp
        hformulaCode hformulaValue)
      (Primrec.const true)
  exact
    (hcodeStream.and
      (hformulaStream.and
        (hpartsParse.and
          (hformulaParse.and
            (hmachineTrace.and
              (hfinal.and
                (hconclusionCheck.and hpayloadCheck))))))).of_eq
      fun input => by
        simp only [CompactNumericListedDirectTraceValid]

theorem compactNumericListedPublicVerifier_eq_true_iff_exists_directTrace
    (code formulaCode : Nat) :
    compactNumericListedPublicVerifier code formulaCode = true ↔
      ∃ trace : CompactNumericListedDirectTrace,
        CompactNumericListedDirectTraceValid code formulaCode trace := by
  constructor
  · intro haccept
    cases hcertified : compactPackedTokenStream code with
    | none =>
        simp [compactNumericListedPublicVerifier, hcertified] at haccept
    | some certifiedTokens =>
        cases hformula : compactPackedTokenStream formulaCode with
        | none =>
            simp [compactNumericListedPublicVerifier,
              compactNumericFormulaCodeStreamCheck,
              hcertified, hformula] at haccept
        | some formulaTokens =>
            cases hparts :
                compactNumericCertifiedPartsParser certifiedTokens with
            | none =>
                simp [compactNumericListedPublicVerifier,
                  compactNumericFormulaCodeStreamCheck,
                  compactNumericParsedStreamsCheck,
                  hcertified, hformula, hparts] at haccept
            | some parts =>
                cases hformulaValue :
                    compactNumericWholeFormulaValue formulaTokens with
                | none =>
                    simp [compactNumericListedPublicVerifier,
                      compactNumericFormulaCodeStreamCheck,
                      compactNumericParsedStreamsCheck,
                      hcertified, hformula, hparts, hformulaValue] at haccept
                | some formulaValue =>
                    let fuel :=
                      compactNumericVerifierFuelBound parts.1 parts.2.1
                    let start :=
                      compactNumericVerifierInitialState parts.1 parts.2.1
                    let states :=
                      compactNumericVerifierStateTrace fuel start
                    have hlocal :
                        compactNumericCertifiedPartsLocalCheck
                            parts formulaValue formulaCode = true := by
                      simpa [compactNumericListedPublicVerifier,
                        compactNumericFormulaCodeStreamCheck,
                        compactNumericParsedStreamsCheck,
                        hcertified, hformula, hparts, hformulaValue]
                        using haccept
                    have hlocalParts :
                        compactNumericVerifierResult parts.1 parts.2.1 = true ∧
                          tokenFormulaSetEq parts.2.2 [formulaValue] = true ∧
                          compactNumericFormulaPayloadMatches
                            formulaCode formulaValue = true := by
                      simpa only [compactNumericCertifiedPartsLocalCheck,
                        Bool.and_eq_true] using hlocal
                    have hmachine :
                        compactNumericVerifierResult parts.1 parts.2.1 = true :=
                      hlocalParts.1
                    have hconclusion :
                        tokenFormulaSetEq parts.2.2 [formulaValue] = true :=
                      hlocalParts.2.1
                    have hpayload :
                        compactNumericFormulaPayloadMatches
                            formulaCode formulaValue = true :=
                      hlocalParts.2.2
                    refine ⟨(certifiedTokens,
                      (formulaTokens, (parts, (formulaValue, states)))), ?_⟩
                    simp only [CompactNumericListedDirectTraceValid,
                      compactNumericDirectTraceCertifiedTokens,
                      compactNumericDirectTraceFormulaTokens,
                      compactNumericDirectTraceParts,
                      compactNumericDirectTraceFormulaValue,
                      compactNumericDirectTraceStates]
                    refine ⟨hcertified, hformula, hparts, hformulaValue,
                      rfl, ?_, hconclusion, hpayload⟩
                    change
                      (compactNumericTraceState?
                        (compactNumericVerifierStateTrace fuel start) fuel).map
                          compactNumericVerifierStateResult = some true
                    rw [compactNumericVerifierStateTrace_final]
                    simpa [fuel, start,
                      compactNumericVerifierStateResult,
                      compactNumericVerifierResult,
                      compactNumericVerifierRun] using hmachine
  · rintro ⟨trace, htrace⟩
    let certifiedTokens := compactNumericDirectTraceCertifiedTokens trace
    let formulaTokens := compactNumericDirectTraceFormulaTokens trace
    let parts := compactNumericDirectTraceParts trace
    let formulaValue := compactNumericDirectTraceFormulaValue trace
    let states := compactNumericDirectTraceStates trace
    let fuel := compactNumericVerifierFuelBound parts.1 parts.2.1
    let start := compactNumericVerifierInitialState parts.1 parts.2.1
    change
      compactPackedTokenStream code = some certifiedTokens ∧
        compactPackedTokenStream formulaCode = some formulaTokens ∧
        compactNumericCertifiedPartsParser certifiedTokens = some parts ∧
        compactNumericWholeFormulaValue formulaTokens = some formulaValue ∧
        CompactNumericVerifierTraceValid fuel start states ∧
        (compactNumericTraceState? states fuel).map
            compactNumericVerifierStateResult = some true ∧
        tokenFormulaSetEq parts.2.2 [formulaValue] = true ∧
        compactNumericFormulaPayloadMatches formulaCode formulaValue = true
      at htrace
    rcases htrace with ⟨hcertified, hformula, hparts, hformulaValue,
      hstates, hfinal, hconclusion, hpayload⟩
    have hstatesEq : states =
        compactNumericVerifierStateTrace fuel start := hstates
    have hmachine :
        compactNumericVerifierResult parts.1 parts.2.1 = true := by
      rw [hstatesEq] at hfinal
      change
        (compactNumericTraceState?
          (compactNumericVerifierStateTrace fuel start) fuel).map
            compactNumericVerifierStateResult = some true at hfinal
      rw [compactNumericVerifierStateTrace_final] at hfinal
      simpa [fuel, start,
        compactNumericVerifierStateResult,
        compactNumericVerifierResult,
        compactNumericVerifierRun] using hfinal
    have hlocal :
        compactNumericCertifiedPartsLocalCheck
            parts formulaValue formulaCode = true := by
      simp [compactNumericCertifiedPartsLocalCheck,
        hmachine, hconclusion, hpayload]
    simp [compactNumericListedPublicVerifier,
      compactNumericFormulaCodeStreamCheck,
      compactNumericParsedStreamsCheck,
      hcertified, hformula, hparts, hformulaValue, hlocal]

#print axioms compactNumericVerifierStateAt_primrec
#print axioms compactNumericVerifierStateTrace_primrec
#print axioms compactNumericTraceState?_primrec
#print axioms compactNumericVerifierTraceValid_primrec
#print axioms compactNumericListedDirectTraceValid_primrec
#print axioms compactNumericListedPublicVerifier_eq_true_iff_exists_directTrace

end FoundationCompactNumericListedDirectTrace
