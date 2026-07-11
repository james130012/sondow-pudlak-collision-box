import integration.FoundationCompactSyntaxDecoderCost

/-!
# Cost trace for the list-preserving compact proof decoder
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofDecoderCost

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactListedProofDecoder
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost

def decodeCompactSequentListTrace
    (fuel : Nat) (bits : List Bool) :
    OptionTrace
      (List LO.FirstOrder.ArithmeticProposition × List Bool) :=
  traceBind (decodeBinaryNatTrace bits) fun cardinalityResult =>
    traceBind
      (decodeManyVectorTrace (decodeCompactFormulaTrace 0 fuel)
        cardinalityResult.1 cardinalityResult.2)
      fun formulasResult =>
        tracePure (formulasResult.1.toList, formulasResult.2)

theorem decodeCompactSequentListTrace_result
    (fuel : Nat) (bits : List Bool) :
    (decodeCompactSequentListTrace fuel bits).1 =
      decodeCompactSequentList fuel bits := by
  have hmany := decodeManyVectorTrace_result
    (decodeCompactFormulaTrace 0 fuel)
    (decodeCompactFormula 0 fuel)
    (decodeCompactFormulaTrace_result 0 fuel)
  simp [decodeCompactSequentListTrace, decodeCompactSequentList,
    traceBind_result, tracePure_result,
    decodeBinaryNatTrace_result, hmany]

def decodeCompactListedProofTrace :
    Nat -> List Bool ->
      OptionTrace (ListedCheckedPAProofTree × List Bool)
  | 0, _ => traceFailure
  | fuel + 1, bits =>
      traceBind (decodeBinaryNatTrace bits) fun tagResult =>
        traceBind (decodeCompactSequentListTrace fuel tagResult.2)
          fun sequentResult =>
            match tagResult.1 with
            | 0 =>
                traceBind
                  (decodeCompactFormulaTrace 0 fuel sequentResult.2)
                  fun formulaResult =>
                    tracePure
                      (.closed sequentResult.1 formulaResult.1,
                        formulaResult.2)
            | 1 =>
                traceBind
                  (decodeCompactFormulaTrace 0 fuel sequentResult.2)
                  fun formulaResult =>
                    traceBind
                      (traceLiftOption
                        (propositionToSentence formulaResult.1)
                        ((binaryFormulaCode formulaResult.1).length + 1))
                      fun sentence =>
                        tracePure
                          (.axm sequentResult.1 sentence, formulaResult.2)
            | 2 => tracePure (.verum sequentResult.1, sequentResult.2)
            | 3 =>
                traceBind
                  (decodeCompactFormulaTrace 0 fuel sequentResult.2)
                  fun leftFormulaResult =>
                    traceBind
                      (decodeCompactFormulaTrace 0 fuel leftFormulaResult.2)
                      fun rightFormulaResult =>
                        traceBind
                          (decodeCompactListedProofTrace fuel
                            rightFormulaResult.2)
                          fun leftResult =>
                            traceBind
                              (decodeCompactListedProofTrace fuel leftResult.2)
                              fun rightResult =>
                                tracePure
                                  (.and sequentResult.1 leftFormulaResult.1
                                    rightFormulaResult.1 leftResult.1
                                    rightResult.1,
                                    rightResult.2)
            | 4 =>
                traceBind
                  (decodeCompactFormulaTrace 0 fuel sequentResult.2)
                  fun leftFormulaResult =>
                    traceBind
                      (decodeCompactFormulaTrace 0 fuel leftFormulaResult.2)
                      fun rightFormulaResult =>
                        traceBind
                          (decodeCompactListedProofTrace fuel
                            rightFormulaResult.2)
                          fun premiseResult =>
                            tracePure
                              (.or sequentResult.1 leftFormulaResult.1
                                rightFormulaResult.1 premiseResult.1,
                                premiseResult.2)
            | 5 =>
                traceBind
                  (decodeCompactFormulaTrace 1 fuel sequentResult.2)
                  fun formulaResult =>
                    traceBind
                      (decodeCompactListedProofTrace fuel formulaResult.2)
                      fun premiseResult =>
                        tracePure
                          (.all sequentResult.1 formulaResult.1 premiseResult.1,
                            premiseResult.2)
            | 6 =>
                traceBind
                  (decodeCompactFormulaTrace 1 fuel sequentResult.2)
                  fun formulaResult =>
                    traceBind
                      (decodeCompactTermTrace 0 fuel formulaResult.2)
                      fun witnessResult =>
                        traceBind
                          (decodeCompactListedProofTrace fuel witnessResult.2)
                          fun premiseResult =>
                            tracePure
                              (.exs sequentResult.1 formulaResult.1
                                witnessResult.1 premiseResult.1,
                                premiseResult.2)
            | 7 =>
                traceBind
                  (decodeCompactListedProofTrace fuel sequentResult.2)
                  fun premiseResult =>
                    tracePure
                      (.wk sequentResult.1 premiseResult.1, premiseResult.2)
            | 8 =>
                traceBind
                  (decodeCompactListedProofTrace fuel sequentResult.2)
                  fun premiseResult =>
                    tracePure
                      (.shift sequentResult.1 premiseResult.1, premiseResult.2)
            | 9 =>
                traceBind
                  (decodeCompactFormulaTrace 0 fuel sequentResult.2)
                  fun formulaResult =>
                    traceBind
                      (decodeCompactListedProofTrace fuel formulaResult.2)
                      fun leftResult =>
                        traceBind
                          (decodeCompactListedProofTrace fuel leftResult.2)
                          fun rightResult =>
                            tracePure
                              (.cut sequentResult.1 formulaResult.1
                                leftResult.1 rightResult.1,
                                rightResult.2)
            | _ => traceFailure

theorem decodeCompactListedProofTrace_result
    (fuel : Nat) (bits : List Bool) :
    (decodeCompactListedProofTrace fuel bits).1 =
      decodeCompactListedProof fuel bits := by
  induction fuel generalizing bits with
  | zero => simp [decodeCompactListedProofTrace,
      decodeCompactListedProof, traceFailure]
  | succ fuel ih =>
      have hsequent := decodeCompactSequentListTrace_result fuel
      have hformula (arity : Nat) :=
        decodeCompactFormulaTrace_result arity fuel
      have hterm (arity : Nat) := decodeCompactTermTrace_result arity fuel
      simp only [decodeCompactListedProofTrace, decodeCompactListedProof,
        traceBind_result, decodeBinaryNatTrace_result]
      cases htag : decodeBinaryNat bits with
      | none => simp
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          simp only [Option.bind_eq_bind, Option.bind_some]
          cases hseq : decodeCompactSequentList fuel afterTag with
          | none =>
              simp [decodeCompactSequentListTrace_result, hseq]
          | some sequentResult =>
              rcases sequentResult with ⟨Gamma, afterSequent⟩
              simp only [Option.bind_some]
              rcases tag with
                (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag) <;>
                simp [hseq, traceBind_result, tracePure_result,
                  traceFailure_result, traceLiftOption_result,
                  decodeCompactSequentListTrace_result, hformula, hterm, ih]

#print axioms decodeCompactSequentListTrace_result
#print axioms decodeCompactListedProofTrace_result

end FoundationCompactListedProofDecoderCost
