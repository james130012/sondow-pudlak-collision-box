import integration.FoundationCompactListedProofDecoderCost

/-!
# Cost traces for compact PA certificate decoding

Every branch of the PA-axiom certificate decoder and every recursive node of
the structural certificate decoder returns its ordinary result together with
an explicit bit-operation cost.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertificateDecoderCost

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost

def decodePAAxiomCertificateTrace :
    Nat -> List Bool -> OptionTrace (PAAxiomCertificate × List Bool)
  | 0, _ => traceFailure
  | fuel + 1, bits =>
      traceBind (decodeBinaryNatTrace bits) fun tagResult =>
        match tagResult.1 with
        | 0 => tracePure (.eqRefl, tagResult.2)
        | 1 => tracePure (.eqSymm, tagResult.2)
        | 2 => tracePure (.eqTrans, tagResult.2)
        | 3 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun arityResult =>
              traceBind (decodeBinaryNatTrace arityResult.2)
                fun symbolResult =>
                  traceBind
                    (traceLiftOption
                      (Encodable.decode₂ _ symbolResult.1 :
                        Option (LO.FirstOrder.Language.Func
                          ℒₒᵣ arityResult.1))
                      (Nat.size arityResult.1 + Nat.size symbolResult.1 + 1))
                    fun functionSymbol =>
                      tracePure (.eqFuncExt functionSymbol, symbolResult.2)
        | 4 =>
            traceBind (decodeBinaryNatTrace tagResult.2) fun arityResult =>
              traceBind (decodeBinaryNatTrace arityResult.2)
                fun symbolResult =>
                  traceBind
                    (traceLiftOption
                      (Encodable.decode₂ _ symbolResult.1 :
                        Option (LO.FirstOrder.Language.Rel
                          ℒₒᵣ arityResult.1))
                      (Nat.size arityResult.1 + Nat.size symbolResult.1 + 1))
                    fun relationSymbol =>
                      tracePure (.eqRelExt relationSymbol, symbolResult.2)
        | 5 => tracePure (.addZero, tagResult.2)
        | 6 => tracePure (.addAssoc, tagResult.2)
        | 7 => tracePure (.addComm, tagResult.2)
        | 8 => tracePure (.addEqOfLt, tagResult.2)
        | 9 => tracePure (.zeroLe, tagResult.2)
        | 10 => tracePure (.zeroLtOne, tagResult.2)
        | 11 => tracePure (.oneLeOfZeroLt, tagResult.2)
        | 12 => tracePure (.addLtAdd, tagResult.2)
        | 13 => tracePure (.mulZero, tagResult.2)
        | 14 => tracePure (.mulOne, tagResult.2)
        | 15 => tracePure (.mulAssoc, tagResult.2)
        | 16 => tracePure (.mulComm, tagResult.2)
        | 17 => tracePure (.mulLtMul, tagResult.2)
        | 18 => tracePure (.distr, tagResult.2)
        | 19 => tracePure (.ltIrrefl, tagResult.2)
        | 20 => tracePure (.ltTrans, tagResult.2)
        | 21 => tracePure (.ltTri, tagResult.2)
        | 22 =>
            traceBind (decodeCompactFormulaTrace 1 fuel tagResult.2)
              fun bodyResult =>
                tracePure (.induction bodyResult.1, bodyResult.2)
        | _ => traceFailure

theorem decodePAAxiomCertificateTrace_result
    (fuel : Nat) (bits : List Bool) :
    (decodePAAxiomCertificateTrace fuel bits).1 =
      decodePAAxiomCertificate fuel bits := by
  cases fuel with
  | zero =>
      simp [decodePAAxiomCertificateTrace, decodePAAxiomCertificate,
        traceFailure]
  | succ fuel =>
      have hformula := decodeCompactFormulaTrace_result 1 fuel
      simp only [decodePAAxiomCertificateTrace, decodePAAxiomCertificate,
        traceBind_result, decodeBinaryNatTrace_result]
      cases htag : decodeBinaryNat bits with
      | none => simp
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          simp only [Option.bind_eq_bind, Option.bind_some]
          rcases tag with
            (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
             _ | _ | _ | _ | _ | _ | _ | _ | _ | tag) <;>
            simp [traceBind_result, tracePure_result, traceFailure_result,
              traceLiftOption_result, decodeBinaryNatTrace_result, hformula]

def decodeStructuralValidityCertificateTrace :
    Nat -> List Bool ->
      OptionTrace (StructuralValidityCertificate × List Bool)
  | 0, _ => traceFailure
  | fuel + 1, bits =>
      traceBind (decodeBinaryNatTrace bits) fun tagResult =>
        match tagResult.1 with
        | 0 => tracePure (.leaf, tagResult.2)
        | 1 =>
            traceBind (decodePAAxiomCertificateTrace fuel tagResult.2)
              fun certificateResult =>
                tracePure (.axiomCert certificateResult.1,
                  certificateResult.2)
        | 2 =>
            traceBind
              (decodeStructuralValidityCertificateTrace fuel tagResult.2)
              fun premiseResult =>
                tracePure (.unary premiseResult.1, premiseResult.2)
        | 3 =>
            traceBind
              (decodeStructuralValidityCertificateTrace fuel tagResult.2)
              fun leftResult =>
                traceBind
                  (decodeStructuralValidityCertificateTrace fuel leftResult.2)
                  fun rightResult =>
                    tracePure (.binary leftResult.1 rightResult.1,
                      rightResult.2)
        | _ => traceFailure

theorem decodeStructuralValidityCertificateTrace_result
    (fuel : Nat) (bits : List Bool) :
    (decodeStructuralValidityCertificateTrace fuel bits).1 =
      decodeStructuralValidityCertificate fuel bits := by
  induction fuel generalizing bits with
  | zero =>
      simp [decodeStructuralValidityCertificateTrace,
        decodeStructuralValidityCertificate, traceFailure]
  | succ fuel ih =>
      have haxiom := decodePAAxiomCertificateTrace_result fuel
      simp only [decodeStructuralValidityCertificateTrace,
        decodeStructuralValidityCertificate, traceBind_result,
        decodeBinaryNatTrace_result]
      cases htag : decodeBinaryNat bits with
      | none => simp
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          simp only [Option.bind_eq_bind, Option.bind_some]
          rcases tag with (_ | _ | _ | _ | tag) <;>
            simp [traceBind_result, tracePure_result, traceFailure_result,
              haxiom, ih]

#print axioms decodePAAxiomCertificateTrace_result
#print axioms decodeStructuralValidityCertificateTrace_result

end FoundationCompactCertificateDecoderCost
