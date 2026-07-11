import integration.FoundationCompactCertificateDecoderCostPotential

/-!
# Polynomial bounds for packed proof and formula decoders
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPackedDecoderCostPotential

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactListedProofDecoder
open FoundationCompactListedCertifiedVerifier
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost
open FoundationCompactListedProofDecoderCost
open FoundationCompactCertificateDecoderCost
open FoundationCompactListedCertifiedDecoderCost
open FoundationCompactDecoderCostPotential
open FoundationCompactSyntaxDecoderCostPotential
open FoundationCompactListedProofDecoderCostPotential
open FoundationCompactCertificateDecoderCostPotential

def parserCostNoReserve {alpha : Type*}
    (trace : OptionTrace (alpha × List Bool))
    (bits : List Bool) : Prop :=
  match trace.1 with
  | none => trace.2 <= decoderPotential bits.length
  | some (_, suffix) =>
      trace.2 + decoderPotential suffix.length <=
        decoderPotential bits.length

theorem parserCostBound_toNoReserve {alpha : Type*}
    {trace : OptionTrace (alpha × List Bool)} {bits : List Bool}
    (hbound : parserCostBound trace bits) :
    parserCostNoReserve trace bits := by
  unfold parserCostBound parserCostBoundWith parserCostNoReserve at *
  cases hresult : trace.1 with
  | none => simp [hresult] at hbound ⊢; omega
  | some result =>
      rcases result with ⟨value, suffix⟩
      simp [hresult] at hbound ⊢
      omega

theorem decodeCompactListedCertifiedPAProofTrace_potential
    (fuel : Nat) (bits : List Bool) :
    parserCostNoReserve
      (decodeCompactListedCertifiedPAProofTrace fuel bits) bits := by
  have hproof :=
    decodeCompactListedProofTrace_parserCostBound fuel bits
  cases hproofResult : (decodeCompactListedProofTrace fuel bits).1 with
  | none =>
      have hproofBound :
          (decodeCompactListedProofTrace fuel bits).2 +
              parserReserve bits.length <= decoderPotential bits.length := by
        simpa [parserCostBound, parserCostBoundWith, hproofResult] using hproof
      unfold parserCostNoReserve
      simp [decodeCompactListedCertifiedPAProofTrace, traceBind, hproofResult]
      unfold parserReserve at *
      omega
  | some proofResult =>
      rcases proofResult with ⟨tree, afterProof⟩
      have hproofSuffix :=
        decodeCompactListedProofTrace_suffix_le hproofResult
      have hproofBound :
          (decodeCompactListedProofTrace fuel bits).2 +
              decoderPotential afterProof.length +
              parserReserve bits.length <= decoderPotential bits.length := by
        simpa [parserCostBound, parserCostBoundWith, hproofResult] using hproof
      have hcertificate :=
        decodeStructuralValidityCertificateTrace_parserCostBound
          fuel afterProof
      cases hcertificateResult :
          (decodeStructuralValidityCertificateTrace fuel afterProof).1 with
      | none =>
          have hcertificateBound :
              (decodeStructuralValidityCertificateTrace fuel afterProof).2 +
                  parserReserve afterProof.length <=
                decoderPotential afterProof.length := by
            simpa [parserCostBound, parserCostBoundWith,
              hcertificateResult] using hcertificate
          unfold parserCostNoReserve
          simp [decodeCompactListedCertifiedPAProofTrace, traceBind,
            hproofResult, hcertificateResult]
          unfold parserReserve at *
          omega
      | some certificateResult =>
          rcases certificateResult with ⟨certificate, suffix⟩
          have hcertificateSuffix :=
            decodeStructuralValidityCertificateTrace_suffix_le
              hcertificateResult
          have hcertificateBound :
              (decodeStructuralValidityCertificateTrace fuel afterProof).2 +
                  decoderPotential suffix.length +
                  parserReserve afterProof.length <=
                decoderPotential afterProof.length := by
            simpa [parserCostBound, parserCostBoundWith,
              hcertificateResult] using hcertificate
          unfold parserCostNoReserve
          simp [decodeCompactListedCertifiedPAProofTrace, traceBind, tracePure,
            hproofResult, hcertificateResult]
          unfold parserReserve at *
          omega

theorem packedPayloadTrace_cost_le (code : Nat) :
    (packedPayloadTrace code).2 <= 2 * Nat.size code + 3 := by
  dsimp only [packedPayloadTrace]
  rw [Nat.size_eq_bits_len]
  split <;> omega

theorem packedPayloadTrace_success_length_le
    {code : Nat} {payload : List Bool}
    (htrace : (packedPayloadTrace code).1 = some payload) :
    payload.length <= Nat.size code := by
  dsimp only [packedPayloadTrace] at htrace
  split at htrace
  · simp at htrace
    subst payload
    rw [List.length_dropLast, Nat.size_eq_bits_len]
    omega
  · simp at htrace

@[simp] theorem requireEmptySuffixTrace_cost {alpha : Type*}
    (value : alpha) (suffix : List Bool) :
    (requireEmptySuffixTrace value suffix).2 = suffix.length + 2 := by
  unfold requireEmptySuffixTrace
  split <;> rfl

theorem length_add_four_le_decoderPotential (length : Nat) :
    length + 4 <= decoderPotential length := by
  have hbound := quadratic_plus_sixteen_le_decoderPotential length
  have hsquare : length + 4 <= (length + 1) * (length + 1) + 16 := by
    nlinarith
  exact hsquare.trans hbound

theorem packedEnvelope_absorbed (length : Nat) :
    (2 * length + 3) + decoderPotential length + 4 <=
      2 * decoderPotential length := by
  have hlinear := length_add_four_le_decoderPotential length
  have hquadratic := quadratic_plus_sixteen_le_decoderPotential length
  have hlinear' :
      2 * length + 7 <= (length + 1) * (length + 1) + 16 := by
    nlinarith
  have hlinearPotential : 2 * length + 7 <= decoderPotential length :=
    hlinear'.trans hquadratic
  omega

theorem decodeCompactPackedListedCertifiedPAProofTrace_cost_le
    (code : Nat) :
    (decodeCompactPackedListedCertifiedPAProofTrace code).2 <=
      2 * decoderPotential (Nat.size code) := by
  have hpayloadCost := packedPayloadTrace_cost_le code
  cases hpayloadResult : (packedPayloadTrace code).1 with
  | none =>
      simp [decodeCompactPackedListedCertifiedPAProofTrace, traceBind,
        hpayloadResult]
      have hpotential := length_add_four_le_decoderPotential (Nat.size code)
      omega
  | some payload =>
      have hpayloadLength :=
        packedPayloadTrace_success_length_le hpayloadResult
      have hdecode :=
        decodeCompactListedCertifiedPAProofTrace_potential
          (payload.length + 1) payload
      cases hdecodeResult :
          (decodeCompactListedCertifiedPAProofTrace
            (payload.length + 1) payload).1 with
      | none =>
          have hdecodeCost :
              (decodeCompactListedCertifiedPAProofTrace
                (payload.length + 1) payload).2 <=
                decoderPotential payload.length := by
            simpa [parserCostNoReserve, hdecodeResult] using hdecode
          have hpotentialMono := decoderPotential_mono hpayloadLength
          simp [decodeCompactPackedListedCertifiedPAProofTrace, traceBind,
            hpayloadResult, hdecodeResult]
          have henvelope := packedEnvelope_absorbed (Nat.size code)
          omega
      | some proofResult =>
          rcases proofResult with ⟨proof, suffix⟩
          have hdecodeCost :
              (decodeCompactListedCertifiedPAProofTrace
                    (payload.length + 1) payload).2 +
                  decoderPotential suffix.length <=
                decoderPotential payload.length := by
            simpa [parserCostNoReserve, hdecodeResult] using hdecode
          have hpotentialMono := decoderPotential_mono hpayloadLength
          have hsuffixLinear := length_add_four_le_decoderPotential suffix.length
          simp [decodeCompactPackedListedCertifiedPAProofTrace, traceBind,
            hpayloadResult, hdecodeResult, requireEmptySuffixTrace_cost]
          have henvelope := packedEnvelope_absorbed (Nat.size code)
          omega

theorem decodeCompactPackedFormulaTrace_cost_le (code : Nat) :
    (decodeCompactPackedFormulaTrace code).2 <=
      2 * decoderPotential (Nat.size code) := by
  have hpayloadCost := packedPayloadTrace_cost_le code
  cases hpayloadResult : (packedPayloadTrace code).1 with
  | none =>
      simp [decodeCompactPackedFormulaTrace, traceBind, hpayloadResult]
      have hpotential := length_add_four_le_decoderPotential (Nat.size code)
      omega
  | some payload =>
      have hpayloadLength :=
        packedPayloadTrace_success_length_le hpayloadResult
      have hdecode :=
        decodeCompactFormulaTrace_parserCostBound
          0 (payload.length + 1) payload
      cases hdecodeResult :
          (decodeCompactFormulaTrace 0 (payload.length + 1) payload).1 with
      | none =>
          have hdecodeCost :
              (decodeCompactFormulaTrace 0
                (payload.length + 1) payload).2 <=
                decoderPotential payload.length := by
            have hnoReserve := parserCostBound_toNoReserve hdecode
            simpa [parserCostNoReserve, hdecodeResult] using hnoReserve
          have hpotentialMono := decoderPotential_mono hpayloadLength
          simp [decodeCompactPackedFormulaTrace, traceBind,
            hpayloadResult, hdecodeResult]
          have henvelope := packedEnvelope_absorbed (Nat.size code)
          omega
      | some formulaResult =>
          rcases formulaResult with ⟨formula, suffix⟩
          have hnoReserve := parserCostBound_toNoReserve hdecode
          have hdecodeCost :
              (decodeCompactFormulaTrace 0
                    (payload.length + 1) payload).2 +
                  decoderPotential suffix.length <=
                decoderPotential payload.length := by
            simpa [parserCostNoReserve, hdecodeResult] using hnoReserve
          have hpotentialMono := decoderPotential_mono hpayloadLength
          have hsuffixLinear := length_add_four_le_decoderPotential suffix.length
          simp [decodeCompactPackedFormulaTrace, traceBind,
            hpayloadResult, hdecodeResult, requireEmptySuffixTrace_cost]
          have henvelope := packedEnvelope_absorbed (Nat.size code)
          omega

#print axioms decodeCompactListedCertifiedPAProofTrace_potential
#print axioms decodeCompactPackedListedCertifiedPAProofTrace_cost_le
#print axioms decodeCompactPackedFormulaTrace_cost_le

end FoundationCompactPackedDecoderCostPotential
