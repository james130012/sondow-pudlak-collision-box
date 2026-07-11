import integration.FoundationCompactListedProofDecoderCostPotential

/-!
# Amortized cost bounds for compact certificate decoding
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertificateDecoderCostPotential

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactVerifierStructuralBound
open FoundationCompactCertificateDecoderStructuralBound
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost
open FoundationCompactCertificateDecoderCost
open FoundationCompactDecoderCostPotential
open FoundationCompactSyntaxDecoderCostPotential

theorem decodePAAxiomCertificateTrace_suffix_le
    {fuel : Nat} {bits suffix : List Bool}
    {certificate : PAAxiomCertificate}
    (htrace : (decodePAAxiomCertificateTrace fuel bits).1 =
      some (certificate, suffix)) :
    suffix.length <= bits.length := by
  have hdecode :
      decodePAAxiomCertificate fuel bits = some (certificate, suffix) := by
    rw [← decodePAAxiomCertificateTrace_result fuel]
    exact htrace
  have hbound := decodePAAxiomCertificate_parseWeight_le hdecode
  omega

theorem decodeStructuralValidityCertificateTrace_suffix_le
    {fuel : Nat} {bits suffix : List Bool}
    {certificate : StructuralValidityCertificate}
    (htrace : (decodeStructuralValidityCertificateTrace fuel bits).1 =
      some (certificate, suffix)) :
    suffix.length <= bits.length := by
  have hdecode :
      decodeStructuralValidityCertificate fuel bits =
        some (certificate, suffix) := by
    rw [← decodeStructuralValidityCertificateTrace_result fuel]
    exact htrace
  have hbound := decodeStructuralValidityCertificate_parseWeight_le hdecode
  omega

theorem decodePAAxiomCertificateTrace_parserCostBound :
    forall (fuel : Nat) (bits : List Bool),
      parserCostBound (decodePAAxiomCertificateTrace fuel bits) bits := by
  intro fuel
  cases fuel with
  | zero =>
      intro bits
      unfold parserCostBound parserCostBoundWith
      simp [decodePAAxiomCertificateTrace, traceFailure]
      exact one_add_parserReserve_le_decoderPotential bits.length
  | succ fuel =>
      intro bits
      have htagStrong := decodeBinaryNatTrace_primitiveCostBound bits
      cases htagTrace : (decodeBinaryNatTrace bits).1 with
      | none =>
          have htagBound :
              (decodeBinaryNatTrace bits).2 + primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          unfold parserCostBound parserCostBoundWith
          simp [decodePAAxiomCertificateTrace, traceBind, htagTrace]
          unfold parserReserve primitiveReserve at *
          omega
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagBound :
              (decodeBinaryNatTrace bits).2 +
                  decoderPotential afterTag.length +
                  primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          have htagDecode :
              decodeBinaryNat bits = some (tag, afterTag) := by
            rw [← decodeBinaryNatTrace_result bits]
            exact htagTrace
          have htagConsume := decodeBinaryNat_consumes_two htagDecode
          unfold parserCostBound parserCostBoundWith
          simp only [decodePAAxiomCertificateTrace, traceBind, htagTrace]
          rcases tag with
            (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
             _ | _ | _ | _ | _ | _ | _ | _ | _ | tag)
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · cases harityTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                simp_all
                unfold parserReserve primitiveReserve at *
                omega
            | some arityResult =>
                rcases arityResult with ⟨arity, afterArity⟩
                have haritySuffix : afterArity.length <= afterTag.length := by
                  have harityDecode :
                      decodeBinaryNat afterTag = some (arity, afterArity) := by
                    rw [← decodeBinaryNatTrace_result afterTag]
                    exact harityTrace
                  have hconsume := decodeBinaryNat_consumes_two harityDecode
                  omega
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                cases hsymbolTrace : (decodeBinaryNatTrace afterArity).1 with
                | none =>
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some symbolResult =>
                    rcases symbolResult with ⟨symbolCode, suffix⟩
                    have hsymbolSuffix : suffix.length <= afterArity.length := by
                      have hsymbolDecode :
                          decodeBinaryNat afterArity =
                            some (symbolCode, suffix) := by
                        rw [← decodeBinaryNatTrace_result afterArity]
                        exact hsymbolTrace
                      have hconsume :=
                        decodeBinaryNat_consumes_two hsymbolDecode
                      omega
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    cases hfunction :
                        (Encodable.decode₂ _ symbolCode :
                          Option (LO.FirstOrder.Language.Func ℒₒᵣ arity)) with
                    | none =>
                        have harityDecode :
                            decodeBinaryNat afterTag =
                              some (arity, afterArity) := by
                          rw [← decodeBinaryNatTrace_result afterTag]
                          exact harityTrace
                        have hsymbolDecode :
                            decodeBinaryNat afterArity =
                              some (symbolCode, suffix) := by
                          rw [← decodeBinaryNatTrace_result afterArity]
                          exact hsymbolTrace
                        have hcharge :=
                          decodedNatPair_charge_le harityDecode hsymbolDecode
                        simp_all [traceLiftOption]
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some functionSymbol =>
                        have hcharge := arithmeticFunc_decode_charge_le hfunction
                        simp_all [traceLiftOption, tracePure]
                        unfold parserReserve primitiveReserve at *
                        omega
          · cases harityTrace : (decodeBinaryNatTrace afterTag).1 with
            | none =>
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                simp_all
                unfold parserReserve primitiveReserve at *
                omega
            | some arityResult =>
                rcases arityResult with ⟨arity, afterArity⟩
                have haritySuffix : afterArity.length <= afterTag.length := by
                  have harityDecode :
                      decodeBinaryNat afterTag = some (arity, afterArity) := by
                    rw [← decodeBinaryNatTrace_result afterTag]
                    exact harityTrace
                  have hconsume := decodeBinaryNat_consumes_two harityDecode
                  omega
                have harity := decodeBinaryNatTrace_parserCostBound afterTag
                simp [parserCostBound, parserCostBoundWith, harityTrace]
                  at harity
                cases hsymbolTrace : (decodeBinaryNatTrace afterArity).1 with
                | none =>
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some symbolResult =>
                    rcases symbolResult with ⟨symbolCode, suffix⟩
                    have hsymbolSuffix : suffix.length <= afterArity.length := by
                      have hsymbolDecode :
                          decodeBinaryNat afterArity =
                            some (symbolCode, suffix) := by
                        rw [← decodeBinaryNatTrace_result afterArity]
                        exact hsymbolTrace
                      have hconsume :=
                        decodeBinaryNat_consumes_two hsymbolDecode
                      omega
                    have hsymbol :=
                      decodeBinaryNatTrace_parserCostBound afterArity
                    simp [parserCostBound, parserCostBoundWith, hsymbolTrace]
                      at hsymbol
                    cases hrelation :
                        (Encodable.decode₂ _ symbolCode :
                          Option (LO.FirstOrder.Language.Rel ℒₒᵣ arity)) with
                    | none =>
                        have harityDecode :
                            decodeBinaryNat afterTag =
                              some (arity, afterArity) := by
                          rw [← decodeBinaryNatTrace_result afterTag]
                          exact harityTrace
                        have hsymbolDecode :
                            decodeBinaryNat afterArity =
                              some (symbolCode, suffix) := by
                          rw [← decodeBinaryNatTrace_result afterArity]
                          exact hsymbolTrace
                        have hcharge :=
                          decodedNatPair_charge_le harityDecode hsymbolDecode
                        simp_all [traceLiftOption]
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some relationSymbol =>
                        have hcharge := arithmeticRel_decode_charge_le hrelation
                        simp_all [traceLiftOption, tracePure]
                        unfold parserReserve primitiveReserve at *
                        omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · cases hbodyTrace :
                (decodeCompactFormulaTrace 1 fuel afterTag).1 with
            | none =>
                have hbody :=
                  decodeCompactFormulaTrace_parserCostBound 1 fuel afterTag
                simp [parserCostBound, parserCostBoundWith, hbodyTrace] at hbody
                simp_all
                unfold parserReserve primitiveReserve at *
                omega
            | some bodyResult =>
                rcases bodyResult with ⟨body, suffix⟩
                have hbodySuffix :=
                  decodeCompactFormulaTrace_suffix_le hbodyTrace
                have hbody :=
                  decodeCompactFormulaTrace_parserCostBound 1 fuel afterTag
                simp [parserCostBound, parserCostBoundWith, hbodyTrace] at hbody
                simp_all [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
          · simp [traceFailure]
            unfold parserReserve primitiveReserve at *
            omega

theorem decodeStructuralValidityCertificateTrace_parserCostBound :
    forall (fuel : Nat) (bits : List Bool),
      parserCostBound
        (decodeStructuralValidityCertificateTrace fuel bits) bits := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits
      unfold parserCostBound parserCostBoundWith
      simp [decodeStructuralValidityCertificateTrace, traceFailure]
      exact one_add_parserReserve_le_decoderPotential bits.length
  | succ fuel ih =>
      intro bits
      have htagStrong := decodeBinaryNatTrace_primitiveCostBound bits
      cases htagTrace : (decodeBinaryNatTrace bits).1 with
      | none =>
          have htagBound :
              (decodeBinaryNatTrace bits).2 + primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          unfold parserCostBound parserCostBoundWith
          simp [decodeStructuralValidityCertificateTrace, traceBind,
            htagTrace]
          unfold parserReserve primitiveReserve at *
          omega
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagBound :
              (decodeBinaryNatTrace bits).2 +
                  decoderPotential afterTag.length +
                  primitiveReserve bits.length <=
                decoderPotential bits.length := by
            simpa [parserCostBoundWith, htagTrace] using htagStrong
          have htagDecode :
              decodeBinaryNat bits = some (tag, afterTag) := by
            rw [← decodeBinaryNatTrace_result bits]
            exact htagTrace
          have htagConsume := decodeBinaryNat_consumes_two htagDecode
          unfold parserCostBound parserCostBoundWith
          simp only [decodeStructuralValidityCertificateTrace, traceBind,
            htagTrace]
          rcases tag with (_ | _ | _ | _ | tag)
          · simp [tracePure]
            unfold parserReserve primitiveReserve at *
            omega
          · cases haxiomTrace :
                (decodePAAxiomCertificateTrace fuel afterTag).1 with
            | none =>
                have haxiom :=
                  decodePAAxiomCertificateTrace_parserCostBound fuel afterTag
                simp [parserCostBound, parserCostBoundWith, haxiomTrace]
                  at haxiom
                simp_all
                unfold parserReserve primitiveReserve at *
                omega
            | some axiomResult =>
                rcases axiomResult with ⟨axiomCertificate, suffix⟩
                have haxiomSuffix :=
                  decodePAAxiomCertificateTrace_suffix_le haxiomTrace
                have haxiom :=
                  decodePAAxiomCertificateTrace_parserCostBound fuel afterTag
                simp [parserCostBound, parserCostBoundWith, haxiomTrace]
                  at haxiom
                simp_all [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
          · cases hpremiseTrace :
                (decodeStructuralValidityCertificateTrace fuel afterTag).1 with
            | none =>
                have hpremise := ih afterTag
                simp [parserCostBound, parserCostBoundWith, hpremiseTrace]
                  at hpremise
                simp_all
                unfold parserReserve primitiveReserve at *
                omega
            | some premiseResult =>
                rcases premiseResult with ⟨premise, suffix⟩
                have hpremiseSuffix :=
                  decodeStructuralValidityCertificateTrace_suffix_le
                    hpremiseTrace
                have hpremise := ih afterTag
                simp [parserCostBound, parserCostBoundWith, hpremiseTrace]
                  at hpremise
                simp_all [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
          · cases hleftTrace :
                (decodeStructuralValidityCertificateTrace fuel afterTag).1 with
            | none =>
                have hleft := ih afterTag
                simp [parserCostBound, parserCostBoundWith, hleftTrace] at hleft
                simp_all
                unfold parserReserve primitiveReserve at *
                omega
            | some leftResult =>
                rcases leftResult with ⟨left, afterLeft⟩
                have hleftSuffix :=
                  decodeStructuralValidityCertificateTrace_suffix_le hleftTrace
                have hleft := ih afterTag
                simp [parserCostBound, parserCostBoundWith, hleftTrace] at hleft
                cases hrightTrace :
                    (decodeStructuralValidityCertificateTrace fuel
                      afterLeft).1 with
                | none =>
                    have hright := ih afterLeft
                    simp [parserCostBound, parserCostBoundWith, hrightTrace]
                      at hright
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some rightResult =>
                    rcases rightResult with ⟨right, suffix⟩
                    have hrightSuffix :=
                      decodeStructuralValidityCertificateTrace_suffix_le
                        hrightTrace
                    have hright := ih afterLeft
                    simp [parserCostBound, parserCostBoundWith, hrightTrace]
                      at hright
                    simp_all [tracePure]
                    unfold parserReserve primitiveReserve at *
                    omega
          · simp [traceFailure]
            unfold parserReserve primitiveReserve at *
            omega

#print axioms decodePAAxiomCertificateTrace_suffix_le
#print axioms decodeStructuralValidityCertificateTrace_suffix_le
#print axioms decodePAAxiomCertificateTrace_parserCostBound
#print axioms decodeStructuralValidityCertificateTrace_parserCostBound

end FoundationCompactCertificateDecoderCostPotential
