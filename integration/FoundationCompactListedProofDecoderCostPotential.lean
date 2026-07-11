import integration.FoundationCompactSyntaxDecoderCostPotential
import integration.FoundationCompactListedProofProjectionComplete
import integration.FoundationCompactProofDecoderStructuralBound

/-!
# Amortized cost bounds for list-preserving proof decoding
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactListedProofDecoderCostPotential

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactVerifierStructuralBound
open FoundationCompactCanonicalDecodeLength
open FoundationCompactListedProofDecoder
open FoundationCompactNatDecoderCost
open FoundationCompactSyntaxDecoderCost
open FoundationCompactListedProofDecoderCost
open FoundationCompactDecoderCostPotential
open FoundationCompactSyntaxDecoderCostPotential
open FoundationCompactListedProofProjectionComplete
open FoundationCompactProofDecoderStructuralBound

theorem decodeCompactSequentListTrace_suffix_le
    {fuel : Nat} {bits suffix : List Bool}
    {Gamma : List LO.FirstOrder.ArithmeticProposition}
    (htrace : (decodeCompactSequentListTrace fuel bits).1 =
      some (Gamma, suffix)) :
    suffix.length <= bits.length := by
  have hdecode :
      decodeCompactSequentList fuel bits = some (Gamma, suffix) := by
    rw [← decodeCompactSequentListTrace_result fuel]
    exact htrace
  have hchecked := decodeCompactSequentList_toFinset hdecode
  have hbound := decodeCompactSequent_symbolCount_le hchecked
  omega

theorem decodeCompactListedProofTrace_suffix_le
    {fuel : Nat} {bits suffix : List Bool}
    {tree : ListedCheckedPAProofTree}
    (htrace : (decodeCompactListedProofTrace fuel bits).1 =
      some (tree, suffix)) :
    suffix.length <= bits.length := by
  have hdecode :
      decodeCompactListedProof fuel bits = some (tree, suffix) := by
    rw [← decodeCompactListedProofTrace_result fuel]
    exact htrace
  have hchecked := decodeCompactListedProof_toChecked hdecode
  have hbound := decodeCompactProof_parseWeight_le hchecked
  omega

theorem decodeCompactSequentListTrace_parserCostBound
    (fuel : Nat) (bits : List Bool) :
    parserCostBound (decodeCompactSequentListTrace fuel bits) bits := by
  have hcardinalityStrong := decodeBinaryNatTrace_primitiveCostBound bits
  cases hcardinalityTrace : (decodeBinaryNatTrace bits).1 with
  | none =>
      have hcardinalityBound :
          (decodeBinaryNatTrace bits).2 + primitiveReserve bits.length <=
            decoderPotential bits.length := by
        simpa [parserCostBoundWith, hcardinalityTrace] using
          hcardinalityStrong
      unfold parserCostBound parserCostBoundWith
      simp [decodeCompactSequentListTrace, traceBind, hcardinalityTrace]
      unfold parserReserve primitiveReserve at *
      omega
  | some cardinalityResult =>
      rcases cardinalityResult with ⟨cardinality, afterCardinality⟩
      have hcardinalityBound :
          (decodeBinaryNatTrace bits).2 +
              decoderPotential afterCardinality.length +
              primitiveReserve bits.length <=
            decoderPotential bits.length := by
        simpa [parserCostBoundWith, hcardinalityTrace] using
          hcardinalityStrong
      have hformula := fun formulaBits =>
        decodeCompactFormulaTrace_parserCostBound 0 fuel formulaBits
      have hmany := decodeManyVectorTrace_potential
        (decodeCompactFormulaTrace 0 fuel) hformula
        cardinality afterCardinality
      unfold parserCostBound parserCostBoundWith
      cases hmanyResult :
          (decodeManyVectorTrace (decodeCompactFormulaTrace 0 fuel)
            cardinality afterCardinality).1 with
      | none =>
          simp [hmanyResult] at hmany
          simp [decodeCompactSequentListTrace, traceBind,
            hcardinalityTrace, hmanyResult]
          unfold parserReserve primitiveReserve at *
          omega
      | some formulasResult =>
          rcases formulasResult with ⟨formulas, suffix⟩
          simp [hmanyResult] at hmany
          simp [decodeCompactSequentListTrace, traceBind, tracePure,
            hcardinalityTrace, hmanyResult]
          unfold parserReserve primitiveReserve at *
          omega

theorem decodeCompactListedProofTrace_parserCostBound :
    forall (fuel : Nat) (bits : List Bool),
      parserCostBound (decodeCompactListedProofTrace fuel bits) bits := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits
      unfold parserCostBound parserCostBoundWith
      simp [decodeCompactListedProofTrace, traceFailure]
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
          simp [decodeCompactListedProofTrace, traceBind, htagTrace]
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
          have hsequent :=
            decodeCompactSequentListTrace_parserCostBound fuel afterTag
          cases hsequentTrace :
              (decodeCompactSequentListTrace fuel afterTag).1 with
          | none =>
              have hsequentBound :
                  (decodeCompactSequentListTrace fuel afterTag).2 +
                      parserReserve afterTag.length <=
                    decoderPotential afterTag.length := by
                simpa [parserCostBound, parserCostBoundWith,
                  hsequentTrace] using hsequent
              unfold parserCostBound parserCostBoundWith
              simp [decodeCompactListedProofTrace, traceBind,
                htagTrace, hsequentTrace]
              unfold parserReserve primitiveReserve at *
              omega
          | some sequentResult =>
              rcases sequentResult with ⟨Gamma, afterSequent⟩
              have hsequentBound :
                  (decodeCompactSequentListTrace fuel afterTag).2 +
                      decoderPotential afterSequent.length +
                      parserReserve afterTag.length <=
                    decoderPotential afterTag.length := by
                simpa [parserCostBound, parserCostBoundWith,
                  hsequentTrace] using hsequent
              have hsequentLength :=
                decodeCompactSequentListTrace_suffix_le hsequentTrace
              unfold parserCostBound parserCostBoundWith
              simp only [decodeCompactListedProofTrace, traceBind,
                htagTrace, hsequentTrace]
              rcases tag with
                (_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | tag)
              · cases hformulaTrace :
                    (decodeCompactFormulaTrace 0 fuel afterSequent).1 with
                | none =>
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    simp
                    unfold parserReserve primitiveReserve at *
                    omega
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, suffix⟩
                    have hformulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hformulaTrace
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    simp [tracePure]
                    unfold parserReserve primitiveReserve at *
                    omega
              · cases hformulaTrace :
                    (decodeCompactFormulaTrace 0 fuel afterSequent).1 with
                | none =>
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    simp
                    unfold parserReserve primitiveReserve at *
                    omega
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, suffix⟩
                    have hformulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hformulaTrace
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    have hformulaDecode :
                        decodeCompactFormula 0 fuel afterSequent =
                          some (formula, suffix) := by
                      rw [← decodeCompactFormulaTrace_result 0 fuel]
                      exact hformulaTrace
                    have hformulaLength :=
                      decodeCompactFormula_canonical_length_le hformulaDecode
                    cases hsentence : propositionToSentence formula with
                    | none =>
                        simp [traceLiftOption, hsentence]
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some sentence =>
                        simp [traceLiftOption, tracePure, hsentence]
                        unfold parserReserve primitiveReserve at *
                        omega
              · simp [tracePure]
                unfold parserReserve primitiveReserve at *
                omega
              · cases hleftFormulaTrace :
                    (decodeCompactFormulaTrace 0 fuel afterSequent).1 with
                | none =>
                    have hleftFormula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hleftFormulaTrace] at hleftFormula
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some leftFormulaResult =>
                    rcases leftFormulaResult with
                      ⟨leftFormula, afterLeftFormula⟩
                    have hleftFormulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hleftFormulaTrace
                    have hleftFormula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hleftFormulaTrace] at hleftFormula
                    cases hrightFormulaTrace :
                        (decodeCompactFormulaTrace 0 fuel
                          afterLeftFormula).1 with
                    | none =>
                        have hrightFormula :=
                          decodeCompactFormulaTrace_parserCostBound
                            0 fuel afterLeftFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hrightFormulaTrace] at hrightFormula
                        simp_all
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some rightFormulaResult =>
                        rcases rightFormulaResult with
                          ⟨rightFormula, afterRightFormula⟩
                        have hrightFormulaSuffix :=
                          decodeCompactFormulaTrace_suffix_le
                            hrightFormulaTrace
                        have hrightFormula :=
                          decodeCompactFormulaTrace_parserCostBound
                            0 fuel afterLeftFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hrightFormulaTrace] at hrightFormula
                        cases hleftProofTrace :
                            (decodeCompactListedProofTrace fuel
                              afterRightFormula).1 with
                        | none =>
                            have hleftProof := ih afterRightFormula
                            simp [parserCostBound, parserCostBoundWith,
                              hleftProofTrace] at hleftProof
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some leftProofResult =>
                            rcases leftProofResult with
                              ⟨leftProof, afterLeftProof⟩
                            have hleftProofSuffix :=
                              decodeCompactListedProofTrace_suffix_le
                                hleftProofTrace
                            have hleftProof := ih afterRightFormula
                            simp [parserCostBound, parserCostBoundWith,
                              hleftProofTrace] at hleftProof
                            cases hrightProofTrace :
                                (decodeCompactListedProofTrace fuel
                                  afterLeftProof).1 with
                            | none =>
                                have hrightProof := ih afterLeftProof
                                simp [parserCostBound, parserCostBoundWith,
                                  hrightProofTrace] at hrightProof
                                simp_all
                                unfold parserReserve primitiveReserve at *
                                omega
                            | some rightProofResult =>
                                rcases rightProofResult with
                                  ⟨rightProof, suffix⟩
                                have hrightProofSuffix :=
                                  decodeCompactListedProofTrace_suffix_le
                                    hrightProofTrace
                                have hrightProof := ih afterLeftProof
                                simp [parserCostBound, parserCostBoundWith,
                                  hrightProofTrace] at hrightProof
                                simp_all
                                unfold parserReserve primitiveReserve at *
                                omega
              · cases hleftFormulaTrace :
                    (decodeCompactFormulaTrace 0 fuel afterSequent).1 with
                | none =>
                    have hleftFormula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hleftFormulaTrace] at hleftFormula
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some leftFormulaResult =>
                    rcases leftFormulaResult with
                      ⟨leftFormula, afterLeftFormula⟩
                    have hleftFormulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hleftFormulaTrace
                    have hleftFormula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hleftFormulaTrace] at hleftFormula
                    cases hrightFormulaTrace :
                        (decodeCompactFormulaTrace 0 fuel
                          afterLeftFormula).1 with
                    | none =>
                        have hrightFormula :=
                          decodeCompactFormulaTrace_parserCostBound
                            0 fuel afterLeftFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hrightFormulaTrace] at hrightFormula
                        simp_all
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some rightFormulaResult =>
                        rcases rightFormulaResult with
                          ⟨rightFormula, afterRightFormula⟩
                        have hrightFormulaSuffix :=
                          decodeCompactFormulaTrace_suffix_le
                            hrightFormulaTrace
                        have hrightFormula :=
                          decodeCompactFormulaTrace_parserCostBound
                            0 fuel afterLeftFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hrightFormulaTrace] at hrightFormula
                        cases hpremiseTrace :
                            (decodeCompactListedProofTrace fuel
                              afterRightFormula).1 with
                        | none =>
                            have hpremise := ih afterRightFormula
                            simp [parserCostBound, parserCostBoundWith,
                              hpremiseTrace] at hpremise
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some premiseResult =>
                            rcases premiseResult with ⟨premise, suffix⟩
                            have hpremiseSuffix :=
                              decodeCompactListedProofTrace_suffix_le
                                hpremiseTrace
                            have hpremise := ih afterRightFormula
                            simp [parserCostBound, parserCostBoundWith,
                              hpremiseTrace] at hpremise
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
              · cases hformulaTrace :
                    (decodeCompactFormulaTrace 1 fuel afterSequent).1 with
                | none =>
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        1 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    have hformulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hformulaTrace
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        1 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    cases hpremiseTrace :
                        (decodeCompactListedProofTrace fuel afterFormula).1 with
                    | none =>
                        have hpremise := ih afterFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hpremiseTrace] at hpremise
                        simp_all
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some premiseResult =>
                        rcases premiseResult with ⟨premise, suffix⟩
                        have hpremiseSuffix :=
                          decodeCompactListedProofTrace_suffix_le
                            hpremiseTrace
                        have hpremise := ih afterFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hpremiseTrace] at hpremise
                        simp_all
                        unfold parserReserve primitiveReserve at *
                        omega
              · cases hformulaTrace :
                    (decodeCompactFormulaTrace 1 fuel afterSequent).1 with
                | none =>
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        1 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    have hformulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hformulaTrace
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        1 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    cases hwitnessTrace :
                        (decodeCompactTermTrace 0 fuel afterFormula).1 with
                    | none =>
                        have hwitness :=
                          decodeCompactTermTrace_parserCostBound
                            0 fuel afterFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hwitnessTrace] at hwitness
                        simp_all
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some witnessResult =>
                        rcases witnessResult with ⟨witness, afterWitness⟩
                        have hwitnessSuffix :=
                          decodeCompactTermTrace_suffix_le hwitnessTrace
                        have hwitness :=
                          decodeCompactTermTrace_parserCostBound
                            0 fuel afterFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hwitnessTrace] at hwitness
                        cases hpremiseTrace :
                            (decodeCompactListedProofTrace fuel
                              afterWitness).1 with
                        | none =>
                            have hpremise := ih afterWitness
                            simp [parserCostBound, parserCostBoundWith,
                              hpremiseTrace] at hpremise
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some premiseResult =>
                            rcases premiseResult with ⟨premise, suffix⟩
                            have hpremiseSuffix :=
                              decodeCompactListedProofTrace_suffix_le
                                hpremiseTrace
                            have hpremise := ih afterWitness
                            simp [parserCostBound, parserCostBoundWith,
                              hpremiseTrace] at hpremise
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
              · cases hpremiseTrace :
                    (decodeCompactListedProofTrace fuel afterSequent).1 with
                | none =>
                    have hpremise := ih afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hpremiseTrace] at hpremise
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some premiseResult =>
                    rcases premiseResult with ⟨premise, suffix⟩
                    have hpremiseSuffix :=
                      decodeCompactListedProofTrace_suffix_le hpremiseTrace
                    have hpremise := ih afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hpremiseTrace] at hpremise
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
              · cases hpremiseTrace :
                    (decodeCompactListedProofTrace fuel afterSequent).1 with
                | none =>
                    have hpremise := ih afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hpremiseTrace] at hpremise
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some premiseResult =>
                    rcases premiseResult with ⟨premise, suffix⟩
                    have hpremiseSuffix :=
                      decodeCompactListedProofTrace_suffix_le hpremiseTrace
                    have hpremise := ih afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hpremiseTrace] at hpremise
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
              · cases hformulaTrace :
                    (decodeCompactFormulaTrace 0 fuel afterSequent).1 with
                | none =>
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    simp_all
                    unfold parserReserve primitiveReserve at *
                    omega
                | some formulaResult =>
                    rcases formulaResult with ⟨formula, afterFormula⟩
                    have hformulaSuffix :=
                      decodeCompactFormulaTrace_suffix_le hformulaTrace
                    have hformula :=
                      decodeCompactFormulaTrace_parserCostBound
                        0 fuel afterSequent
                    simp [parserCostBound, parserCostBoundWith,
                      hformulaTrace] at hformula
                    cases hleftProofTrace :
                        (decodeCompactListedProofTrace fuel afterFormula).1 with
                    | none =>
                        have hleftProof := ih afterFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hleftProofTrace] at hleftProof
                        simp_all
                        unfold parserReserve primitiveReserve at *
                        omega
                    | some leftProofResult =>
                        rcases leftProofResult with
                          ⟨leftProof, afterLeftProof⟩
                        have hleftProofSuffix :=
                          decodeCompactListedProofTrace_suffix_le
                            hleftProofTrace
                        have hleftProof := ih afterFormula
                        simp [parserCostBound, parserCostBoundWith,
                          hleftProofTrace] at hleftProof
                        cases hrightProofTrace :
                            (decodeCompactListedProofTrace fuel
                              afterLeftProof).1 with
                        | none =>
                            have hrightProof := ih afterLeftProof
                            simp [parserCostBound, parserCostBoundWith,
                              hrightProofTrace] at hrightProof
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
                        | some rightProofResult =>
                            rcases rightProofResult with
                              ⟨rightProof, suffix⟩
                            have hrightProofSuffix :=
                              decodeCompactListedProofTrace_suffix_le
                                hrightProofTrace
                            have hrightProof := ih afterLeftProof
                            simp [parserCostBound, parserCostBoundWith,
                              hrightProofTrace] at hrightProof
                            simp_all
                            unfold parserReserve primitiveReserve at *
                            omega
              · simp [traceFailure]
                unfold parserReserve primitiveReserve at *
                omega

#print axioms decodeCompactSequentListTrace_parserCostBound
#print axioms decodeCompactListedProofTrace_parserCostBound

end FoundationCompactListedProofDecoderCostPotential
