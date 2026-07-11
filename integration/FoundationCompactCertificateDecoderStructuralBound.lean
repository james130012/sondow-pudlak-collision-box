import integration.FoundationCompactProofDecoderStructuralBound

/-!
# Structural bounds for compact PA certificates
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactCertificateDecoderStructuralBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCertifiedPAProof
open FoundationCompactVerifierStructuralBound
open FoundationCompactProofDecoderStructuralBound

theorem decodePAAxiomCertificate_parseWeight_le :
    forall {fuel bits suffix certificate},
      decodePAAxiomCertificate fuel bits = some (certificate, suffix) ->
      axiomCertificateParseWeight certificate + suffix.length <=
        bits.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits suffix certificate hdecode
      simp [decodePAAxiomCertificate] at hdecode
  | succ fuel ih =>
      intro bits suffix certificate hdecode
      cases htag : decodeBinaryNat bits with
      | none => simp [decodePAAxiomCertificate, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_consumes_two htag
          simp only [decodePAAxiomCertificate] at hdecode
          rw [htag] at hdecode
          dsimp only [Bind.bind, Option.bind] at hdecode
          split at hdecode
          all_goals try
            rcases hdecode with ⟨rfl, rfl⟩
            simp [axiomCertificateParseWeight]
            omega
          case h_4 =>
            cases harity : decodeBinaryNat afterTag with
            | none => simp [harity] at hdecode
            | some arityResult =>
                rcases arityResult with ⟨arity, afterArity⟩
                cases hcode : decodeBinaryNat afterArity with
                | none => simp [harity, hcode] at hdecode
                | some codeResult =>
                    rcases codeResult with ⟨code, afterCode⟩
                    cases hsymbol :
                        (Encodable.decode₂ _ code :
                          Option (LO.FirstOrder.Language.Func ℒₒᵣ arity)) with
                    | none => simp [harity, hcode, hsymbol] at hdecode
                    | some symbol =>
                        simp [harity, hcode, hsymbol] at hdecode
                        rcases hdecode with ⟨rfl, rfl⟩
                        have harityLength :=
                          decodeBinaryNat_consumes_two harity
                        have hcodeLength :=
                          decodeBinaryNat_consumes_two hcode
                        simp [axiomCertificateParseWeight]
                        omega
          case h_5 =>
            cases harity : decodeBinaryNat afterTag with
            | none => simp [harity] at hdecode
            | some arityResult =>
                rcases arityResult with ⟨arity, afterArity⟩
                cases hcode : decodeBinaryNat afterArity with
                | none => simp [harity, hcode] at hdecode
                | some codeResult =>
                    rcases codeResult with ⟨code, afterCode⟩
                    cases hsymbol :
                        (Encodable.decode₂ _ code :
                          Option (LO.FirstOrder.Language.Rel ℒₒᵣ arity)) with
                    | none => simp [harity, hcode, hsymbol] at hdecode
                    | some symbol =>
                        simp [harity, hcode, hsymbol] at hdecode
                        rcases hdecode with ⟨rfl, rfl⟩
                        have harityLength :=
                          decodeBinaryNat_consumes_two harity
                        have hcodeLength :=
                          decodeBinaryNat_consumes_two hcode
                        simp [axiomCertificateParseWeight]
                        omega
          case h_23 =>
            cases hformula : decodeCompactFormula 1 fuel afterTag with
            | none => simp [hformula] at hdecode
            | some formulaResult =>
                rcases formulaResult with ⟨body, afterFormula⟩
                simp [hformula] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                have hformulaLength :=
                  decodeCompactFormula_symbolCount_le hformula
                simp [axiomCertificateParseWeight]
                omega
          case h_24 => simp at hdecode

theorem decodeStructuralValidityCertificate_parseWeight_le :
    forall {fuel bits suffix certificate},
      decodeStructuralValidityCertificate fuel bits =
        some (certificate, suffix) ->
      structuralCertificateParseWeight certificate + suffix.length <=
        bits.length := by
  intro fuel
  induction fuel with
  | zero =>
      intro bits suffix certificate hdecode
      simp [decodeStructuralValidityCertificate] at hdecode
  | succ fuel ih =>
      intro bits suffix certificate hdecode
      cases htag : decodeBinaryNat bits with
      | none =>
          simp [decodeStructuralValidityCertificate, htag] at hdecode
      | some tagResult =>
          rcases tagResult with ⟨tag, afterTag⟩
          have htagLength := decodeBinaryNat_consumes_two htag
          cases tag with
          | zero =>
              simp [decodeStructuralValidityCertificate, htag] at hdecode
              rcases hdecode with ⟨rfl, rfl⟩
              simp [structuralCertificateParseWeight]
              omega
          | succ tag =>
              cases tag with
              | zero =>
                  cases haxiom : decodePAAxiomCertificate fuel afterTag with
                  | none =>
                      simp [decodeStructuralValidityCertificate, htag,
                        haxiom] at hdecode
                  | some axiomResult =>
                      rcases axiomResult with ⟨axiomCertificate, afterAxiom⟩
                      simp [decodeStructuralValidityCertificate, htag,
                        haxiom] at hdecode
                      rcases hdecode with ⟨rfl, rfl⟩
                      have haxiomLength :=
                        decodePAAxiomCertificate_parseWeight_le haxiom
                      simp [structuralCertificateParseWeight]
                      omega
              | succ tag =>
                  cases tag with
                  | zero =>
                      cases hpremise :
                          decodeStructuralValidityCertificate fuel afterTag with
                      | none =>
                          simp [decodeStructuralValidityCertificate, htag,
                            hpremise] at hdecode
                      | some premiseResult =>
                          rcases premiseResult with ⟨premise, afterPremise⟩
                          simp [decodeStructuralValidityCertificate, htag,
                            hpremise] at hdecode
                          rcases hdecode with ⟨rfl, rfl⟩
                          have hpremiseLength := ih hpremise
                          simp [structuralCertificateParseWeight]
                          omega
                  | succ tag =>
                      cases tag with
                      | zero =>
                          cases hleft :
                              decodeStructuralValidityCertificate fuel
                                afterTag with
                          | none =>
                              simp [decodeStructuralValidityCertificate, htag,
                                hleft] at hdecode
                          | some leftResult =>
                              rcases leftResult with ⟨left, afterLeft⟩
                              cases hright :
                                  decodeStructuralValidityCertificate fuel
                                    afterLeft with
                              | none =>
                                  simp [decodeStructuralValidityCertificate,
                                    htag, hleft, hright] at hdecode
                              | some rightResult =>
                                  rcases rightResult with ⟨right, afterRight⟩
                                  simp [decodeStructuralValidityCertificate,
                                    htag, hleft, hright] at hdecode
                                  rcases hdecode with ⟨rfl, rfl⟩
                                  have hleftLength := ih hleft
                                  have hrightLength := ih hright
                                  simp [structuralCertificateParseWeight]
                                  omega
                      | succ tag =>
                          simp [decodeStructuralValidityCertificate, htag]
                            at hdecode

theorem decodeCompactCertifiedPAProof_parseWeight_le
    {fuel : Nat} {bits suffix : List Bool}
    {tree : CheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactCertifiedPAProof fuel bits =
      some ((tree, certificate), suffix)) :
    tree.parseWeight + structuralCertificateParseWeight certificate +
        suffix.length <= bits.length := by
  cases hproof : decodeCompactProof fuel bits with
  | none => simp [decodeCompactCertifiedPAProof, hproof] at hdecode
  | some proofResult =>
      rcases proofResult with ⟨decodedTree, afterProof⟩
      cases hcertificate :
          decodeStructuralValidityCertificate fuel afterProof with
      | none =>
          simp [decodeCompactCertifiedPAProof, hproof, hcertificate] at hdecode
      | some certificateResult =>
          rcases certificateResult with
            ⟨decodedCertificate, afterCertificate⟩
          simp [decodeCompactCertifiedPAProof, hproof, hcertificate] at hdecode
          rcases hdecode with ⟨⟨rfl, rfl⟩, rfl⟩
          have hproofLength := decodeCompactProof_parseWeight_le hproof
          have hcertificateLength :=
            decodeStructuralValidityCertificate_parseWeight_le hcertificate
          omega

theorem decodeCompactPackedCertifiedPAProof_parseWeight_le
    {code : Nat} {tree : CheckedPAProofTree}
    {certificate : StructuralValidityCertificate}
    (hdecode : decodeCompactPackedCertifiedPAProof code =
      some (tree, certificate)) :
    tree.parseWeight + structuralCertificateParseWeight certificate <=
      packedPayloadLength code := by
  simp only [decodeCompactPackedCertifiedPAProof] at hdecode
  cases hlast : code.bits.getLast? with
  | none =>
      simp [hlast] at hdecode
  | some lastBit =>
      cases lastBit with
      | false =>
          simp [hlast] at hdecode
      | true =>
          cases hproof :
              decodeCompactCertifiedPAProof
                (code.bits.length - 1 + 1) code.bits.dropLast with
          | none =>
              simp [hproof] at hdecode
          | some proofResult =>
              rcases proofResult with ⟨decodedProof, suffix⟩
              cases suffix with
              | cons head tail =>
                  simp [hproof, hlast] at hdecode
              | nil =>
                  rcases decodedProof with
                    ⟨decodedTree, decodedCertificate⟩
                  simp [hproof, hlast] at hdecode
                  rcases hdecode with ⟨rfl, rfl⟩
                  have hweight :=
                    decodeCompactCertifiedPAProof_parseWeight_le hproof
                  have hpayloadLength :
                      code.bits.dropLast.length =
                        packedPayloadLength code := by
                    simp [packedPayloadLength, Nat.size_eq_bits_len]
                  simpa [hpayloadLength] using hweight

theorem compactCertifiedPAProofVerifier_acceptance_bound
    {code formulaCode : Nat}
    (haccept : compactCertifiedPAProofVerifier code formulaCode = true) :
    exists (tree : CheckedPAProofTree)
        (certificate : StructuralValidityCertificate)
        (formula : LO.FirstOrder.ArithmeticProposition),
      decodeCompactPackedCertifiedPAProof code =
          some (tree, certificate) ∧
        certificateValid tree certificate ∧
        tree.conclusion = {formula} ∧
        compactFormulaCode formula = formulaCode ∧
        tree.parseWeight +
            structuralCertificateParseWeight certificate <=
          packedPayloadLength code ∧
        formulaSymbolCount formula <= packedPayloadLength formulaCode := by
  rcases checks_of_compactCertifiedPAProofVerifier_eq_true haccept with
    ⟨tree, certificate, formula, hdecode, hcertificate,
      hconclusion, hformulaCode⟩
  refine ⟨tree, certificate, formula, hdecode, hcertificate,
    hconclusion, hformulaCode, ?_, ?_⟩
  · exact decodeCompactPackedCertifiedPAProof_parseWeight_le hdecode
  · subst formulaCode
    have hformulaLength :=
      formulaSymbolCount_le_binaryFormulaCode_length formula
    simpa [packedPayloadLength] using hformulaLength

theorem compactCertifiedPAProofVerifier_total_structure_bound
    {code formulaCode : Nat}
    (haccept : compactCertifiedPAProofVerifier code formulaCode = true) :
    exists (tree : CheckedPAProofTree)
        (certificate : StructuralValidityCertificate)
        (formula : LO.FirstOrder.ArithmeticProposition),
      decodeCompactPackedCertifiedPAProof code =
          some (tree, certificate) ∧
        certificateValid tree certificate ∧
        tree.conclusion = {formula} ∧
        compactFormulaCode formula = formulaCode ∧
        tree.parseWeight +
            structuralCertificateParseWeight certificate +
            formulaSymbolCount formula <=
          packedPayloadLength code + packedPayloadLength formulaCode := by
  rcases compactCertifiedPAProofVerifier_acceptance_bound haccept with
    ⟨tree, certificate, formula, hdecode, hcertificate,
      hconclusion, hformulaCode, hproofBound, hformulaBound⟩
  refine ⟨tree, certificate, formula, hdecode, hcertificate,
    hconclusion, hformulaCode, ?_⟩
  omega

#print axioms decodeCompactProof_parseWeight_le
#print axioms decodeStructuralValidityCertificate_parseWeight_le
#print axioms compactCertifiedPAProofVerifier_total_structure_bound

end FoundationCompactCertificateDecoderStructuralBound
