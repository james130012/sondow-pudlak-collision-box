import integration.FoundationCompactProofCanonicalDecodeLengthComplete

/-!
# Canonical decode length for compact PA axiom certificates
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAAxiomCertificateCanonicalDecodeLength

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAProofVerifier
open FoundationCompactPAAxiomCertificate
open FoundationCompactCanonicalDecodeLength

theorem decodePAAxiomCertificate_binaryLength_le :
    forall {fuel bits suffix certificate},
      decodePAAxiomCertificate fuel bits = some (certificate, suffix) ->
      (binaryPAAxiomCertificateCode certificate).length + suffix.length <=
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
          have htagLength := decodeBinaryNat_canonical_length_le htag
          simp only [decodePAAxiomCertificate] at hdecode
          rw [htag] at hdecode
          dsimp only [Bind.bind, Option.bind] at hdecode
          split at hdecode
          all_goals try
            rcases hdecode with ⟨rfl, rfl⟩
            simp [binaryPAAxiomCertificateCode]
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
                          decodeBinaryNat_canonical_length_le harity
                        have hcodeLength :=
                          decodeBinaryNat_canonical_length_le hcode
                        have hencode : Encodable.encode symbol = code :=
                          Encodable.decode₂_eq_some.mp hsymbol
                        change (binaryNatCode 3).length +
                            afterTag.length <= bits.length at htagLength
                        simp only [binaryPAAxiomCertificateCode,
                          List.length_append]
                        rw [hencode]
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
                          decodeBinaryNat_canonical_length_le harity
                        have hcodeLength :=
                          decodeBinaryNat_canonical_length_le hcode
                        have hencode : Encodable.encode symbol = code :=
                          Encodable.decode₂_eq_some.mp hsymbol
                        change (binaryNatCode 4).length +
                            afterTag.length <= bits.length at htagLength
                        simp only [binaryPAAxiomCertificateCode,
                          List.length_append]
                        rw [hencode]
                        omega
          case h_23 =>
            cases hformula : decodeCompactFormula 1 fuel afterTag with
            | none => simp [hformula] at hdecode
            | some formulaResult =>
                rcases formulaResult with ⟨body, afterFormula⟩
                simp [hformula] at hdecode
                rcases hdecode with ⟨rfl, rfl⟩
                have hformulaLength :=
                  decodeCompactFormula_canonical_length_le hformula
                change (binaryNatCode 22).length +
                    afterTag.length <= bits.length at htagLength
                simp only [binaryPAAxiomCertificateCode,
                  List.length_append]
                omega
          case h_24 => simp at hdecode

#print axioms decodePAAxiomCertificate_binaryLength_le

end FoundationCompactPAAxiomCertificateCanonicalDecodeLength
