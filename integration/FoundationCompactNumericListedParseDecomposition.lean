import integration.FoundationCompactNumericListedPublicVerifier

/-!
# Exact decomposition of compact numeric parse results

This module removes the two result-packaging functions from the direct trace
boundary.  Successful certified-part parsing is decomposed into the real proof
parser result, the real certificate parser result, an exact consumed prefix,
and one explicit root-node result.  Successful whole-formula value parsing is
decomposed into the real formula-parser result and token equality.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedParseDecomposition

open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedPublicVerifier

abbrev CompactNumericProofRoot := Nat × CompactNumericNodeFields

/-- The residual data relation after the proof and certificate parser results
have been exposed separately. -/
def CompactNumericCertifiedPartsResidualValid
    (tokens : List Nat) (parts : CompactNumericCertifiedParts)
    (root : CompactNumericProofRoot) : Prop :=
  parts.1 = consumedTokenPrefix tokens parts.2.1 ∧
    compactListedProofNodeFieldsParser parts.1 = some root ∧
    parts.2.2 = root.2.1

theorem compactNumericCertifiedPartsResidualValid_primrec :
    PrimrecPred (fun input :
        (List Nat × CompactNumericCertifiedParts) × CompactNumericProofRoot =>
      CompactNumericCertifiedPartsResidualValid
        input.1.1 input.1.2 input.2) := by
  let Input :=
    (List Nat × CompactNumericCertifiedParts) × CompactNumericProofRoot
  have htokens : Primrec (fun input : Input => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hparts : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hroot : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hproofTokens : Primrec (fun input : Input => input.1.2.1) :=
    Primrec.fst.comp hparts
  have hcertificateTokens : Primrec (fun input : Input => input.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hparts)
  have hconclusion : Primrec (fun input : Input => input.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hparts)
  have hconsumed : Primrec (fun input : Input =>
      consumedTokenPrefix input.1.1 input.1.2.2.1) :=
    consumedTokenPrefix_primrec.comp htokens hcertificateTokens
  have hprefix : PrimrecPred (fun input : Input =>
      input.1.2.1 = consumedTokenPrefix input.1.1 input.1.2.2.1) :=
    Primrec.eq.comp hproofTokens hconsumed
  have hrootParse : PrimrecPred (fun input : Input =>
      compactListedProofNodeFieldsParser input.1.2.1 = some input.2) :=
    Primrec.eq.comp
      (compactListedProofNodeFieldsParser_primrec.comp hproofTokens)
      (Primrec.option_some.comp hroot)
  have hrootConclusion : Primrec (fun input : Input => input.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hroot)
  have hconclusionEq : PrimrecPred (fun input : Input =>
      input.1.2.2.2 = input.2.2.1) :=
    Primrec.eq.comp hconclusion hrootConclusion
  exact
    (hprefix.and (hrootParse.and hconclusionEq)).of_eq fun input => by
      simp only [CompactNumericCertifiedPartsResidualValid]

theorem compactNumericCertifiedPartsParser_eq_some_iff_exists_root
    (tokens : List Nat) (parts : CompactNumericCertifiedParts) :
    compactNumericCertifiedPartsParser tokens = some parts ↔
      ∃ root : CompactNumericProofRoot,
        compactProofTokenParser tokens = some parts.2.1 ∧
          compactStructuralCertificateTokenParser parts.2.1 = some [] ∧
          CompactNumericCertifiedPartsResidualValid tokens parts root := by
  constructor
  · intro hparts
    unfold compactNumericCertifiedPartsParser at hparts
    cases hproof : compactProofTokenParser tokens with
    | none =>
        simp [hproof] at hparts
    | some certificateTokens =>
        simp only [hproof] at hparts
        by_cases hcertificate :
            compactStructuralCertificateTokenParser certificateTokens =
              some []
        · cases hroot : compactListedProofNodeFieldsParser
              (consumedTokenPrefix tokens certificateTokens) with
          | none =>
              simp [compactNumericCertifiedPartsAfter,
                hcertificate, hroot] at hparts
          | some root =>
              have heq :
                  (consumedTokenPrefix tokens certificateTokens,
                    (certificateTokens, root.2.1)) = parts := by
                simpa [compactNumericCertifiedPartsAfter,
                  hcertificate, hroot] using hparts
              subst parts
              exact ⟨root, rfl, hcertificate, rfl, hroot, rfl⟩
        · simp [compactNumericCertifiedPartsAfter,
            hcertificate] at hparts
  · rintro ⟨root, hproof, hcertificate,
      hprefix, hroot, hconclusion⟩
    unfold compactNumericCertifiedPartsParser
    rw [hproof]
    change compactNumericCertifiedPartsAfter tokens parts.2.1 = some parts
    unfold compactNumericCertifiedPartsAfter
    rw [if_pos hcertificate]
    rw [← hprefix]
    dsimp only
    rw [hroot]
    simp only [Option.map_some]
    rw [← hconclusion]

/-- Once the real formula parser has consumed the whole stream, the recorded
formula value is exactly that stream. -/
def CompactNumericWholeFormulaResidualValid
    (tokens value : List Nat) : Prop :=
  value = tokens

theorem compactNumericWholeFormulaResidualValid_primrec :
    PrimrecPred (fun input : List Nat × List Nat =>
      CompactNumericWholeFormulaResidualValid input.1 input.2) := by
  exact Primrec.eq.comp Primrec.snd Primrec.fst

theorem compactNumericWholeFormulaValue_eq_some_iff
    (tokens value : List Nat) :
    compactNumericWholeFormulaValue tokens = some value ↔
      compactFormulaTokenParser 0 tokens = some [] ∧
        CompactNumericWholeFormulaResidualValid tokens value := by
  constructor
  · intro hvalue
    cases hparser : compactFormulaTokenParser 0 tokens with
    | none =>
        simp [compactNumericWholeFormulaValue,
          compactFormulaTokenValueParser, hparser] at hvalue
    | some suffix =>
        cases suffix with
        | nil =>
            have htokens : tokens = value := by
              simpa [compactNumericWholeFormulaValue,
                compactFormulaTokenValueParser, hparser,
                consumedTokenPrefix] using hvalue
            exact ⟨rfl, htokens.symm⟩
        | cons head tail =>
            simp [compactNumericWholeFormulaValue,
              compactFormulaTokenValueParser, hparser] at hvalue
  · rintro ⟨hparser, hvalue⟩
    unfold CompactNumericWholeFormulaResidualValid at hvalue
    subst value
    simp [compactNumericWholeFormulaValue,
      compactFormulaTokenValueParser, hparser, consumedTokenPrefix]

#print axioms compactNumericCertifiedPartsResidualValid_primrec
#print axioms compactNumericCertifiedPartsParser_eq_some_iff_exists_root
#print axioms compactNumericWholeFormulaResidualValid_primrec
#print axioms compactNumericWholeFormulaValue_eq_some_iff

end FoundationCompactNumericListedParseDecomposition
