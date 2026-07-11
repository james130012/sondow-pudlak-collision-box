import integration.FoundationCompactNumericListedPublicVerifier
import integration.FoundationCompactNumericListedRootFieldsDirectTrace

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
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedRootFieldsDirectTrace
open FoundationCompactNumericListedPublicVerifier

local instance compactNumericRootFieldBranchDirectTracePrimcodable :
    Primcodable CompactNumericRootFieldBranchDirectTrace :=
  inferInstance

abbrev CompactNumericCertifiedPartsRootData :=
  (List Nat × CompactNumericCertifiedParts) × CompactNumericProofRoot

local instance compactNumericCertifiedPartsRootDataPrimcodable :
    Primcodable CompactNumericCertifiedPartsRootData :=
  inferInstance

/-- The residual data relation after the proof and certificate parser results
have been exposed separately. -/
def CompactNumericCertifiedPartsResidualValid
    (tokens : List Nat) (parts : CompactNumericCertifiedParts)
    (root : CompactNumericProofRoot)
    (rootTrace : CompactNumericRootFieldBranchDirectTrace) : Prop :=
  parts.1 = consumedTokenPrefix tokens parts.2.1 ∧
    CompactNumericProofRootDirectTraceValid parts.1 root rootTrace ∧
    parts.2.2 = root.2.1

theorem compactNumericCertifiedPartsResidualValid_primrec :
    PrimrecPred (fun input :
        ((List Nat × CompactNumericCertifiedParts) × CompactNumericProofRoot) ×
          CompactNumericRootFieldBranchDirectTrace =>
      CompactNumericCertifiedPartsResidualValid
        input.1.1.1 input.1.1.2 input.1.2 input.2) := by
  let Input :=
    CompactNumericCertifiedPartsRootData ×
      CompactNumericRootFieldBranchDirectTrace
  have htokens : Primrec (fun input : Input => input.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hparts : Primrec (fun input : Input => input.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hroot : Primrec (fun input : Input => input.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hrootTrace : Primrec (fun input : Input => input.2) :=
    Primrec.snd
  have hproofTokens : Primrec (fun input : Input => input.1.1.2.1) :=
    Primrec.fst.comp hparts
  have hcertificateTokens : Primrec (fun input : Input =>
      input.1.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hparts)
  have hconclusion : Primrec (fun input : Input => input.1.1.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hparts)
  have hconsumed : Primrec (fun input : Input =>
      consumedTokenPrefix input.1.1.1 input.1.1.2.2.1) :=
    consumedTokenPrefix_primrec.comp htokens hcertificateTokens
  have hprefix : PrimrecPred (fun input : Input =>
      input.1.1.2.1 =
        consumedTokenPrefix input.1.1.1 input.1.1.2.2.1) :=
    Primrec.eq.comp hproofTokens hconsumed
  have hrootBranch : PrimrecPred (fun input : Input =>
      CompactNumericProofRootDirectTraceValid
        input.1.1.2.1 input.1.2 input.2) :=
    compactNumericProofRootDirectTraceValid_primrec.comp <|
      Primrec.pair (Primrec.pair hproofTokens hroot) hrootTrace
  have hrootConclusion : Primrec (fun input : Input => input.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hroot)
  have hconclusionEq : PrimrecPred (fun input : Input =>
      input.1.1.2.2.2 = input.1.2.2.1) :=
    Primrec.eq.comp hconclusion hrootConclusion
  exact
    (hprefix.and (hrootBranch.and hconclusionEq)).of_eq fun input => by
      simp only [CompactNumericCertifiedPartsResidualValid]

theorem compactNumericCertifiedPartsParser_eq_some_iff_exists_root
    (tokens : List Nat) (parts : CompactNumericCertifiedParts) :
    compactNumericCertifiedPartsParser tokens = some parts ↔
      ∃ root : CompactNumericProofRoot,
        ∃ rootTrace : CompactNumericRootFieldBranchDirectTrace,
        compactProofTokenParser tokens = some parts.2.1 ∧
          compactStructuralCertificateTokenParser parts.2.1 = some [] ∧
          CompactNumericCertifiedPartsResidualValid
            tokens parts root rootTrace := by
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
              obtain ⟨rootTrace, hrootTrace⟩ :=
                (compactListedProofNodeFieldsParser_eq_some_iff_exists_directTrace
                  (consumedTokenPrefix tokens certificateTokens) root).mp hroot
              exact ⟨root, rootTrace, rfl, hcertificate,
                rfl, hrootTrace, rfl⟩
        · simp [compactNumericCertifiedPartsAfter,
            hcertificate] at hparts
  · rintro ⟨root, rootTrace, hproof, hcertificate,
      hprefix, hrootTraceValid, hconclusion⟩
    have hroot :=
      (compactListedProofNodeFieldsParser_eq_some_iff_exists_directTrace
        parts.1 root).mpr ⟨rootTrace, hrootTraceValid⟩
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
