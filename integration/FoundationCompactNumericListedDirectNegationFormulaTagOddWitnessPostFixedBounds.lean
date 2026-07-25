import integration.FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostSyntaxFixedBounds

/-! # Fixed checked conjunction resource for the odd tag witness -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 80000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNegationFormulaTagOddWitnessPostFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate
open FoundationCompactNumericListedDirectNegationFormulaTagAtomicFixedBounds
open FoundationCompactNumericListedDirectNegationFormulaTagWitnessPostFixedBounds

private abbrev tagZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNegationFormulaTagExplicitHybridCertificate.zeroValuation

theorem oddPostCertificate_structuralPayloadBound_le_fixed
    (tag mapped pair bitBound : Nat)
    (hpair : pair < 4)
    (htag : tag = 2 * pair + 1)
    (hmapped : tag = mapped + 1)
    (htagSize : Nat.size tag <= bitBound)
    (hmappedSize : Nat.size mapped <= bitBound) :
    let pairCertificate := pairLtFourCertificate pair hpair
    let equalityCertificate := oddTagEqualityCertificate tag pair htag
    let successorCertificate :=
      tagMappedSuccessorCertificate tag mapped hmapped
    let innerCertificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        equalityCertificate successorCertificate
    let postCertificate :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        pairCertificate innerCertificate
    hybridFormulaStructuralPayloadBound postCertificate <=
      negationFormulaTagWitnessPostFixedPayloadPolynomial bitBound := by
  dsimp only
  have hpairResource :=
    pairLtFourCertificate_structuralPayloadBound_le_fixed pair bitBound hpair
  have hequalityResource :=
    oddTagEqualityCertificate_structuralPayloadBound_le_fixed
      tag pair bitBound htag hpair htagSize
  have hsuccessorResource :=
    tagMappedSuccessorCertificate_structuralPayloadBound_le_fixed
      tag mapped bitBound hmapped htagSize hmappedSize
  have hinner := transparentHybridConjunctionPayloadBound_le
    (oddTagEqualityCertificate tag pair htag)
    (tagMappedSuccessorCertificate tag mapped hmapped) _ _
    hequalityResource hsuccessorResource
  have hpost := transparentHybridConjunctionPayloadBound_le
    (pairLtFourCertificate pair hpair)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (oddTagEqualityCertificate tag pair htag)
      (tagMappedSuccessorCertificate tag mapped hmapped))
    _ _ hpairResource hinner
  have hgeneral :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      tagZeroValuation
      “!!(shortBinaryNumeralTerm pair) < 4”
      “!!(shortBinaryNumeralTerm tag) =
        2 * !!(shortBinaryNumeralTerm pair) + 1”
      “!!(shortBinaryNumeralTerm tag) =
        !!(shortBinaryNumeralTerm mapped) + 1”
      (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)
      (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)
      (negationFormulaTagAtomicFixedPayloadPolynomial bitBound)
      (negationFormulaTagWitnessPostSyntaxPolynomial bitBound)
      (by
        unfold negationFormulaTagWitnessPostSyntaxPolynomial
        omega)
      (oddPostFormula_closed tag mapped pair)
      (oddPostFormula_code_le tag mapped pair bitBound hpair htagSize
        hmappedSize)
  exact hpost.trans hgeneral

#print axioms oddPostCertificate_structuralPayloadBound_le_fixed

end FoundationCompactNumericListedDirectNegationFormulaTagOddWitnessPostFixedBounds
