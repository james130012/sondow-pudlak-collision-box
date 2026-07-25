import integration.FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
import integration.FoundationCompactPADirectNineConjunctionCompiler

/-!
# Uniform direct compiler for the completed parser branch

The completed-status alternative is assembled from its original nine checked
formulas.  Both structured-list layouts use the uniform direct compiler, so
the resulting proof does not depend on the obsolete witness-indexed layout
sum.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPADirectNineConjunctionCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

private abbrev doneDirectZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

noncomputable def compileCompactBinaryNatCompletedStatusSameRowsUniformDirect
    (tokenTable width tokenCount
      sourceStatusStart sourceStatusFinish
      targetStatusStart targetStatusFinish
      sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
      targetOutputStart targetOutputBoundary targetOutputBoundarySize
      outputCount numericBound bitBound : Nat)
    (hgraph : CompactBinaryNatCompletedStatusSameRowsWithSize
      tokenTable width tokenCount
        sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish
        sourceOutputStart sourceOutputBoundary sourceOutputBoundarySize
        targetOutputStart targetOutputBoundary targetOutputBoundarySize
        outputCount)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (hsourceBoundarySize : Nat.size sourceOutputBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
          tokenTable width tokenCount sourceStatusStart sourceStatusFinish
          targetStatusStart targetStatusFinish sourceOutputStart
          sourceOutputBoundary sourceOutputBoundarySize targetOutputStart
          targetOutputBoundary targetOutputBoundarySize outputCount).freeVariables
        doneDirectZeroValuation)
      (compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
        tokenTable width tokenCount sourceStatusStart sourceStatusFinish
        targetStatusStart targetStatusFinish sourceOutputStart
        sourceOutputBoundary sourceOutputBoundarySize targetOutputStart
        targetOutputBoundary targetOutputBoundarySize outputCount) := by
  rcases hgraph with
    ⟨⟨hsourcePrefix, hsourceLayout, htargetPrefix, htargetLayout, hsame⟩,
      hsourceSize, hsourceArea, htargetSize, htargetArea⟩
  let sourceLayoutData :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      sourceOutputStart outputCount sourceStatusFinish sourceOutputBoundary
      hsourceLayout
  let targetLayoutData :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      targetOutputStart outputCount targetStatusFinish targetOutputBoundary
      htargetLayout
  let sourcePrefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceStatusStart sourceOutputStart
      hsourcePrefix
  let sourceLayoutFormula :=
    compactAdditiveStructuredListLayoutClosedFormula tokenTable width tokenCount
      sourceOutputStart outputCount sourceStatusFinish sourceOutputBoundary
  let sourceLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount sourceOutputStart outputCount
      sourceStatusFinish sourceOutputBoundary sourceLayoutData.bodyStart
      numericBound bitBound sourceLayoutData.bodyStart_le_tokenCount
      sourceLayoutData.header sourceLayoutData.boundaryFinish_le_tokenCount
      sourceLayoutData.boundaryStartEntry sourceLayoutData.boundaryFinishEntry
      sourceLayoutData.rows htokenCount houtputCount hsourceBoundarySize
      hnumericSize
  have hsourceLayoutContext :
      (∅ : Finset ValuationFormula) =
        valuationContext sourceLayoutFormula.freeVariables
          doneDirectZeroValuation := by
    rw [show sourceLayoutFormula.freeVariables = ∅ by
      simpa only [sourceLayoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount sourceOutputStart outputCount
          sourceStatusFinish sourceOutputBoundary]
    simp [valuationContext]
  let sourceLayoutProof :=
    CertifiedPAContextProof.castContext hsourceLayoutContext sourceLayoutRaw
  let targetPrefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetStatusStart targetOutputStart
      htargetPrefix
  let targetLayoutFormula :=
    compactAdditiveStructuredListLayoutClosedFormula tokenTable width tokenCount
      targetOutputStart outputCount targetStatusFinish targetOutputBoundary
  let targetLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount targetOutputStart outputCount
      targetStatusFinish targetOutputBoundary targetLayoutData.bodyStart
      numericBound bitBound targetLayoutData.bodyStart_le_tokenCount
      targetLayoutData.header targetLayoutData.boundaryFinish_le_tokenCount
      targetLayoutData.boundaryStartEntry targetLayoutData.boundaryFinishEntry
      targetLayoutData.rows htokenCount houtputCount htargetBoundarySize
      hnumericSize
  have htargetLayoutContext :
      (∅ : Finset ValuationFormula) =
        valuationContext targetLayoutFormula.freeVariables
          doneDirectZeroValuation := by
    rw [show targetLayoutFormula.freeVariables = ∅ by
      simpa only [targetLayoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount targetOutputStart outputCount
          targetStatusFinish targetOutputBoundary]
    simp [valuationContext]
  let targetLayoutProof :=
    CertifiedPAContextProof.castContext htargetLayoutContext targetLayoutRaw
  let sameRowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount sourceOutputBoundary outputCount targetOutputBoundary
      outputCount hsame
  let sourceSizeCertificate :=
    compactNatSizeExplicitHybridCertificateOfEq sourceOutputBoundarySize
      sourceOutputBoundary hsourceSize
  let sourceAreaCertificate :=
    boundaryAreaCertificate tokenCount outputCount sourceOutputBoundarySize
      hsourceArea
  let targetSizeCertificate :=
    compactNatSizeExplicitHybridCertificateOfEq targetOutputBoundarySize
      targetOutputBoundary htargetSize
  let targetAreaCertificate :=
    boundaryAreaCertificate tokenCount outputCount targetOutputBoundarySize
      htargetArea
  exact compileDirectNineConjunction sourcePrefixCertificate.compile
    sourceLayoutProof targetPrefixCertificate.compile targetLayoutProof
    sameRowsCertificate.compile sourceSizeCertificate.compile
    sourceAreaCertificate.compile targetSizeCertificate.compile
    targetAreaCertificate.compile

end FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler
