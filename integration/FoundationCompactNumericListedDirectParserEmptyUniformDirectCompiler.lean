import integration.FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
import integration.FoundationCompactPADirectNineConjunctionCompiler

/-!
# Uniform direct compiler for the empty parser branch

The original nine formulas are retained.  Eight leaves use their checked
hybrid certificates; the structured-list-layout leaf uses the uniform direct
compiler, avoiding the obsolete finite sum over every possible witness.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserEmptyUniformDirectCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPADirectNineConjunctionCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler

private abbrev emptyDirectZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.zeroValuation

noncomputable def compileCompactUnifiedParserEmptyUniformDirectContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentTokensCount : current.tokensCount <= numericBound)
    (houtputBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserEmptyExplicitFormula tokenTable width tokenCount
          current next witness).freeVariables emptyDirectZeroValuation)
      (compactUnifiedParserEmptyExplicitFormula tokenTable width tokenCount
        current next witness) := by
  rcases hgraph with
    ⟨hcurrentCount, hnextCount, hrunning, htokenRows, hcompleted⟩
  rcases hcompleted with
    ⟨⟨hprefix, hlayout, houtputRows⟩, hsize, harea⟩
  let layoutData :=
    compactAdditiveStructuredListLayoutDataOfLayout tokenTable width tokenCount
      witness.targetOutputStart current.tokensCount next.finish
      witness.targetOutputBoundary hlayout
  let currentCountCertificate :=
    closedEqZeroCertificate current.tasksCount hcurrentCount
  let nextCountCertificate :=
    closedEqZeroCertificate next.tasksCount hnextCount
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hrunning
  let tokenRowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      next.tokensBoundary next.tokensCount htokenRows
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount next.tasksFinish witness.targetOutputStart
      hprefix
  let layoutProof :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount witness.targetOutputStart
      current.tokensCount next.finish witness.targetOutputBoundary
      layoutData.bodyStart numericBound bitBound layoutData.bodyStart_le_tokenCount
      layoutData.header layoutData.boundaryFinish_le_tokenCount
      layoutData.boundaryStartEntry layoutData.boundaryFinishEntry
      layoutData.rows htokenCount hcurrentTokensCount houtputBoundarySize
      hnumericSize
  let layoutFormula :=
    compactAdditiveStructuredListLayoutClosedFormula tokenTable width tokenCount
      witness.targetOutputStart current.tokensCount next.finish
      witness.targetOutputBoundary
  have hlayoutContext :
      (∅ : Finset ValuationFormula) =
        valuationContext layoutFormula.freeVariables emptyDirectZeroValuation := by
    rw [show layoutFormula.freeVariables = ∅ by
      simpa only [layoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount witness.targetOutputStart
          current.tokensCount next.finish witness.targetOutputBoundary]
    simp [valuationContext]
  let layoutAtValuation :=
    CertifiedPAContextProof.castContext hlayoutContext layoutProof
  let outputRowsCertificate :=
    compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount current.tokensBoundary current.tokensCount
      witness.targetOutputBoundary current.tokensCount houtputRows
  let sizeCertificate :=
    compactNatSizeExplicitHybridCertificateOfEq
      witness.targetOutputBoundarySize witness.targetOutputBoundary hsize
  let areaCertificate :=
    outputBoundaryAreaCertificate tokenCount current.tokensCount
      witness.targetOutputBoundarySize harea
  let parts :=
    compileDirectNineConjunction currentCountCertificate.compile
      nextCountCertificate.compile runningCertificate.compile
      tokenRowsCertificate.compile prefixCertificate.compile
      layoutAtValuation outputRowsCertificate.compile sizeCertificate.compile
      areaCertificate.compile
  exact parts

end FoundationCompactNumericListedDirectParserEmptyUniformDirectCompiler
