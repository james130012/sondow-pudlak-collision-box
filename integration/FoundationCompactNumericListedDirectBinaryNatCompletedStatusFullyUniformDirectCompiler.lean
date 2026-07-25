import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler

/-!
# Fully uniform direct compiler for the completed binary-Nat status branch

This five-leaf assembly replaces the structured-list layout leaf by its
uniform direct compiler.  The prefix, unit-boundary, Nat-size and area leaves
remain independently checked and are joined only by direct PA conjunctions.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedPublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

local notation "completedZeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

def compactBinaryNatCompletedStatusFullyUniformDirectPayloadEnvelope
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount bodyStart numericBound bitBound : Nat) :
    Nat :=
  let prefixFormula := compactBinaryNatCompletedStatusPrefixClosedFormula
    tokenTable width tokenCount start outputStart
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula tokenCount
    outputCount outputBoundary
  let sizeFormula := compactNatSizeClosedFormula outputBoundarySize
    outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let prefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope tokenTable
      width tokenCount outputStart outputCount finish outputBoundary bodyStart
      numericBound bitBound
  let unitResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
      outputCount outputBoundary numericBound bitBound
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    outputBoundarySize outputBoundary
  let areaResource := completedAreaStructuralPayloadPolynomial tokenCount
    outputCount outputBoundarySize
  let sizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sizeFormula areaFormula sizeResource areaResource
  let unitTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation unitFormula (sizeFormula ⋏ areaFormula)
    unitResource sizeAreaResource
  let layoutTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation layoutFormula
    (unitFormula ⋏ (sizeFormula ⋏ areaFormula)) layoutResource
    unitTailResource
  transparentHybridConjunctionPayloadEnvelope completedZeroValuation
    prefixFormula
    (layoutFormula ⋏ (unitFormula ⋏ (sizeFormula ⋏ areaFormula)))
    prefixResource layoutTailResource

noncomputable def compileCompactBinaryNatCompletedStatusFullyUniformDirect
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows tokenTable width
      tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf outputStart outputBoundary
          outputBoundarySize outputCount))
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (htableSize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width
          tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount).freeVariables
        completedZeroValuation)
      (compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width
        tokenCount start finish outputStart outputBoundary
        outputBoundarySize outputCount) := by
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1
  let layoutData := compactAdditiveStructuredListLayoutDataOfLayout tokenTable
    width tokenCount outputStart outputCount finish outputBoundary
    hcompleted.2.1
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let layoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      layoutData.bodyStart numericBound bitBound
      layoutData.bodyStart_le_tokenCount layoutData.header
      layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
      layoutData.boundaryFinishEntry layoutData.rows htokenCount houtputCount
      htableSize hnumericSize
  have hlayoutContext : (∅ : Finset ValuationFormula) =
      valuationContext layoutFormula.freeVariables completedZeroValuation := by
    rw [show layoutFormula.freeVariables = ∅ by
      simpa only [layoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount outputStart outputCount finish
          outputBoundary]
    simp [valuationContext]
  let layoutProof := CertifiedPAContextProof.castContext hlayoutContext
    layoutRaw
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula tokenCount
    outputCount outputBoundary
  let unitRaw :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount outputCount outputBoundary numericBound bitBound
      hcompleted.2.2.1 htokenCount houtputCount htableSize hnumericSize
  have hunitContext : (∅ : Finset ValuationFormula) =
      valuationContext unitFormula.freeVariables completedZeroValuation := by
    rw [show unitFormula.freeVariables = ∅ by
      exact compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount outputCount outputBoundary]
    simp [valuationContext]
  let unitProof := CertifiedPAContextProof.castContext hunitContext unitRaw
  let sizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    outputBoundarySize outputBoundary hcompleted.2.2.2.1
  let areaCertificate := completedAreaCertificate tokenCount outputCount
    outputBoundarySize hcompleted.2.2.2.2
  let sizeArea := compileDirectConjunction sizeCertificate.compile
    areaCertificate.compile
  let unitTail := compileDirectConjunction unitProof sizeArea
  let layoutTail := compileDirectConjunction layoutProof unitTail
  exact compileDirectConjunction prefixCertificate.compile layoutTail

theorem
    compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows tokenTable width
      tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf outputStart outputBoundary
          outputBoundarySize outputCount))
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (htableSize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactBinaryNatCompletedStatusFullyUniformDirect tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount numericBound bitBound hcompleted htokenCount houtputCount
      htableSize hnumericSize).payloadLength <=
      compactBinaryNatCompletedStatusFullyUniformDirectPayloadEnvelope
        tokenTable width tokenCount start finish outputStart outputBoundary
        outputBoundarySize outputCount
        (compactAdditiveStructuredListLayoutDataOfLayout tokenTable width
          tokenCount outputStart outputCount finish outputBoundary
          hcompleted.2.1).bodyStart numericBound bitBound := by
  let prefixFormula := compactBinaryNatCompletedStatusPrefixClosedFormula
    tokenTable width tokenCount start outputStart
  let layoutData := compactAdditiveStructuredListLayoutDataOfLayout tokenTable
    width tokenCount outputStart outputCount finish outputBoundary
    hcompleted.2.1
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula tokenCount
    outputCount outputBoundary
  let sizeFormula := compactNatSizeClosedFormula outputBoundarySize
    outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1
  let layoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      layoutData.bodyStart numericBound bitBound
      layoutData.bodyStart_le_tokenCount layoutData.header
      layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
      layoutData.boundaryFinishEntry layoutData.rows htokenCount houtputCount
      htableSize hnumericSize
  have hlayoutContext : (∅ : Finset ValuationFormula) =
      valuationContext layoutFormula.freeVariables completedZeroValuation := by
    rw [show layoutFormula.freeVariables = ∅ by
      simpa only [layoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount outputStart outputCount finish
          outputBoundary]
    simp [valuationContext]
  let layoutProof := CertifiedPAContextProof.castContext hlayoutContext
    layoutRaw
  let unitRaw :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount outputCount outputBoundary numericBound bitBound
      hcompleted.2.2.1 htokenCount houtputCount htableSize hnumericSize
  have hunitContext : (∅ : Finset ValuationFormula) =
      valuationContext unitFormula.freeVariables completedZeroValuation := by
    rw [show unitFormula.freeVariables = ∅ by
      exact compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount outputCount outputBoundary]
    simp [valuationContext]
  let unitProof := CertifiedPAContextProof.castContext hunitContext unitRaw
  let sizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    outputBoundarySize outputBoundary hcompleted.2.2.2.1
  let areaCertificate := completedAreaCertificate tokenCount outputCount
    outputBoundarySize hcompleted.2.2.2.2
  let prefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope tokenTable
      width tokenCount outputStart outputCount finish outputBoundary
      layoutData.bodyStart numericBound bitBound
  let unitResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
      outputCount outputBoundary numericBound bitBound
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    outputBoundarySize outputBoundary
  let areaResource := completedAreaStructuralPayloadPolynomial tokenCount
    outputCount outputBoundarySize
  have hprefix : prefixCertificate.compile.payloadLength <= prefixResource :=
    (compile_payloadLength_le_structuralPayloadBound prefixCertificate).trans
      (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount start outputStart hcompleted.1)
  have hlayoutRaw : layoutRaw.payloadLength <= layoutResource :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      layoutData.bodyStart numericBound bitBound
      layoutData.bodyStart_le_tokenCount layoutData.header
      layoutData.boundaryFinish_le_tokenCount layoutData.boundaryStartEntry
      layoutData.boundaryFinishEntry layoutData.rows htokenCount houtputCount
      htableSize hnumericSize
  have hlayout : layoutProof.payloadLength <= layoutResource := by
    dsimp only [layoutProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hlayoutRaw
  have hunitRaw : unitRaw.payloadLength <= unitResource :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount outputCount outputBoundary numericBound bitBound
      hcompleted.2.2.1 htokenCount houtputCount htableSize hnumericSize
  have hunit : unitProof.payloadLength <= unitResource := by
    dsimp only [unitProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hunitRaw
  have hsize : sizeCertificate.compile.payloadLength <= sizeResource :=
    (compile_payloadLength_le_structuralPayloadBound sizeCertificate).trans
      (compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        outputBoundarySize outputBoundary hcompleted.2.2.2.1)
  have harea : areaCertificate.compile.payloadLength <= areaResource :=
    (compile_payloadLength_le_structuralPayloadBound areaCertificate).trans
      (completedAreaCertificate_structuralPayloadBound_le_public tokenCount
        outputCount outputBoundarySize hcompleted.2.2.2.2)
  let sizeArea := compileDirectConjunction sizeCertificate.compile
    areaCertificate.compile
  let sizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sizeFormula areaFormula sizeResource areaResource
  have hsizeArea : sizeArea.payloadLength <= sizeAreaResource :=
    compileDirectConjunction_payloadLength_le sizeCertificate.compile
      areaCertificate.compile sizeResource areaResource hsize harea
  let unitTail := compileDirectConjunction unitProof sizeArea
  let unitTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation unitFormula (sizeFormula ⋏ areaFormula)
    unitResource sizeAreaResource
  have hunitTail : unitTail.payloadLength <= unitTailResource :=
    compileDirectConjunction_payloadLength_le unitProof sizeArea unitResource
      sizeAreaResource hunit hsizeArea
  let layoutTail := compileDirectConjunction layoutProof unitTail
  let layoutTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation layoutFormula
    (unitFormula ⋏ (sizeFormula ⋏ areaFormula)) layoutResource
    unitTailResource
  have hlayoutTail : layoutTail.payloadLength <= layoutTailResource :=
    compileDirectConjunction_payloadLength_le layoutProof unitTail
      layoutResource unitTailResource hlayout hunitTail
  let completed := compileDirectConjunction prefixCertificate.compile
    layoutTail
  have hcompletedBound := compileDirectConjunction_payloadLength_le
    prefixCertificate.compile layoutTail prefixResource layoutTailResource
    hprefix hlayoutTail
  change completed.payloadLength <= _
  simpa only [
    compactBinaryNatCompletedStatusFullyUniformDirectPayloadEnvelope,
    prefixFormula, layoutData, layoutFormula, unitFormula, sizeFormula,
    areaFormula, prefixResource, layoutResource, unitResource, sizeResource,
    areaResource, sizeAreaResource, unitTailResource, layoutTailResource] using
      hcompletedBound

def compactBinaryNatCompletedStatusFullyUniformDirectPublicPayloadEnvelope
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun bodyStart =>
    compactBinaryNatCompletedStatusFullyUniformDirectPayloadEnvelope
      tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount bodyStart numericBound bitBound

theorem
    compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le_public
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows tokenTable width
      tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf outputStart outputBoundary
          outputBoundarySize outputCount))
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (htableSize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactBinaryNatCompletedStatusFullyUniformDirect tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount numericBound bitBound hcompleted htokenCount houtputCount
      htableSize hnumericSize).payloadLength <=
      compactBinaryNatCompletedStatusFullyUniformDirectPublicPayloadEnvelope
        tokenTable width tokenCount start finish outputStart outputBoundary
        outputBoundarySize outputCount numericBound bitBound := by
  let layoutData := compactAdditiveStructuredListLayoutDataOfLayout tokenTable
    width tokenCount outputStart outputCount finish outputBoundary
    hcompleted.2.1
  have hatBodyStart :=
    compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le
      tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound hcompleted
      htokenCount houtputCount htableSize hnumericSize
  have hsum :
      compactBinaryNatCompletedStatusFullyUniformDirectPayloadEnvelope
          tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount layoutData.bodyStart numericBound
          bitBound <=
        compactBinaryNatCompletedStatusFullyUniformDirectPublicPayloadEnvelope
          tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount numericBound bitBound := by
    unfold
      compactBinaryNatCompletedStatusFullyUniformDirectPublicPayloadEnvelope
    exact Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compactBinaryNatCompletedStatusFullyUniformDirectPayloadEnvelope
          tokenTable width tokenCount start finish outputStart outputBoundary
          outputBoundarySize outputCount candidate numericBound bitBound))
      (Finset.mem_range.mpr
        (Nat.lt_succ_of_le layoutData.bodyStart_le_tokenCount))
  simpa only [layoutData] using hatBodyStart.trans hsum

#print axioms compileCompactBinaryNatCompletedStatusFullyUniformDirect
#print axioms
  compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le
#print axioms
  compileCompactBinaryNatCompletedStatusFullyUniformDirect_payloadLength_le_public

end FoundationCompactNumericListedDirectBinaryNatCompletedStatusFullyUniformDirectCompiler
