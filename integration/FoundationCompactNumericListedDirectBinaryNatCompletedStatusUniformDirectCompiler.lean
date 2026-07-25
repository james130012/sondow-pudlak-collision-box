import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler

/-!
# Uniform direct compiler for the completed binary-Nat status branch

The completed branch combines five independently checked leaves.  Its unit
boundary leaf is the uniform direct compiler, so no finite enumeration over
cursor values or proof-dependent unit-row resource remains in this branch.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler

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
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

local notation "completedZeroValuation" =>
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

def compactBinaryNatCompletedStatusUniformDirectFormula
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount : Nat) : ValuationFormula :=
  compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount start outputStart ⋏
    (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount outputStart outputCount finish
          outputBoundary ⋏
      (compactAdditiveUnitBoundaryRowsClosedFormula
          tokenCount outputCount outputBoundary ⋏
        (compactNatSizeClosedFormula outputBoundarySize outputBoundary ⋏
          “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
            (!!(shortBinaryNumeralTerm outputCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)”)))

def compactBinaryNatCompletedStatusUniformDirectPayloadEnvelope
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat) : Nat :=
  let prefixFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount start outputStart
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount outputCount outputBoundary
  let sizeFormula := compactNatSizeClosedFormula
    outputBoundarySize outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let prefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
      outputCount outputBoundary numericBound bitBound
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    outputBoundarySize outputBoundary
  let areaResource := completedAreaStructuralPayloadPolynomial
    tokenCount outputCount outputBoundarySize
  let sizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation sizeFormula areaFormula sizeResource areaResource
  let unitTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation unitFormula (sizeFormula ⋏ areaFormula)
    unitResource sizeAreaResource
  let layoutTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation layoutFormula
    (unitFormula ⋏ (sizeFormula ⋏ areaFormula))
    layoutResource unitTailResource
  transparentHybridConjunctionPayloadEnvelope completedZeroValuation prefixFormula
    (layoutFormula ⋏ (unitFormula ⋏ (sizeFormula ⋏ areaFormula)))
    prefixResource layoutTailResource

noncomputable def compileCompactBinaryNatCompletedStatusUniformDirect
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf
          outputStart outputBoundary outputBoundarySize outputCount))
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
  let layoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      hcompleted.2.1
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount outputCount outputBoundary
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
  let areaCertificate := completedAreaCertificate
    tokenCount outputCount outputBoundarySize hcompleted.2.2.2.2
  let sizeArea := compileDirectConjunction
    sizeCertificate.compile areaCertificate.compile
  let unitTail := compileDirectConjunction unitProof sizeArea
  let layoutTail := compileDirectConjunction layoutCertificate.compile unitTail
  let completed := compileDirectConjunction prefixCertificate.compile layoutTail
  exact completed

theorem compileCompactBinaryNatCompletedStatusUniformDirect_payloadLength_le
    (tokenTable width tokenCount start finish outputStart outputBoundary
      outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
        (compactBinaryNatStatusValidityWitnessOf
          outputStart outputBoundary outputBoundarySize outputCount))
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : outputCount <= numericBound)
    (htableSize : Nat.size outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactBinaryNatCompletedStatusUniformDirect tokenTable width
      tokenCount start finish outputStart outputBoundary outputBoundarySize
      outputCount numericBound bitBound hcompleted htokenCount houtputCount
      htableSize hnumericSize).payloadLength <=
      compactBinaryNatCompletedStatusUniformDirectPayloadEnvelope tokenTable
        width tokenCount start finish outputStart outputBoundary
        outputBoundarySize outputCount numericBound bitBound := by
  let prefixFormula :=
    compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount start outputStart
  let layoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount outputCount outputBoundary
  let sizeFormula := compactNatSizeClosedFormula
    outputBoundarySize outputBoundary
  let areaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let prefixCertificate :=
    compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount start outputStart hcompleted.1
  let layoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
      hcompleted.2.1
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
  let areaCertificate := completedAreaCertificate
    tokenCount outputCount outputBoundarySize hcompleted.2.2.2.2
  let prefixResource :=
    compactBinaryNatCompletedStatusPrefixStructuralPayloadPolynomial
      tokenTable width tokenCount start outputStart
  let layoutResource :=
    compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
      tokenTable width tokenCount outputStart outputCount finish outputBoundary
  let unitResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
      outputCount outputBoundary numericBound bitBound
  let sizeResource := compactNatSizeStructuralPayloadPolynomial
    outputBoundarySize outputBoundary
  let areaResource := completedAreaStructuralPayloadPolynomial
    tokenCount outputCount outputBoundarySize
  have hprefix : prefixCertificate.compile.payloadLength <= prefixResource :=
    (compile_payloadLength_le_structuralPayloadBound prefixCertificate).trans
      (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenTable width tokenCount start outputStart hcompleted.1)
  have hlayout : layoutCertificate.compile.payloadLength <= layoutResource :=
    (compile_payloadLength_le_structuralPayloadBound layoutCertificate).trans
      (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_fixedWidthEntry
        tokenTable width tokenCount outputStart outputCount finish
        outputBoundary hcompleted.2.1)
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
  let sizeArea := compileDirectConjunction
    sizeCertificate.compile areaCertificate.compile
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
  let layoutTail := compileDirectConjunction layoutCertificate.compile unitTail
  let layoutTailResource := transparentHybridConjunctionPayloadEnvelope
    completedZeroValuation layoutFormula
    (unitFormula ⋏ (sizeFormula ⋏ areaFormula))
    layoutResource unitTailResource
  have hlayoutTail : layoutTail.payloadLength <= layoutTailResource :=
    compileDirectConjunction_payloadLength_le layoutCertificate.compile unitTail
      layoutResource unitTailResource hlayout hunitTail
  let completed := compileDirectConjunction prefixCertificate.compile layoutTail
  have hcompletedBound := compileDirectConjunction_payloadLength_le
    prefixCertificate.compile layoutTail prefixResource layoutTailResource
    hprefix hlayoutTail
  change completed.payloadLength <= _
  simpa only [compactBinaryNatCompletedStatusUniformDirectPayloadEnvelope,
    prefixFormula, layoutFormula, unitFormula, sizeFormula, areaFormula,
    prefixResource, layoutResource, unitResource, sizeResource, areaResource,
    sizeAreaResource, unitTailResource, layoutTailResource] using hcompletedBound

#print axioms compileCompactBinaryNatCompletedStatusUniformDirect
#print axioms compileCompactBinaryNatCompletedStatusUniformDirect_payloadLength_le

end FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
