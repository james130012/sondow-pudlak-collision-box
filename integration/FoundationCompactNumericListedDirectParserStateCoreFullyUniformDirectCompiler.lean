import integration.FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-!
# Fully uniform direct compiler for the numeric parser-state core

The ten checked leaves are compiled independently.  Structured-list, unit-row,
and triple-row leaves use their uniform direct compilers, so no proof-dependent
finite sum survives in the public payload resource.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

private abbrev parserZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.zeroValuation

structure ClosedDirectFormulaBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

theorem compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize : Nat) :
    (compactUnifiedParserStateCoreClosedFormula tokenTable width tokenCount
      start finish tokensFinish tasksFinish tokensBoundary tokensCount
      tasksBoundary tasksCount tokensBoundarySize
      tasksBoundarySize).freeVariables = ∅ := by
  unfold compactUnifiedParserStateCoreClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

def compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (tokensBodyStart tasksBodyStart numericBound bitBound : Nat) : Nat :=
  let outerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
  let tokensRowsFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount coordinates.tokensCount coordinates.tokensBoundary
  let innerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.tokensFinish coordinates.tasksFinish coordinates.finish
  let tasksLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary
  let tasksRowsFormula := compactAdditiveTripleBoundaryRowsClosedFormula
    tokenCount coordinates.tasksCount coordinates.tasksBoundary
  let tokensSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tokensBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tokensCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let tasksSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tasksBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tasksCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let outerResource := compactAdditiveProductSplitStructuralPayloadPolynomial
    tokenCount coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope tokenTable
      width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary tokensBodyStart
      numericBound bitBound
  let tokensRowsResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
      coordinates.tokensCount coordinates.tokensBoundary numericBound bitBound
  let innerResource := compactAdditiveProductSplitStructuralPayloadPolynomial
    tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish
  let tasksLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope tokenTable
      width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary tasksBodyStart
      numericBound bitBound
  let tasksRowsResource :=
    compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource tokenCount
      coordinates.tasksCount coordinates.tasksBoundary numericBound bitBound
  let tokensSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaResource := boundaryAreaStructuralPayloadPolynomial
    sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
  let tasksSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaResource := boundaryAreaStructuralPayloadPolynomial
    sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
  let tasksSizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tasksSizeFormula tasksAreaFormula tasksSizeResource
      tasksAreaResource
  let tokensAreaTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensAreaFormula
      (tasksSizeFormula ⋏ tasksAreaFormula) tokensAreaResource
      tasksSizeAreaResource
  let tokensSizeTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensSizeFormula
      (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))
      tokensSizeResource tokensAreaTailResource
  let tasksRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tasksRowsFormula
      (tokensSizeFormula ⋏
        (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula)))
      tasksRowsResource tokensSizeTailResource
  let tasksLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tasksLayoutFormula
      (tasksRowsFormula ⋏
        (tokensSizeFormula ⋏
          (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))))
      tasksLayoutResource tasksRowsTailResource
  let innerTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation innerFormula
      (tasksLayoutFormula ⋏
        (tasksRowsFormula ⋏
          (tokensSizeFormula ⋏
            (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula)))))
      innerResource tasksLayoutTailResource
  let tokensRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensRowsFormula
      (innerFormula ⋏
        (tasksLayoutFormula ⋏
          (tasksRowsFormula ⋏
            (tokensSizeFormula ⋏
              (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))))))
      tokensRowsResource innerTailResource
  let tokensLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensLayoutFormula
      (tokensRowsFormula ⋏
        (innerFormula ⋏
          (tasksLayoutFormula ⋏
            (tasksRowsFormula ⋏
              (tokensSizeFormula ⋏
                (tokensAreaFormula ⋏
                  (tasksSizeFormula ⋏ tasksAreaFormula)))))))
      tokensLayoutResource tokensRowsTailResource
  transparentHybridConjunctionPayloadEnvelope parserZeroValuation outerFormula
    (tokensLayoutFormula ⋏
      (tokensRowsFormula ⋏
        (innerFormula ⋏
          (tasksLayoutFormula ⋏
            (tasksRowsFormula ⋏
              (tokensSizeFormula ⋏
                (tokensAreaFormula ⋏
                  (tasksSizeFormula ⋏ tasksAreaFormula))))))))
    outerResource tokensLayoutTailResource

def compactUnifiedParserStateCoreFullyUniformDirectPublicPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (numericBound bitBound : Nat) : Nat :=
  (Finset.range (tokenCount + 1)).sum fun tokensBodyStart =>
    (Finset.range (tokenCount + 1)).sum fun tasksBodyStart =>
      compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness tokensBodyStart
        tasksBodyStart numericBound bitBound

noncomputable def compactUnifiedParserStateCoreFullyUniformDirectBound
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokensCount : coordinates.tokensCount <= numericBound)
    (htasksCount : coordinates.tasksCount <= numericBound)
    (htokensTableSize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htasksTableSize : Nat.size coordinates.tasksBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ClosedDirectFormulaBound
      (compactUnifiedParserStateCoreClosedFormula tokenTable width tokenCount
        coordinates.start coordinates.finish coordinates.tokensFinish
        coordinates.tasksFinish coordinates.tokensBoundary
        coordinates.tokensCount coordinates.tasksBoundary
        coordinates.tasksCount sizeWitness.tokensBoundarySize
        sizeWitness.tasksBoundarySize)
      (compactUnifiedParserStateCoreFullyUniformDirectPublicPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness numericBound
        bitBound) := by
  rcases hgraph with
    ⟨houter, htokensLayout, htokensRows, hinner, htasksLayout, htasksRows,
      htokensSize, htokensArea, htasksSize, htasksArea⟩
  let tokensLayoutData := compactAdditiveStructuredListLayoutDataOfLayout
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary htokensLayout
  let tasksLayoutData := compactAdditiveStructuredListLayoutDataOfLayout
    tokenTable width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary htasksLayout
  let outerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
  let tokensRowsFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount coordinates.tokensCount coordinates.tokensBoundary
  let innerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.tokensFinish coordinates.tasksFinish coordinates.finish
  let tasksLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary
  let tasksRowsFormula := compactAdditiveTripleBoundaryRowsClosedFormula
    tokenCount coordinates.tasksCount coordinates.tasksBoundary
  let tokensSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tokensBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tokensCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let tasksSizeFormula := compactNatSizeClosedFormula
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.tasksBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.tasksCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let outerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      coordinates.start coordinates.tokensFinish coordinates.finish houter
  let tokensLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
      tokensLayoutData.bodyStart numericBound bitBound
      tokensLayoutData.bodyStart_le_tokenCount tokensLayoutData.header
      tokensLayoutData.boundaryFinish_le_tokenCount
      tokensLayoutData.boundaryStartEntry tokensLayoutData.boundaryFinishEntry
      tokensLayoutData.rows htokenCount htokensCount htokensTableSize
      hnumericSize
  have htokensLayoutContext : (∅ : Finset ValuationFormula) =
      valuationContext tokensLayoutFormula.freeVariables
        parserZeroValuation := by
    rw [show tokensLayoutFormula.freeVariables = ∅ by
      simpa only [tokensLayoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount coordinates.start
          coordinates.tokensCount coordinates.tokensFinish
          coordinates.tokensBoundary]
    simp [valuationContext]
  let tokensLayoutProof := CertifiedPAContextProof.castContext
    htokensLayoutContext tokensLayoutRaw
  let tokensRowsRaw :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      numericBound bitBound htokensRows htokenCount htokensCount
      htokensTableSize hnumericSize
  have htokensRowsContext : (∅ : Finset ValuationFormula) =
      valuationContext tokensRowsFormula.freeVariables parserZeroValuation := by
    rw [show tokensRowsFormula.freeVariables = ∅ by
      simpa only [tokensRowsFormula] using
        compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
          tokenCount coordinates.tokensCount coordinates.tokensBoundary]
    simp [valuationContext]
  let tokensRowsProof := CertifiedPAContextProof.castContext
    htokensRowsContext tokensRowsRaw
  let innerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      coordinates.tokensFinish coordinates.tasksFinish coordinates.finish
      hinner
  let tasksLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      tasksLayoutData.bodyStart numericBound bitBound
      tasksLayoutData.bodyStart_le_tokenCount tasksLayoutData.header
      tasksLayoutData.boundaryFinish_le_tokenCount
      tasksLayoutData.boundaryStartEntry tasksLayoutData.boundaryFinishEntry
      tasksLayoutData.rows htokenCount htasksCount htasksTableSize hnumericSize
  have htasksLayoutContext : (∅ : Finset ValuationFormula) =
      valuationContext tasksLayoutFormula.freeVariables
        parserZeroValuation := by
    rw [show tasksLayoutFormula.freeVariables = ∅ by
      simpa only [tasksLayoutFormula] using
        compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount coordinates.tokensFinish
          coordinates.tasksCount coordinates.tasksFinish
          coordinates.tasksBoundary]
    simp [valuationContext]
  let tasksLayoutProof := CertifiedPAContextProof.castContext
    htasksLayoutContext tasksLayoutRaw
  let tasksRowsRaw :=
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount coordinates.tasksCount coordinates.tasksBoundary
      numericBound bitBound htasksRows htokenCount htasksCount htasksTableSize
      hnumericSize
  have htasksRowsContext : (∅ : Finset ValuationFormula) =
      valuationContext tasksRowsFormula.freeVariables parserZeroValuation := by
    rw [show tasksRowsFormula.freeVariables = ∅ by
      simpa only [tasksRowsFormula] using
        compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
          tokenCount coordinates.tasksCount coordinates.tasksBoundary]
    simp [valuationContext]
  let tasksRowsProof := CertifiedPAContextProof.castContext htasksRowsContext
    tasksRowsRaw
  let tokensSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary htokensSize
  let tokensAreaCertificate := boundaryAreaCertificate
    sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
      htokensArea
  let tasksSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary htasksSize
  let tasksAreaCertificate := boundaryAreaCertificate
    sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount htasksArea
  let outerResource := compactAdditiveProductSplitStructuralPayloadPolynomial
    tokenCount coordinates.start coordinates.tokensFinish coordinates.finish
  let tokensLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope tokenTable
      width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
      tokensLayoutData.bodyStart numericBound bitBound
  let tokensRowsResource :=
    compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource tokenCount
      coordinates.tokensCount coordinates.tokensBoundary numericBound bitBound
  let innerResource := compactAdditiveProductSplitStructuralPayloadPolynomial
    tokenCount coordinates.tokensFinish coordinates.tasksFinish
      coordinates.finish
  let tasksLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectPayloadEnvelope tokenTable
      width tokenCount coordinates.tokensFinish coordinates.tasksCount
      coordinates.tasksFinish coordinates.tasksBoundary
      tasksLayoutData.bodyStart numericBound bitBound
  let tasksRowsResource :=
    compactAdditiveTripleBoundaryRowsUniformDirectUniversalResource tokenCount
      coordinates.tasksCount coordinates.tasksBoundary numericBound bitBound
  let tokensSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.tokensBoundarySize coordinates.tokensBoundary
  let tokensAreaResource := boundaryAreaStructuralPayloadPolynomial
    sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
  let tasksSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.tasksBoundarySize coordinates.tasksBoundary
  let tasksAreaResource := boundaryAreaStructuralPayloadPolynomial
    sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
  have houterProof : outerCertificate.compile.payloadLength <= outerResource :=
    (compile_payloadLength_le_structuralPayloadBound outerCertificate).trans
      (compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenCount coordinates.start coordinates.tokensFinish
        coordinates.finish houter)
  have htokensLayoutRaw : tokensLayoutRaw.payloadLength <=
      tokensLayoutResource :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le
      tokenTable width tokenCount coordinates.start coordinates.tokensCount
      coordinates.tokensFinish coordinates.tokensBoundary
      tokensLayoutData.bodyStart numericBound bitBound
      tokensLayoutData.bodyStart_le_tokenCount tokensLayoutData.header
      tokensLayoutData.boundaryFinish_le_tokenCount
      tokensLayoutData.boundaryStartEntry tokensLayoutData.boundaryFinishEntry
      tokensLayoutData.rows htokenCount htokensCount htokensTableSize
      hnumericSize
  have htokensLayoutProof : tokensLayoutProof.payloadLength <=
      tokensLayoutResource := by
    dsimp only [tokensLayoutProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact htokensLayoutRaw
  have htokensRowsRaw : tokensRowsRaw.payloadLength <= tokensRowsResource :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount coordinates.tokensCount coordinates.tokensBoundary
      numericBound bitBound htokensRows htokenCount htokensCount
      htokensTableSize hnumericSize
  have htokensRowsProof : tokensRowsProof.payloadLength <=
      tokensRowsResource := by
    dsimp only [tokensRowsProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact htokensRowsRaw
  have hinnerProof : innerCertificate.compile.payloadLength <= innerResource :=
    (compile_payloadLength_le_structuralPayloadBound innerCertificate).trans
      (compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
        tokenCount coordinates.tokensFinish coordinates.tasksFinish
        coordinates.finish hinner)
  have htasksLayoutRaw : tasksLayoutRaw.payloadLength <= tasksLayoutResource :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le
      tokenTable width tokenCount coordinates.tokensFinish
      coordinates.tasksCount coordinates.tasksFinish coordinates.tasksBoundary
      tasksLayoutData.bodyStart numericBound bitBound
      tasksLayoutData.bodyStart_le_tokenCount tasksLayoutData.header
      tasksLayoutData.boundaryFinish_le_tokenCount
      tasksLayoutData.boundaryStartEntry tasksLayoutData.boundaryFinishEntry
      tasksLayoutData.rows htokenCount htasksCount htasksTableSize hnumericSize
  have htasksLayoutProof : tasksLayoutProof.payloadLength <=
      tasksLayoutResource := by
    dsimp only [tasksLayoutProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact htasksLayoutRaw
  have htasksRowsRaw : tasksRowsRaw.payloadLength <= tasksRowsResource :=
    compileCompactAdditiveTripleBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount coordinates.tasksCount coordinates.tasksBoundary
      numericBound bitBound htasksRows htokenCount htasksCount htasksTableSize
      hnumericSize
  have htasksRowsProof : tasksRowsProof.payloadLength <= tasksRowsResource := by
    dsimp only [tasksRowsProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact htasksRowsRaw
  have htokensSize : tokensSizeCertificate.compile.payloadLength <=
      tokensSizeResource :=
    (compile_payloadLength_le_structuralPayloadBound
      tokensSizeCertificate).trans
      (compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        sizeWitness.tokensBoundarySize coordinates.tokensBoundary htokensSize)
  have htokensArea : tokensAreaCertificate.compile.payloadLength <=
      tokensAreaResource :=
    (compile_payloadLength_le_structuralPayloadBound
      tokensAreaCertificate).trans
      (boundaryAreaCertificate_structuralPayloadBound_le_public
        sizeWitness.tokensBoundarySize coordinates.tokensCount tokenCount
        htokensArea)
  have htasksSize : tasksSizeCertificate.compile.payloadLength <=
      tasksSizeResource :=
    (compile_payloadLength_le_structuralPayloadBound tasksSizeCertificate).trans
      (compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        sizeWitness.tasksBoundarySize coordinates.tasksBoundary htasksSize)
  have htasksArea : tasksAreaCertificate.compile.payloadLength <=
      tasksAreaResource :=
    (compile_payloadLength_le_structuralPayloadBound tasksAreaCertificate).trans
      (boundaryAreaCertificate_structuralPayloadBound_le_public
        sizeWitness.tasksBoundarySize coordinates.tasksCount tokenCount
        htasksArea)
  let tasksSizeArea := compileDirectConjunction tasksSizeCertificate.compile
    tasksAreaCertificate.compile
  let tasksSizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tasksSizeFormula tasksAreaFormula tasksSizeResource
      tasksAreaResource
  have htasksSizeArea : tasksSizeArea.payloadLength <= tasksSizeAreaResource :=
    compileDirectConjunction_payloadLength_le tasksSizeCertificate.compile
      tasksAreaCertificate.compile tasksSizeResource tasksAreaResource
      htasksSize htasksArea
  let tokensAreaTail := compileDirectConjunction tokensAreaCertificate.compile
    tasksSizeArea
  let tokensAreaTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensAreaFormula
      (tasksSizeFormula ⋏ tasksAreaFormula) tokensAreaResource
      tasksSizeAreaResource
  have htokensAreaTail : tokensAreaTail.payloadLength <=
      tokensAreaTailResource :=
    compileDirectConjunction_payloadLength_le tokensAreaCertificate.compile
      tasksSizeArea tokensAreaResource tasksSizeAreaResource htokensArea
      htasksSizeArea
  let tokensSizeTail := compileDirectConjunction tokensSizeCertificate.compile
    tokensAreaTail
  let tokensSizeTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensSizeFormula
      (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))
      tokensSizeResource tokensAreaTailResource
  have htokensSizeTail : tokensSizeTail.payloadLength <=
      tokensSizeTailResource :=
    compileDirectConjunction_payloadLength_le tokensSizeCertificate.compile
      tokensAreaTail tokensSizeResource tokensAreaTailResource htokensSize
      htokensAreaTail
  let tasksRowsTail := compileDirectConjunction tasksRowsProof tokensSizeTail
  let tasksRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tasksRowsFormula
      (tokensSizeFormula ⋏
        (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula)))
      tasksRowsResource tokensSizeTailResource
  have htasksRowsTail : tasksRowsTail.payloadLength <= tasksRowsTailResource :=
    compileDirectConjunction_payloadLength_le tasksRowsProof tokensSizeTail
      tasksRowsResource tokensSizeTailResource htasksRowsProof
      htokensSizeTail
  let tasksLayoutTail := compileDirectConjunction tasksLayoutProof
    tasksRowsTail
  let tasksLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tasksLayoutFormula
      (tasksRowsFormula ⋏
        (tokensSizeFormula ⋏
          (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))))
      tasksLayoutResource tasksRowsTailResource
  have htasksLayoutTail : tasksLayoutTail.payloadLength <=
      tasksLayoutTailResource :=
    compileDirectConjunction_payloadLength_le tasksLayoutProof tasksRowsTail
      tasksLayoutResource tasksRowsTailResource htasksLayoutProof
      htasksRowsTail
  let innerTail := compileDirectConjunction innerCertificate.compile
    tasksLayoutTail
  let innerTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation innerFormula
      (tasksLayoutFormula ⋏
        (tasksRowsFormula ⋏
          (tokensSizeFormula ⋏
            (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula)))))
      innerResource tasksLayoutTailResource
  have hinnerTail : innerTail.payloadLength <= innerTailResource :=
    compileDirectConjunction_payloadLength_le innerCertificate.compile
      tasksLayoutTail innerResource tasksLayoutTailResource hinnerProof
      htasksLayoutTail
  let tokensRowsTail := compileDirectConjunction tokensRowsProof innerTail
  let tokensRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensRowsFormula
      (innerFormula ⋏
        (tasksLayoutFormula ⋏
          (tasksRowsFormula ⋏
            (tokensSizeFormula ⋏
              (tokensAreaFormula ⋏ (tasksSizeFormula ⋏ tasksAreaFormula))))))
      tokensRowsResource innerTailResource
  have htokensRowsTail : tokensRowsTail.payloadLength <=
      tokensRowsTailResource :=
    compileDirectConjunction_payloadLength_le tokensRowsProof innerTail
      tokensRowsResource innerTailResource htokensRowsProof hinnerTail
  let tokensLayoutTail := compileDirectConjunction tokensLayoutProof
    tokensRowsTail
  let tokensLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    parserZeroValuation tokensLayoutFormula
      (tokensRowsFormula ⋏
        (innerFormula ⋏
          (tasksLayoutFormula ⋏
            (tasksRowsFormula ⋏
              (tokensSizeFormula ⋏
                (tokensAreaFormula ⋏
                  (tasksSizeFormula ⋏ tasksAreaFormula)))))))
      tokensLayoutResource tokensRowsTailResource
  have htokensLayoutTail : tokensLayoutTail.payloadLength <=
      tokensLayoutTailResource :=
    compileDirectConjunction_payloadLength_le tokensLayoutProof
      tokensRowsTail tokensLayoutResource tokensRowsTailResource
      htokensLayoutProof htokensRowsTail
  let parts := compileDirectConjunction outerCertificate.compile
    tokensLayoutTail
  have hparts : parts.payloadLength <=
      transparentHybridConjunctionPayloadEnvelope parserZeroValuation
        outerFormula
        (tokensLayoutFormula ⋏
          (tokensRowsFormula ⋏
            (innerFormula ⋏
              (tasksLayoutFormula ⋏
                (tasksRowsFormula ⋏
                  (tokensSizeFormula ⋏
                    (tokensAreaFormula ⋏
                      (tasksSizeFormula ⋏ tasksAreaFormula))))))))
        outerResource tokensLayoutTailResource :=
    compileDirectConjunction_payloadLength_le outerCertificate.compile
      tokensLayoutTail outerResource tokensLayoutTailResource houterProof
      htokensLayoutTail
  let closedFormula := compactUnifiedParserStateCoreClosedFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  let explicitFormula := compactUnifiedParserStateCoreExplicitFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  have hformula : explicitFormula = closedFormula :=
    (compactUnifiedParserStateCoreClosedFormula_alignment tokenTable width
      tokenCount coordinates.start coordinates.finish
      coordinates.tokensFinish coordinates.tasksFinish
      coordinates.tokensBoundary coordinates.tokensCount
      coordinates.tasksBoundary coordinates.tasksCount
      sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize).symm
  let formulaProof := CertifiedPAContextProof.cast hformula parts
  have hcontext : valuationContext explicitFormula.freeVariables
      parserZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [hformula]
    rw [show closedFormula.freeVariables = ∅ by
      simpa only [closedFormula] using
        compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty
          tokenTable width tokenCount coordinates.start coordinates.finish
          coordinates.tokensFinish coordinates.tasksFinish
          coordinates.tokensBoundary coordinates.tokensCount
          coordinates.tasksBoundary coordinates.tasksCount
          sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext formulaProof
  refine { proof := proof, payloadLength_le := ?_ }
  change proof.payloadLength <= _
  have hformulaProofLength : formulaProof.payloadLength =
      parts.payloadLength := by
    dsimp only [formulaProof]
    exact CertifiedPAContextProof.cast_payloadLength hformula parts
  have hproofLength : proof.payloadLength = parts.payloadLength := by
    dsimp only [proof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hformulaProofLength
  rw [hproofLength]
  have hexact : parts.payloadLength <=
      compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness
        tokensLayoutData.bodyStart tasksLayoutData.bodyStart numericBound
        bitBound := by
    simpa only [
    compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope,
    tokensLayoutData, tasksLayoutData, outerFormula, tokensLayoutFormula,
    tokensRowsFormula, innerFormula, tasksLayoutFormula, tasksRowsFormula,
    tokensSizeFormula, tokensAreaFormula, tasksSizeFormula, tasksAreaFormula,
    outerResource, tokensLayoutResource, tokensRowsResource, innerResource,
    tasksLayoutResource, tasksRowsResource, tokensSizeResource,
    tokensAreaResource, tasksSizeResource, tasksAreaResource,
    tasksSizeAreaResource, tokensAreaTailResource, tokensSizeTailResource,
    tasksRowsTailResource, tasksLayoutTailResource, innerTailResource,
    tokensRowsTailResource, tokensLayoutTailResource] using hparts
  have htasksMember : tasksLayoutData.bodyStart ∈
      Finset.range (tokenCount + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le tasksLayoutData.bodyStart_le_tokenCount
  have htasksSum :
      compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
          tokenTable width tokenCount coordinates sizeWitness
          tokensLayoutData.bodyStart tasksLayoutData.bodyStart numericBound
          bitBound <=
        (Finset.range (tokenCount + 1)).sum fun tasksBodyStart =>
          compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
            tokenTable width tokenCount coordinates sizeWitness
            tokensLayoutData.bodyStart tasksBodyStart numericBound bitBound :=
    Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        (compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
          tokenTable width tokenCount coordinates sizeWitness
          tokensLayoutData.bodyStart candidate numericBound bitBound))
      htasksMember
  have htokensMember : tokensLayoutData.bodyStart ∈
      Finset.range (tokenCount + 1) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le tokensLayoutData.bodyStart_le_tokenCount
  have htokensSum :
      ((Finset.range (tokenCount + 1)).sum fun tasksBodyStart =>
          compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
            tokenTable width tokenCount coordinates sizeWitness
            tokensLayoutData.bodyStart tasksBodyStart numericBound bitBound) <=
        (Finset.range (tokenCount + 1)).sum fun tokensBodyStart =>
          (Finset.range (tokenCount + 1)).sum fun tasksBodyStart =>
            compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
              tokenTable width tokenCount coordinates sizeWitness
              tokensBodyStart tasksBodyStart numericBound bitBound :=
    Finset.single_le_sum
      (fun candidate _ => Nat.zero_le
        ((Finset.range (tokenCount + 1)).sum fun tasksBodyStart =>
          compactUnifiedParserStateCoreFullyUniformDirectPayloadEnvelope
            tokenTable width tokenCount coordinates sizeWitness candidate
            tasksBodyStart numericBound bitBound))
      htokensMember
  exact hexact.trans (htasksSum.trans (by
    simpa only [
      compactUnifiedParserStateCoreFullyUniformDirectPublicPayloadEnvelope]
      using htokensSum))

noncomputable def compileCompactUnifiedParserStateCoreFullyUniformDirect
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokensCount : coordinates.tokensCount <= numericBound)
    (htasksCount : coordinates.tasksCount <= numericBound)
    (htokensTableSize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htasksTableSize : Nat.size coordinates.tasksBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :=
  (compactUnifiedParserStateCoreFullyUniformDirectBound tokenTable width
    tokenCount coordinates sizeWitness hgraph numericBound bitBound
    htokenCount htokensCount htasksCount htokensTableSize htasksTableSize
    hnumericSize).proof

theorem compileCompactUnifiedParserStateCoreFullyUniformDirect_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokensCount : coordinates.tokensCount <= numericBound)
    (htasksCount : coordinates.tasksCount <= numericBound)
    (htokensTableSize : Nat.size coordinates.tokensBoundary <= bitBound)
    (htasksTableSize : Nat.size coordinates.tasksBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactUnifiedParserStateCoreFullyUniformDirect tokenTable width
      tokenCount coordinates sizeWitness hgraph numericBound bitBound
      htokenCount htokensCount htasksCount htokensTableSize htasksTableSize
      hnumericSize).payloadLength <=
      compactUnifiedParserStateCoreFullyUniformDirectPublicPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness numericBound
        bitBound :=
  (compactUnifiedParserStateCoreFullyUniformDirectBound tokenTable width
    tokenCount coordinates sizeWitness hgraph numericBound bitBound
    htokenCount htokensCount htasksCount htokensTableSize htasksTableSize
    hnumericSize).payloadLength_le

#print axioms compactUnifiedParserStateCoreFullyUniformDirectBound
#print axioms
  compileCompactUnifiedParserStateCoreFullyUniformDirect_payloadLength_le

end FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
