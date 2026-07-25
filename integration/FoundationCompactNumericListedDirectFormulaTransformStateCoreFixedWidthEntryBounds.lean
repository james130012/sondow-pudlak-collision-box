import integration.FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds
import integration.FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds

/-!
# Fixed-width entry closure inside formula-transform state cores

The state core has six independently certified conjuncts.  This layer replaces
the structured-list and unit-boundary-row resources by their complete
fixed-width-entry endpoints and reassembles the actual state-core certificate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 700000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStateCoreFixedWidthEntryBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCorePublicBounds
open FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitPublicBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds

noncomputable def
    compactFormulaTransformStateCoreFixedWidthEntryStructuralPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  let outerFormula := compactAdditiveProductSplitClosedFormula
    tokenCount coordinates.start coordinates.parserFinish coordinates.finish
  let parserFormula := compactUnifiedParserStateCoreClosedFormula
    tokenTable width tokenCount
    coordinates.parser.start coordinates.parser.finish
    coordinates.parser.tokensFinish coordinates.parser.tasksFinish
    coordinates.parser.tokensBoundary coordinates.parser.tokensCount
    coordinates.parser.tasksBoundary coordinates.parser.tasksCount
    sizeWitness.parser.tokensBoundarySize sizeWitness.parser.tasksBoundarySize
  let outputLayoutFormula := compactAdditiveStructuredListLayoutClosedFormula
    tokenTable width tokenCount coordinates.parserFinish
    coordinates.outputCount coordinates.finish coordinates.outputBoundary
  let outputRowsFormula := compactAdditiveUnitBoundaryRowsClosedFormula
    tokenCount coordinates.outputCount coordinates.outputBoundary
  let outputSizeFormula := compactNatSizeClosedFormula
    sizeWitness.outputBoundarySize coordinates.outputBoundary
  let outputAreaFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sizeWitness.outputBoundarySize) ≤
      (!!(shortBinaryNumeralTerm coordinates.outputCount) + 1) *
        !!(shortBinaryNumeralTerm tokenCount)”
  let outerResource :=
    compactAdditiveProductSplitStructuralPayloadPolynomial
      tokenCount coordinates.start coordinates.parserFinish coordinates.finish
  let parserResource :=
    compactUnifiedParserStateCoreFixedWidthEntryStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates.parser sizeWitness.parser
  let outputLayoutResource :=
    compactAdditiveStructuredListLayoutFixedWidthEntryStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
  let outputRowsResource :=
    compactAdditiveUnitBoundaryRowsFixedWidthEntryStructuralPayloadEnvelope
      tokenCount coordinates.outputCount coordinates.outputBoundary
  let outputSizeResource := compactNatSizeStructuralPayloadPolynomial
    sizeWitness.outputBoundarySize coordinates.outputBoundary
  let outputAreaResource := outputBoundaryAreaStructuralPayloadPolynomial
    tokenCount coordinates sizeWitness
  let outputSizeAreaResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate.zeroValuation
    outputSizeFormula outputAreaFormula outputSizeResource outputAreaResource
  let outputRowsTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation
    outputRowsFormula (outputSizeFormula ⋏ outputAreaFormula)
    outputRowsResource outputSizeAreaResource
  let outputLayoutTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation
    outputLayoutFormula
    (outputRowsFormula ⋏ (outputSizeFormula ⋏ outputAreaFormula))
    outputLayoutResource outputRowsTailResource
  let parserTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate.zeroValuation
    parserFormula
    (outputLayoutFormula ⋏
      (outputRowsFormula ⋏ (outputSizeFormula ⋏ outputAreaFormula)))
    parserResource outputLayoutTailResource
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate.zeroValuation
    outerFormula
    (parserFormula ⋏
      (outputLayoutFormula ⋏
        (outputRowsFormula ⋏ (outputSizeFormula ⋏ outputAreaFormula))))
    outerResource parserTailResource

theorem
    compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixedWidthEntry
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
          tokenTable width tokenCount coordinates sizeWitness hgraph) <=
      compactFormulaTransformStateCoreFixedWidthEntryStructuralPayloadEnvelope
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases hgraph with
    ⟨houter, hparser, houtputLayout, houtputRows,
      houtputSize, houtputArea⟩
  let outerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph
      tokenCount coordinates.start coordinates.parserFinish
      coordinates.finish houter
  let parserCertificate :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.parser sizeWitness.parser
      hparser
  let outputLayoutCertificate :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      houtputLayout
  let outputRowsCertificate :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount coordinates.outputCount coordinates.outputBoundary
      houtputRows
  let outputSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.outputBoundarySize coordinates.outputBoundary houtputSize
  let outputAreaCertificate :=
    FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate.outputBoundaryAreaCertificate
      tokenCount coordinates sizeWitness houtputArea
  have houterResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenCount coordinates.start coordinates.parserFinish
      coordinates.finish houter
  have hparserResource :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixedWidthEntry
      tokenTable width tokenCount coordinates.parser sizeWitness.parser hparser
  have houtputLayoutResource :=
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout_structuralPayloadBound_le_fixedWidthEntry
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      houtputLayout
  have houtputRowsTransparent :=
    compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenCount coordinates.outputCount coordinates.outputBoundary
      houtputRows
  have houtputRowsResource := houtputRowsTransparent.trans
    (compactAdditiveUnitBoundaryRowsGraphStructuralPayloadEnvelope_le_fixedWidthEntry
      tokenCount coordinates.outputCount coordinates.outputBoundary
      houtputRows)
  have houtputSizeResource :=
    compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
      sizeWitness.outputBoundarySize coordinates.outputBoundary houtputSize
  have houtputAreaResource :=
    outputBoundaryAreaCertificate_structuralPayloadBound_le_public
      tokenCount coordinates sizeWitness houtputArea
  let outputSizeArea :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputSizeCertificate outputAreaCertificate
  have houtputSizeArea := transparentHybridConjunctionPayloadBound_le
    outputSizeCertificate outputAreaCertificate _ _
    houtputSizeResource houtputAreaResource
  let outputRowsTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputRowsCertificate outputSizeArea
  have houtputRowsTail := transparentHybridConjunctionPayloadBound_le
    outputRowsCertificate outputSizeArea _ _
    houtputRowsResource houtputSizeArea
  let outputLayoutTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      outputLayoutCertificate outputRowsTail
  have houtputLayoutTail := transparentHybridConjunctionPayloadBound_le
    outputLayoutCertificate outputRowsTail _ _
    houtputLayoutResource houtputRowsTail
  let parserTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      parserCertificate outputLayoutTail
  have hparserTail := transparentHybridConjunctionPayloadBound_le
    parserCertificate outputLayoutTail _ _
    hparserResource houtputLayoutTail
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    outerCertificate parserTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    outerCertificate parserTail _ _ houterResource hparserTail
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactFormulaTransformStateCoreClosedFormula_alignment
          tokenTable width tokenCount coordinates sizeWitness).symm parts) <= _
  unfold
    compactFormulaTransformStateCoreFixedWidthEntryStructuralPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound,
    outerCertificate, parserCertificate, outputLayoutCertificate,
    outputRowsCertificate, outputSizeCertificate, outputAreaCertificate,
    outputSizeArea, outputRowsTail, outputLayoutTail, parserTail, parts]
    using hparts

#print axioms
  compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fixedWidthEntry

end FoundationCompactNumericListedDirectFormulaTransformStateCoreFixedWidthEntryBounds
