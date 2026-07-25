import integration.FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

/-!
# Fully uniform fixed direct compiler for formula-transform state cores

The six checked leaves use the fixed parser-state, product-split, output-list,
unit-boundary, binary-length, and area endpoints.  Five direct conjunctions
assemble the exact closed seventeen-coordinate state-core formula.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStateCoreFullyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerGeneralContextBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveProductSplitFixedPolynomialBounds
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutUniformDirectClosedFixedBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizePublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds

theorem compactFormulaTransformStateCoreClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    (compactFormulaTransformStateCoreClosedFormula tokenTable width tokenCount
      coordinates sizeWitness).freeVariables = ∅ := by
  unfold compactFormulaTransformStateCoreClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

def compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  productSplitFixedPayloadPolynomial bitBound +
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    parserAreaFixedPayloadPolynomial bitBound +
    5 * (binaryNatCode 4).length + 1

def compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  productSplitFixedPayloadPolynomial bitBound +
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound +
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound +
    compactNatSizeFixedPayloadPolynomial bitBound +
    parserAreaFixedPayloadPolynomial bitBound +
    15 * generalContextAssemblyEnvelope syntaxResource

noncomputable def compactFormulaTransformStateCoreFullyUniformDirectFixedBound
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hparserTokensCount : coordinates.parserTokensCount <= numericBound)
    (hparserTasksCount : coordinates.parserTasksCount <= numericBound)
    (houtputCount : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hparserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputTableSize : Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ClosedDirectFormulaBound
      (compactFormulaTransformStateCoreClosedFormula tokenTable width
        tokenCount coordinates sizeWitness)
      (compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
        numericBound bitBound) := by
  rcases hgraph with
    ⟨houter, hparser, houtputLayout, houtputRows, houtputSize,
      houtputArea⟩
  let outputLayoutData := compactAdditiveStructuredListLayoutDataOfLayout
    tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      houtputLayout
  let outerFormula := compactAdditiveProductSplitClosedFormula tokenCount
    coordinates.start coordinates.parserFinish coordinates.finish
  let parserFormula := compactUnifiedParserStateCoreClosedFormula tokenTable
    width tokenCount coordinates.start coordinates.parserFinish
    coordinates.parserTokensFinish coordinates.parserTasksFinish
    coordinates.parserTokensBoundary coordinates.parserTokensCount
    coordinates.parserTasksBoundary coordinates.parserTasksCount
    sizeWitness.parserTokensBoundarySize
    sizeWitness.parserTasksBoundarySize
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
  let outerCertificate :=
    compactAdditiveProductSplitExplicitHybridCertificateOfGraph tokenCount
      coordinates.start coordinates.parserFinish coordinates.finish houter
  let parserProof :=
    compileCompactUnifiedParserStateCoreFullyUniformDirectFixed tokenTable
      width tokenCount coordinates.parser sizeWitness.parser hparser
      numericBound bitBound hwidthBound htokenCount hparserTokensCount
      hparserTasksCount htokenTableSize hparserTokensTableSize
      hparserTasksTableSize hnumericSize
  let outputLayoutRaw :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      outputLayoutData.bodyStart numericBound bitBound
      outputLayoutData.bodyStart_le_tokenCount outputLayoutData.header
      outputLayoutData.boundaryFinish_le_tokenCount
      outputLayoutData.boundaryStartEntry
      outputLayoutData.boundaryFinishEntry outputLayoutData.rows htokenCount
      houtputCount houtputTableSize hnumericSize
  let outputRowsRaw :=
    compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph
      tokenCount coordinates.outputCount coordinates.outputBoundary
      numericBound bitBound houtputRows htokenCount houtputCount
      houtputTableSize hnumericSize
  let outputSizeCertificate := compactNatSizeExplicitHybridCertificateOfEq
    sizeWitness.outputBoundarySize coordinates.outputBoundary houtputSize
  let outputAreaCertificate := boundaryAreaCertificate
    sizeWitness.outputBoundarySize coordinates.outputCount tokenCount
      houtputArea
  let outerResource := productSplitFixedPayloadPolynomial bitBound
  let parserResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let outputLayoutResource :=
    compactAdditiveStructuredListLayoutUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let outputRowsResource :=
    unitBoundaryUniformDirectUniversalFixedPayloadPolynomial numericBound
      bitBound
  let outputSizeResource := compactNatSizeFixedPayloadPolynomial bitBound
  let outputAreaResource := parserAreaFixedPayloadPolynomial bitBound
  let syntaxResource :=
    compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
      numericBound bitBound
  have hfinishBound : coordinates.finish <= numericBound :=
    houter.2.2.trans htokenCount
  have hstartBound : coordinates.start <= numericBound :=
    (Nat.le_of_lt houter.1).trans
      ((Nat.le_of_lt houter.2.1).trans hfinishBound)
  have hparserFinishBound : coordinates.parserFinish <= numericBound :=
    (Nat.le_of_lt houter.2.1).trans hfinishBound
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstartSize : Nat.size coordinates.start <= bitBound :=
    (Nat.size_le_size hstartBound).trans hnumericSize
  have hparserFinishSize : Nat.size coordinates.parserFinish <= bitBound :=
    (Nat.size_le_size hparserFinishBound).trans hnumericSize
  have hfinishSize : Nat.size coordinates.finish <= bitBound :=
    (Nat.size_le_size hfinishBound).trans hnumericSize
  have houterProof : outerCertificate.compile.payloadLength <= outerResource :=
    compactAdditiveProductSplitExplicitHybridCertificate_payloadLength_le_fixed
      tokenCount coordinates.start coordinates.parserFinish
      coordinates.finish bitBound houter htokenCountSize hstartSize
      hparserFinishSize hfinishSize
  have hparserProof : parserProof.payloadLength <= parserResource := by
    simpa only [parserProof, parserResource] using
      compileCompactUnifiedParserStateCoreFullyUniformDirectFixed_payloadLength_le
        tokenTable width tokenCount coordinates.parser sizeWitness.parser
        hparser numericBound bitBound hwidthBound htokenCount
        hparserTokensCount hparserTasksCount htokenTableSize
        hparserTokensTableSize hparserTasksTableSize hnumericSize
  have houtputLayoutProof : outputLayoutRaw.payloadLength <=
      outputLayoutResource :=
    compileCompactAdditiveStructuredListLayoutUniformDirectClosedContext_payloadLength_le_fixed
      tokenTable width tokenCount coordinates.parserFinish
      coordinates.outputCount coordinates.finish coordinates.outputBoundary
      outputLayoutData.bodyStart numericBound bitBound
      outputLayoutData.bodyStart_le_tokenCount outputLayoutData.header
      outputLayoutData.boundaryFinish_le_tokenCount
      outputLayoutData.boundaryStartEntry
      outputLayoutData.boundaryFinishEntry outputLayoutData.rows hwidthBound
      htokenCount houtputCount htokenTableSize houtputTableSize hnumericSize
  have houtputRowsProof : outputRowsRaw.payloadLength <= outputRowsResource :=
    (compileCompactAdditiveUnitBoundaryRowsUniformDirectClosedContextOfGraph_payloadLength_le
      tokenCount coordinates.outputCount coordinates.outputBoundary
      numericBound bitBound houtputRows htokenCount houtputCount
      houtputTableSize hnumericSize).trans
      (compactAdditiveUnitBoundaryRowsUniformDirectUniversalResource_le_fixed
        tokenCount coordinates.outputCount coordinates.outputBoundary
        numericBound bitBound htokenCount houtputCount houtputTableSize
        hnumericSize)
  have houtputSizeProof : outputSizeCertificate.compile.payloadLength <=
      outputSizeResource :=
    (compile_payloadLength_le_structuralPayloadBound
      outputSizeCertificate).trans
      ((compactNatSizeExplicitHybridCertificate_structuralPayloadBound_le_public
        sizeWitness.outputBoundarySize coordinates.outputBoundary
        houtputSize).trans
        (compactNatSizeStructuralPayloadPolynomial_le_fixed
          sizeWitness.outputBoundarySize coordinates.outputBoundary bitBound
          houtputSize houtputTableSize))
  have houtputAreaProof : outputAreaCertificate.compile.payloadLength <=
      outputAreaResource :=
    (compile_payloadLength_le_structuralPayloadBound
      outputAreaCertificate).trans
      ((boundaryAreaCertificate_structuralPayloadBound_le_public
        sizeWitness.outputBoundarySize coordinates.outputCount tokenCount
        houtputArea).trans
        (boundaryAreaStructuralPayloadPolynomial_le_fixed
          sizeWitness.outputBoundarySize coordinates.outputCount tokenCount
          coordinates.outputBoundary numericBound bitBound houtputSize
          htokenCount houtputCount houtputTableSize hnumericSize))
  have houterClosed : outerFormula.freeVariables = ∅ := by
    simpa only [outerFormula] using
      productSplitClosedFormula_freeVariables_eq_empty tokenCount
        coordinates.start coordinates.parserFinish coordinates.finish
  have hparserClosed : parserFormula.freeVariables = ∅ := by
    simpa only [parserFormula] using
      compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount coordinates.start
        coordinates.parserFinish coordinates.parserTokensFinish
        coordinates.parserTasksFinish coordinates.parserTokensBoundary
        coordinates.parserTokensCount coordinates.parserTasksBoundary
        coordinates.parserTasksCount sizeWitness.parserTokensBoundarySize
        sizeWitness.parserTasksBoundarySize
  have houtputLayoutClosed : outputLayoutFormula.freeVariables = ∅ := by
    simpa only [outputLayoutFormula] using
      compactAdditiveStructuredListLayoutClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount coordinates.parserFinish
        coordinates.outputCount coordinates.finish coordinates.outputBoundary
  have houtputRowsClosed : outputRowsFormula.freeVariables = ∅ := by
    simpa only [outputRowsFormula] using
      compactAdditiveUnitBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount coordinates.outputCount coordinates.outputBoundary
  have houtputSizeClosed : outputSizeFormula.freeVariables = ∅ := by
    simpa only [outputSizeFormula] using
      natSizeClosedFormula_freeVariables_eq_empty sizeWitness.outputBoundarySize
        coordinates.outputBoundary
  have houtputAreaClosed : outputAreaFormula.freeVariables = ∅ := by
    simpa only [outputAreaFormula] using
      parserAreaFormula_freeVariables_eq_empty sizeWitness.outputBoundarySize
        coordinates.outputCount tokenCount
  let outerBound := fixedClosedDirectFormulaBoundOfProof
    outerCertificate.compile outerResource houterProof houterClosed
  let parserBound := fixedClosedDirectFormulaBoundOfEmptyProof parserProof
    parserResource hparserProof hparserClosed
  let outputLayoutBound := fixedClosedDirectFormulaBoundOfEmptyProof
    outputLayoutRaw outputLayoutResource houtputLayoutProof
      houtputLayoutClosed
  let outputRowsBound := fixedClosedDirectFormulaBoundOfEmptyProof outputRowsRaw
    outputRowsResource houtputRowsProof houtputRowsClosed
  let outputSizeBound := fixedClosedDirectFormulaBoundOfProof
    outputSizeCertificate.compile outputSizeResource houtputSizeProof
      houtputSizeClosed
  let outputAreaBound := fixedClosedDirectFormulaBoundOfProof
    outputAreaCertificate.compile outputAreaResource houtputAreaProof
      houtputAreaClosed
  have hpositive : 1 <= syntaxResource := by
    dsimp only [syntaxResource]
    unfold
      compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
    omega
  let outputSizeAreaFormula := outputSizeFormula ⋏ outputAreaFormula
  let outputSizeAreaResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource outputSizeResource outputAreaResource
  let outputSizeAreaCode := outputSizeResource + outputAreaResource +
    (binaryNatCode 4).length
  let outputSizeAreaBound : FixedClosedDirectFormulaBound
      outputSizeAreaFormula outputSizeAreaResource outputSizeAreaCode :=
    FixedClosedDirectFormulaBound.conjunction outputSizeBound outputAreaBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, outputSizeResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let outputRowsTailFormula := outputRowsFormula ⋏ outputSizeAreaFormula
  let outputRowsTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource outputRowsResource outputSizeAreaResource
  let outputRowsTailCode := outputRowsResource + outputSizeAreaCode +
    (binaryNatCode 4).length
  let outputRowsTailBound : FixedClosedDirectFormulaBound
      outputRowsTailFormula outputRowsTailResource outputRowsTailCode :=
    FixedClosedDirectFormulaBound.conjunction outputRowsBound
      outputSizeAreaBound syntaxResource hpositive (by
        dsimp only [syntaxResource, outputRowsResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputSizeAreaCode, outputSizeResource,
          outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputRowsResource, outputSizeAreaCode,
          outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let outputLayoutTailFormula :=
    outputLayoutFormula ⋏ outputRowsTailFormula
  let outputLayoutTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource outputLayoutResource outputRowsTailResource
  let outputLayoutTailCode := outputLayoutResource + outputRowsTailCode +
    (binaryNatCode 4).length
  let outputLayoutTailBound : FixedClosedDirectFormulaBound
      outputLayoutTailFormula outputLayoutTailResource
      outputLayoutTailCode :=
    FixedClosedDirectFormulaBound.conjunction outputLayoutBound
      outputRowsTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, outputLayoutResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputRowsTailCode, outputRowsResource,
          outputSizeAreaCode, outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputLayoutResource,
          outputRowsTailCode, outputRowsResource, outputSizeAreaCode,
          outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let parserTailFormula := parserFormula ⋏ outputLayoutTailFormula
  let parserTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource parserResource outputLayoutTailResource
  let parserTailCode := parserResource + outputLayoutTailCode +
    (binaryNatCode 4).length
  let parserTailBound : FixedClosedDirectFormulaBound parserTailFormula
      parserTailResource parserTailCode :=
    FixedClosedDirectFormulaBound.conjunction parserBound
      outputLayoutTailBound syntaxResource hpositive (by
        dsimp only [syntaxResource, parserResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outputLayoutTailCode,
          outputLayoutResource, outputRowsTailCode, outputRowsResource,
          outputSizeAreaCode, outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, parserResource, outputLayoutTailCode,
          outputLayoutResource, outputRowsTailCode, outputRowsResource,
          outputSizeAreaCode, outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let partsFormula := outerFormula ⋏ parserTailFormula
  let partsResource := hybridConjunctionGeneralPayloadEnvelope syntaxResource
    outerResource parserTailResource
  let partsCode := outerResource + parserTailCode +
    (binaryNatCode 4).length
  let partsBound : FixedClosedDirectFormulaBound partsFormula partsResource
      partsCode :=
    FixedClosedDirectFormulaBound.conjunction outerBound parserTailBound
      syntaxResource hpositive (by
        dsimp only [syntaxResource, outerResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, parserTailCode, parserResource,
          outputLayoutTailCode, outputLayoutResource, outputRowsTailCode,
          outputRowsResource, outputSizeAreaCode, outputSizeResource,
          outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega) (by
        dsimp only [syntaxResource, outerResource, parserTailCode,
          parserResource, outputLayoutTailCode, outputLayoutResource,
          outputRowsTailCode, outputRowsResource, outputSizeAreaCode,
          outputSizeResource, outputAreaResource]
        unfold
          compactFormulaTransformStateCoreFullyUniformDirectAssemblySyntaxPolynomial
        omega)
  let closedFormula := compactFormulaTransformStateCoreClosedFormula
    tokenTable width tokenCount coordinates sizeWitness
  let explicitFormula := compactFormulaTransformStateCoreExplicitFormula
    tokenTable width tokenCount coordinates sizeWitness
  have hpartsFormula : partsFormula = explicitFormula := by
    rfl
  let explicitProof := CertifiedPAContextProof.cast hpartsFormula
    partsBound.proof
  have hformula : explicitFormula = closedFormula :=
    (compactFormulaTransformStateCoreClosedFormula_alignment tokenTable width
      tokenCount coordinates sizeWitness).symm
  let formulaProof := CertifiedPAContextProof.cast hformula explicitProof
  have hcontext : valuationContext partsFormula.freeVariables
      parserFixedZeroValuation = (∅ : Finset ValuationFormula) := by
    rw [partsBound.closed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext formulaProof
  refine { proof := proof, payloadLength_le := ?_ }
  change proof.payloadLength <= _
  have hexplicitProofLength : explicitProof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [explicitProof]
    exact CertifiedPAContextProof.cast_payloadLength hpartsFormula
      partsBound.proof
  have hformulaProofLength : formulaProof.payloadLength =
      partsBound.proof.payloadLength := by
    dsimp only [formulaProof]
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact hexplicitProofLength
  have hproofLength : proof.payloadLength = partsBound.proof.payloadLength := by
    dsimp only [proof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact hformulaProofLength
  rw [hproofLength]
  apply partsBound.payloadLength_le.trans
  dsimp only [partsResource, parserTailResource, outputLayoutTailResource,
    outputRowsTailResource, outputSizeAreaResource, outerResource,
    parserResource, outputLayoutResource, outputRowsResource,
    outputSizeResource, outputAreaResource, syntaxResource]
  unfold hybridConjunctionGeneralPayloadEnvelope
    compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
  dsimp only
  omega

noncomputable def compileCompactFormulaTransformStateCoreFullyUniformDirectFixed
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hparserTokensCount : coordinates.parserTokensCount <= numericBound)
    (hparserTasksCount : coordinates.parserTasksCount <= numericBound)
    (houtputCount : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hparserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputTableSize : Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :=
  (compactFormulaTransformStateCoreFullyUniformDirectFixedBound tokenTable
    width tokenCount coordinates sizeWitness hgraph numericBound bitBound
    hwidthBound htokenCount hparserTokensCount hparserTasksCount houtputCount
    htokenTableSize hparserTokensTableSize hparserTasksTableSize
    houtputTableSize hnumericSize).proof

theorem
    compileCompactFormulaTransformStateCoreFullyUniformDirectFixed_payloadLength_le
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (numericBound bitBound : Nat)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hparserTokensCount : coordinates.parserTokensCount <= numericBound)
    (hparserTasksCount : coordinates.parserTasksCount <= numericBound)
    (houtputCount : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hparserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputTableSize : Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactFormulaTransformStateCoreFullyUniformDirectFixed
      tokenTable width tokenCount coordinates sizeWitness hgraph numericBound
      bitBound hwidthBound htokenCount hparserTokensCount hparserTasksCount
      houtputCount htokenTableSize hparserTokensTableSize
      hparserTasksTableSize houtputTableSize hnumericSize).payloadLength <=
      compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
        numericBound bitBound :=
  (compactFormulaTransformStateCoreFullyUniformDirectFixedBound tokenTable
    width tokenCount coordinates sizeWitness hgraph numericBound bitBound
    hwidthBound htokenCount hparserTokensCount hparserTasksCount houtputCount
    htokenTableSize hparserTokensTableSize hparserTasksTableSize
    houtputTableSize hnumericSize).payloadLength_le

#print axioms compactFormulaTransformStateCoreFullyUniformDirectFixedBound
#print axioms
  compileCompactFormulaTransformStateCoreFullyUniformDirectFixed_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStateCoreFullyUniformDirectFixedBounds
