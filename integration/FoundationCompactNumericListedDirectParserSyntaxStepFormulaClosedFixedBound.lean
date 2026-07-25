import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

/-! # Closed fixed SyntaxStep bound: formula branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxStepFormulaClosedFixedBound

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaTaskFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanFormulaBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

noncomputable def compactUnifiedParserSyntaxStepFormulaClosedFixedBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next witness.slot0 witness.formula) :
    ExplicitDirectFormulaBound compactUnifiedParserSyntaxStepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepFormulaClosedFixedResource tokenCount numericBound bitBound) := by
  let certificate :=
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
      width tokenCount current next witness (.formula hgraph)
  let proof := certificate.compile
  have hstruct :=
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromFormulaData_structuralPayloadBound_le_closedFixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph context.width_le context.tokenCount_le context.currentValue
      context.nextValue context.tokenTableSize context.currentSize
      context.nextSize
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
          compactSyntaxFormulaTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (1 : Fin 7))
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (0 : Fin 7))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
          compactSyntaxFormulaTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (5 : Fin 7))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
          compactSyntaxFormulaTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (6 : Fin 7))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.formula,
          compactSyntaxFormulaTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (4 : Fin 7))
      context.numericSize context.bitPositive context.stepSize
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      certificate).trans (by
        simpa only [certificate, syntaxStepFormulaClosedFixedResource] using
          hstruct)

end FoundationCompactNumericListedDirectParserSyntaxStepFormulaClosedFixedBound
