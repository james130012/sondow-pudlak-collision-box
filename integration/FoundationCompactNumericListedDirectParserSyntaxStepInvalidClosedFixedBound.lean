import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

/-! # Closed fixed SyntaxStep bound: invalid branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxStepInvalidClosedFixedBound

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidFormula
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanGraphCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCleanInvalidBranchFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

noncomputable def compactUnifiedParserSyntaxStepInvalidClosedFixedBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current next witness.invalid) :
    ExplicitDirectFormulaBound compactUnifiedParserSyntaxStepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepInvalidClosedFixedResource tokenCount numericBound bitBound) := by
  let certificate :=
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromData tokenTable
      width tokenCount current next witness (.invalid hgraph)
  let proof := certificate.compile
  have hstruct :=
    compactUnifiedParserSyntaxStepCleanHybridCertificateFromInvalidData_structuralPayloadBound_le_closedFixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph context.width_le context.width_le_bit context.tokenCount_le
      context.currentValue context.nextValue context.tokenTableSize
      context.currentSize context.nextSize
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.invalid,
          compactSyntaxInvalidTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (0 : Fin 7))
      context.numericSize context.bitPositive context.stepSize
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      certificate).trans (by
        simpa only [certificate, syntaxStepInvalidClosedFixedResource] using
          hstruct)

end FoundationCompactNumericListedDirectParserSyntaxStepInvalidClosedFixedBound
