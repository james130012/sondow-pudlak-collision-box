import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

/-! # Closed fixed SyntaxStep bound: empty branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxStepEmptyClosedFixedBound

open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepEmptyDirectSelectedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

noncomputable def compactUnifiedParserSyntaxStepEmptyClosedFixedBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound)
    (hgraph : CompactUnifiedParserEmptyGraphRows tokenTable width tokenCount
      current next witness.empty) :
    ExplicitDirectFormulaBound compactUnifiedParserSyntaxStepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepEmptyClosedFixedResource numericBound bitBound) := by
  let proof :=
    compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext tokenTable width
      tokenCount current next witness numericBound bitBound hgraph
      context.tokenCount_le
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentValue (5 : Fin 8))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.empty,
          compactUnifiedParserEmptyWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (1 : Fin 7))
      context.numericSize
  have hbound :=
    compileCompactUnifiedParserSyntaxStepFromEmptyDirectContext_payloadLength_le_closedFixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph context.width_le context.tokenCount_le context.currentValue
      context.nextValue context.tokenTableSize context.currentSize
      context.nextSize
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.empty,
          compactUnifiedParserEmptyWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (1 : Fin 7))
      context.numericSize context.bitPositive context.stepSize
  refine ⟨proof, ?_⟩
  simpa only [proof, syntaxStepEmptyClosedFixedResource] using hbound

end FoundationCompactNumericListedDirectParserSyntaxStepEmptyClosedFixedBound
