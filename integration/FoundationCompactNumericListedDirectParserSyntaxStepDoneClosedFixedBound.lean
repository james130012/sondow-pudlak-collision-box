import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

/-! # Closed fixed SyntaxStep bound: done branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxStepDoneClosedFixedBound

open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepDoneDirectSelectedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

noncomputable def compactUnifiedParserSyntaxStepDoneClosedFixedBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness.done) :
    ExplicitDirectFormulaBound compactUnifiedParserSyntaxStepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepDoneClosedFixedResource numericBound bitBound) := by
  let proof :=
    compileCompactUnifiedParserSyntaxStepFromDoneDirectContext tokenTable width
      tokenCount current next witness numericBound bitBound hgraph
      context.tokenCount_le
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
          compactUnifiedParserDoneWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessValue (6 : Fin 7))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
          compactUnifiedParserDoneWitnessCoordinatesOf,
          compactUnifiedParserDoneWitnessCoordinateValues,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (1 : Fin 7))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
          compactUnifiedParserDoneWitnessCoordinatesOf,
          compactUnifiedParserDoneWitnessCoordinateValues,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (4 : Fin 7))
      context.numericSize
  have hbound :=
    compileCompactUnifiedParserSyntaxStepFromDoneDirectContext_payloadLength_le_closedFixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph context.width_le context.tokenCount_le
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.done,
          compactUnifiedParserDoneWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessValue (6 : Fin 7))
      context.currentValue context.nextValue context.tokenTableSize
      context.currentSize context.nextSize context.doneWitnessSize
      context.numericSize context.bitPositive context.stepSize
  refine ⟨proof, ?_⟩
  simpa only [proof, syntaxStepDoneClosedFixedResource] using hbound

end FoundationCompactNumericListedDirectParserSyntaxStepDoneClosedFixedBound
