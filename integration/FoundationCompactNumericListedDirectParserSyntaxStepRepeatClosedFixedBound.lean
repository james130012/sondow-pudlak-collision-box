import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

/-! # Closed fixed SyntaxStep bound: repeat branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxStepRepeatClosedFixedBound

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormula
open FoundationCompactNumericListedDirectParserSyntaxRepeatFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepRepeatGraphFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

noncomputable def compactUnifiedParserSyntaxStepRepeatClosedFixedBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound)
    (hgraph : CompactUnifiedParserSyntaxRepeatRows tokenTable width tokenCount
      current next witness.slot0 witness.slot1 witness.repeat) :
    ExplicitDirectFormulaBound compactUnifiedParserSyntaxStepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepRepeatClosedFixedResource tokenCount numericBound bitBound) := by
  let certificate :=
    compactUnifiedParserSyntaxStepCertificateFromRepeatGraph tokenTable width
      tokenCount current next witness hgraph
  let proof := certificate.compile
  have hrepeatSize :=
    compactUnifiedParserSyntaxRepeatFormulaEnvironmentOf_size_le tokenTable
      width tokenCount current next witness.slot0 witness.slot1 witness.repeat
      bitBound context.tokenTableSize context.widthSize context.tokenCountSize
      context.currentSize context.nextSize
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (0 : Fin 7))
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (1 : Fin 7))
      context.repeatWitnessSize
  have hstruct :=
    compactUnifiedParserSyntaxStepCertificateFromRepeatGraph_structuralPayloadBound_le_closedFixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph hrepeatSize context.width_le context.tokenCount_le
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentValue (3 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextValue (3 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentValue (5 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentValue (7 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextValue (7 : Fin 8))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
          compactSyntaxRepeatTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessValue (3 : Fin 7))
      context.tokenTableSize context.widthSize context.tokenCountSize
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentSize (3 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentSize (1 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextSize (3 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextSize (1 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentSize (4 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextSize (4 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.currentSize (6 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextSize (6 : Fin 8))
      (by
        simpa [compactUnifiedParserStateCoordinateValues] using
          context.nextSize (7 : Fin 8))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
          compactSyntaxRepeatTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (2 : Fin 7))
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (0 : Fin 7))
      (by
        simpa [compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (1 : Fin 7))
      (by
        simpa [CompactUnifiedParserSyntaxStepWitnessCoordinates.repeat,
          compactSyntaxRepeatTaskWitnessCoordinatesOf,
          compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (5 : Fin 7))
      context.numericSize context.stepSize
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      certificate).trans (by
        simpa only [certificate, syntaxStepRepeatClosedFixedResource] using
          hstruct)

end FoundationCompactNumericListedDirectParserSyntaxStepRepeatClosedFixedBound
