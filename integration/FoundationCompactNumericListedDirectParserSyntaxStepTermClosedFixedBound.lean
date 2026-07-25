import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

/-! # Closed fixed SyntaxStep bound: term branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxStepTermClosedFixedBound

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepTermGraphFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase

noncomputable def compactUnifiedParserSyntaxStepTermClosedFixedBound
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserSyntaxStepWitnessCoordinates)
    (numericBound bitBound : Nat)
    (context :
      CompactUnifiedParserSyntaxStepClosedFixedContext tokenTable width
        tokenCount current next witness numericBound bitBound)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next witness.slot0 witness.term) :
    ExplicitDirectFormulaBound compactUnifiedParserSyntaxStepZeroValuation
      (compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
        current next witness)
      (syntaxStepTermClosedFixedResource tokenCount numericBound bitBound) := by
  let certificate :=
    compactUnifiedParserSyntaxStepCertificateFromTermGraph tokenTable width
      tokenCount current next witness hgraph
  let proof := certificate.compile
  have hstruct :=
    compactUnifiedParserSyntaxStepCertificateFromTermGraph_structuralPayloadBound_le_closedFixed
      tokenTable width tokenCount current next witness numericBound bitBound
      hgraph context.width_le context.tokenCount_le context.currentValue
      context.nextValue context.tokenTableSize context.widthSize
      context.tokenCountSize context.currentSize context.nextSize
      (by
        simpa [FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds.compactUnifiedParserSyntaxStepWitnessCoordinateValues] using
          context.witnessSize (0 : Fin 7))
      context.termWitnessSize context.numericSize context.bitPositive
      context.stepSize
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      certificate).trans (by
        simpa only [certificate, syntaxStepTermClosedFixedResource] using
          hstruct)

end FoundationCompactNumericListedDirectParserSyntaxStepTermClosedFixedBound
