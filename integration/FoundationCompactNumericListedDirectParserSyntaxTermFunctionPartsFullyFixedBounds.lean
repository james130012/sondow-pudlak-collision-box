import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsTransparentBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionTransparentEnvelopeFullyFixedBounds

/-!
# Fully fixed bound for the assembled function syntax-term branches

The checked branch construction and the formula-assembly estimate are composed
here after being verified independently.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsTransparentBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionTransparentEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows

theorem
    syntaxTermFunctionPartsCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount binderArity functionArity numericBound bitBound :
      Nat)
    (hgraph : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next tailBoundary tailCount binderArity
      functionArity)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFunctionPartsCertificate tokenTable width tokenCount
          next.tasksFinish next.finish current.tokensBoundary
          current.tokensCount next.tokensBoundary next.tokensCount
          tailBoundary tailCount next.tasksBoundary next.tasksCount binderArity
          functionArity hgraph.1 hgraph.2.1 hgraph.2.2) <=
      syntaxTermFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have htailCountValue : tailCount <= numericBound := by
    rcases hgraph with ⟨_, _, htasks⟩
    unfold CompactAdditiveSyntaxTaskListConsRows at htasks
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    omega
  have htailCountSize : Nat.size tailCount <= bitBound :=
    (Nat.size_le_size htailCountValue).trans hnumericSize
  exact
    (syntaxTermFunctionPartsCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current next tailBoundary tailCount
      binderArity functionArity numericBound bitBound hgraph hwidth
      htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
      hnextSize htailBoundarySize hbinderSize hfunctionSize hnumericSize).trans
    (syntaxTermFunctionPartsTransparentEnvelope_le_fullyFixed tokenTable width
      tokenCount current next tailBoundary tailCount binderArity functionArity
      numericBound bitBound htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize htailCountSize hbinderSize
      hfunctionSize)

#print axioms
  syntaxTermFunctionPartsCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionPartsFullyFixedBounds
