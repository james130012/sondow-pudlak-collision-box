import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate

/-!
# Fixed function-task branch for the syntax-term transition

The ConsRows graph is decomposed once into its genuine head datum and tail
rows, then discharged by the fully fixed function ConsRows certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchCertificate

theorem
    syntaxTermFunctionTaskCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount tailBoundary tailCount targetBoundary
      targetCount binderArity functionArity numericBound bitBound : Nat)
    (htasks : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount targetBoundary targetCount 2 binderArity
      functionArity)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htargetCount : targetCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFunctionTaskCertificate tokenTable width tokenCount
          tailBoundary tailCount targetBoundary targetCount binderArity
          functionArity htasks) <=
      taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  let headData :=
    compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
      tokenCount tailBoundary tailCount targetBoundary targetCount 2
      binderArity functionArity htasks
  let tailRows :=
    compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
      tokenCount tailBoundary tailCount targetBoundary targetCount 2
      binderArity functionArity htasks
  have hfromData :=
    taskConsFunctionCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount tailBoundary tailCount targetBoundary
      targetCount binderArity functionArity numericBound bitBound hwidth
      htokenCount htargetCount htokenTableSize htailBoundarySize
      htargetBoundarySize hbinderSize hfunctionSize hnumericSize htasks.1
      headData tailRows
  simpa only [
    syntaxTermFunctionTaskCertificate,
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph,
    headData, tailRows] using hfromData

#print axioms
  syntaxTermFunctionTaskCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionTaskBranchFullyFixedBounds
