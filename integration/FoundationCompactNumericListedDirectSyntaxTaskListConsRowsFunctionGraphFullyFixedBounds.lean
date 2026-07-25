import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate

/-! # Fully fixed graph certificate for function ConsRows syntax -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphCertificate

theorem
    taskConsFunctionGraphCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity functionArity numericBound bitBound : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 2 binderArity
      functionArity)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htargetCount : targetCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (functionConsCertificateOfGraph tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount binderArity
          functionArity hcons) <=
      taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  unfold functionConsCertificateOfGraph
  exact taskConsFunctionCertificate_structuralPayloadBound_le_fullyFixed
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount binderArity functionArity numericBound bitBound hwidth
    htokenCount htargetCount htokenTableSize hsourceBoundarySize
    htargetBoundarySize hbinderSize hfunctionSize hnumericSize hcons.1
    (functionConsHeadDataOfGraph tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount binderArity functionArity hcons)
    (functionConsTailRowsOfGraph tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount binderArity functionArity hcons)

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionGraphFullyFixedBounds
