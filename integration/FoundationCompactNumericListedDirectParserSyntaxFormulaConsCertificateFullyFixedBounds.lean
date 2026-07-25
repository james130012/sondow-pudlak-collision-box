import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds

/-! # Fully fixed named Cons certificate used by the parser Uncons tail -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaConsCertificateFullyFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsTail456Certificate

theorem parserSyntaxFormulaConsCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount binderArity numericBound bitBound : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 1 binderArity 0)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserSyntaxFormulaConsCertificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount binderArity
          hcons) <=
      taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
  unfold parserSyntaxFormulaConsCertificate
  exact taskConsParserGraphCertificate_structuralPayloadBound_le_fullyFixed
    tokenTable width tokenCount tailBoundary tailCount sourceBoundary
    sourceCount binderArity numericBound bitBound hcons hwidth htokenCount
    hsourceCount htokenTableSize htailBoundarySize hsourceBoundarySize
    hbinderSize hnumericSize

end FoundationCompactNumericListedDirectParserSyntaxFormulaConsCertificateFullyFixedBounds
