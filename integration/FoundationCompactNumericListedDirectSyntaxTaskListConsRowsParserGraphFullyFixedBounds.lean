import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds

/-! # Fully fixed original graph certificate for the parser ConsRows syntax -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private theorem termValue_parserFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (parserFixedNumeralTerm value) = value := by
  simp [parserFixedNumeralTerm,
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    termValue]

theorem
    taskConsParserGraphCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity numericBound bitBound : Nat)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 1 binderArity 0)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htargetCount : targetCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount 1 binderArity 0 (parserFixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
          (termValue_parserFixedNumeralTerm · 1)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_parserFixedNumeralTerm · 0) hcons) <=
      taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
  simpa only [
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph]
    using
    (taskConsParserCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity numericBound bitBound hwidth htokenCount
      htargetCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hbinderSize hnumericSize hcons.1
      (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount 1
        binderArity 0 hcons)
      (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount 1
        binderArity 0 hcons))

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserGraphFullyFixedBounds
