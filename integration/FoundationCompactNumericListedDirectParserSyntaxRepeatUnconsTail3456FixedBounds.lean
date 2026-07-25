import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456Certificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds

/-! # Fully fixed Repeat uncons tail: TripleBoundary and Tail456 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456FixedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsPublicBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456Certificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

def parserSyntaxRepeatUnconsTail3456PayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
        bitBound)
      (parserSyntaxRepeatUnconsTail456PayloadPolynomial tokenCount numericBound
        bitBound))
    (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
      bitBound)
    (parserSyntaxRepeatUnconsTail456PayloadPolynomial tokenCount numericBound
      bitBound)

theorem
    parserSyntaxRepeatUnconsTail3456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount tailBoundary tailCount sourceBoundary
      sourceCount tailBoundarySize binderArity repeatCount numericBound
      bitBound : Nat)
    (htriple : CompactAdditiveTripleBoundaryRows tokenCount tailCount
      tailBoundary)
    (hcons : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount 2 binderArity
      repeatCount)
    (hsize : tailBoundarySize = Nat.size tailBoundary)
    (harea : tailBoundarySize <= (tailCount + 1) * tokenCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htailCount : tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htailBoundarySize : Nat.size tailBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hrepeatSize : Nat.size repeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (parserSyntaxRepeatUnconsTail3456Certificate tokenTable width tokenCount
          tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
          binderArity repeatCount htriple hcons hsize harea) <=
      parserSyntaxRepeatUnconsTail3456PayloadPolynomial tokenCount numericBound
        bitBound := by
  let tripleCertificate :=
    compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
      tokenCount tailCount tailBoundary htriple
  let tailCertificate :=
    parserSyntaxRepeatUnconsTail456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity repeatCount hcons hsize harea
  let tripleFormula :=
    compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
      tailBoundary
  let tailFormula :=
    parserSyntaxRepeatUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity
        repeatCount ⋏
      parserSyntaxRepeatUnconsTail56Formula tailBoundarySize tailBoundary
        tailCount tokenCount
  let tripleResource :=
    tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
      bitBound
  let tailResource :=
    parserSyntaxRepeatUnconsTail456PayloadPolynomial tokenCount numericBound
      bitBound
  have htripleResource :
      hybridFormulaStructuralPayloadBound tripleCertificate <=
        tripleResource := by
    exact
      (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
        tokenCount tailCount tailBoundary htriple).trans
      (compactAdditiveTripleBoundaryRowsGraphStructuralPayloadEnvelope_le_fullyFixed
        tokenCount tailCount tailBoundary numericBound bitBound htriple
        htokenCount htailCount htailBoundarySize hnumericSize)
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    simpa only [tailCertificate, tailResource] using
      parserSyntaxRepeatUnconsTail456Certificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount tailBoundarySize binderArity repeatCount numericBound
        bitBound hcons hsize harea hwidth htokenCount hsourceCount htailCount
        htokenTableSize hsourceBoundarySize htailBoundarySize hbinderSize
        hrepeatSize hnumericSize
  have htripleClosed : tripleFormula.freeVariables = ∅ := by
    simpa only [tripleFormula] using
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount tailCount tailBoundary
  have htailClosed : tailFormula.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    rw [show
      (parserSyntaxRepeatUnconsTail456ConsFormula tokenTable width tokenCount
        tailBoundary tailCount sourceBoundary sourceCount binderArity
        repeatCount).freeVariables = ∅ by
      simpa only [parserSyntaxRepeatUnconsTail456ConsFormula] using
        taskConsFunctionFormula_freeVariables_eq_empty tokenTable width
          tokenCount tailBoundary tailCount sourceBoundary sourceCount
          binderArity repeatCount]
    unfold parserSyntaxRepeatUnconsTail56Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      natSizeClosedFormula_freeVariables_eq_empty,
      parserAreaFormula_freeVariables_eq_empty]
    simp
  have hpair :=
    closedPairCertificate_structuralPayloadBound_le_fixed
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      tripleFormula tailFormula tripleCertificate tailCertificate
      tripleResource tailResource htripleClosed htailClosed htripleResource
      htailResource
  unfold parserSyntaxRepeatUnconsTail3456Certificate
    parserSyntaxRepeatUnconsTail3456PayloadPolynomial
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        tripleCertificate tailCertificate) <=
    hybridConjunctionGeneralPayloadEnvelope
      (repeatClosedPairSyntaxResource tripleResource tailResource)
      tripleResource tailResource
  exact hpair

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456FixedBounds
