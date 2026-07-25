import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456Certificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds

/-! # Fully fixed Repeat uncons tail: DropOne and Tail3456 -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456FixedBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsUniformDirectCompiler
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail456Certificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456Certificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail3456FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456Certificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

def parserSyntaxRepeatUnconsTail23456PayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (parserSyntaxRepeatUnconsTail3456PayloadPolynomial tokenCount
        numericBound bitBound))
    (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
    (parserSyntaxRepeatUnconsTail3456PayloadPolynomial tokenCount numericBound
      bitBound)

theorem parserSyntaxRepeatUnconsTail23456Formula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat) :
    (parserSyntaxRepeatUnconsTail23456Formula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount).freeVariables = ∅ := by
  unfold parserSyntaxRepeatUnconsTail23456Formula
    parserSyntaxRepeatUnconsTail3456Formula
  rw [LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty]
  rw [LO.FirstOrder.Semiformula.freeVariables_and]
  rw [show
    (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
      tailBoundary).freeVariables = ∅ by
    exact
      compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
        tokenCount tailCount tailBoundary]
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

theorem
    parserSyntaxRepeatUnconsTail23456Certificate_structuralPayloadBound_le_fixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount numericBound
      bitBound : Nat)
    (hdrop : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount 1)
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
        (parserSyntaxRepeatUnconsTail23456Certificate tokenTable width
          tokenCount sourceBoundary sourceCount tailBoundary tailCount
          tailBoundarySize binderArity repeatCount hdrop htriple hcons hsize
          harea) <=
      parserSyntaxRepeatUnconsTail23456PayloadPolynomial tokenCount numericBound
        bitBound := by
  let dropCertificate :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop
  let tailCertificate :=
    parserSyntaxRepeatUnconsTail3456Certificate tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity repeatCount htriple hcons hsize harea
  let dropFormula :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable
      width tokenCount sourceBoundary sourceCount tailBoundary tailCount 1
  let tailFormula :=
    parserSyntaxRepeatUnconsTail3456Formula tokenTable width tokenCount
      tailBoundary tailCount sourceBoundary sourceCount tailBoundarySize
      binderArity repeatCount
  let dropResource :=
    taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound
  let tailResource :=
    parserSyntaxRepeatUnconsTail3456PayloadPolynomial tokenCount numericBound
      bitBound
  have hdropResource :
      hybridFormulaStructuralPayloadBound dropCertificate <= dropResource :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount 1 hdrop).trans
    (compactAdditiveSyntaxTaskListDropOneRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount numericBound bitBound hdrop hwidth htokenCount hsourceCount
      htokenTableSize hsourceBoundarySize htailBoundarySize hnumericSize)
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    simpa only [tailCertificate, tailResource] using
      parserSyntaxRepeatUnconsTail3456Certificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount tailBoundary tailCount sourceBoundary
        sourceCount tailBoundarySize binderArity repeatCount numericBound
        bitBound htriple hcons hsize harea hwidth htokenCount hsourceCount
        htailCount htokenTableSize hsourceBoundarySize htailBoundarySize
        hbinderSize hrepeatSize hnumericSize
  have hdropClosed : dropFormula.freeVariables = ∅ := by
    simpa only [dropFormula] using
      compactAdditiveSyntaxTaskListDropOneRowsClosedFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount
  have htailClosed : tailFormula.freeVariables = ∅ := by
    unfold tailFormula parserSyntaxRepeatUnconsTail3456Formula
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    rw [show
      (compactAdditiveTripleBoundaryRowsClosedFormula tokenCount tailCount
        tailBoundary).freeVariables = ∅ by
      exact
        compactAdditiveTripleBoundaryRowsClosedFormula_freeVariables_eq_empty
          tokenCount tailCount tailBoundary]
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
      dropFormula tailFormula dropCertificate tailCertificate dropResource
      tailResource hdropClosed htailClosed hdropResource htailResource
  unfold parserSyntaxRepeatUnconsTail23456Certificate
    parserSyntaxRepeatUnconsTail23456PayloadPolynomial
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        dropCertificate tailCertificate) <=
    hybridConjunctionGeneralPayloadEnvelope
      (repeatClosedPairSyntaxResource dropResource tailResource)
      dropResource tailResource
  exact hpair

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456FixedBounds
