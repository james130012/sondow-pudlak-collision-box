import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds

/-! # Fully fixed exact function-task uncons certificate for Repeat -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullyFixedBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456Certificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsTail23456FixedBounds
open FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullCertificate
open FoundationCompactNumericListedDirectParserSyntaxRepeatClosedPairFixedBounds

def parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (repeatClosedPairSyntaxResource
      (unconsPositiveFullyFixedPayloadPolynomial bitBound)
      (parserSyntaxRepeatUnconsTail23456PayloadPolynomial tokenCount
        numericBound bitBound))
    (unconsPositiveFullyFixedPayloadPolynomial bitBound)
    (parserSyntaxRepeatUnconsTail23456PayloadPolynomial tokenCount numericBound
      bitBound)

theorem
    parserSyntaxRepeatUnconsFullCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount numericBound
      bitBound : Nat)
    (hpositive : 0 < sourceCount)
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
        (parserSyntaxRepeatUnconsFullCertificate tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          binderArity repeatCount hpositive hdrop htriple hcons hsize harea) <=
      parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  let positiveCertificate := closedPositiveCertificate sourceCount hpositive
  let tailCertificate :=
    parserSyntaxRepeatUnconsTail23456Certificate tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount hdrop htriple hcons hsize harea
  let positiveFormula : ValuationFormula :=
    “0 < !!(shortBinaryNumeralTerm sourceCount)”
  let tailFormula :=
    parserSyntaxRepeatUnconsTail23456Formula tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount
  let positiveResource := unconsPositiveFullyFixedPayloadPolynomial bitBound
  let tailResource :=
    parserSyntaxRepeatUnconsTail23456PayloadPolynomial tokenCount numericBound
      bitBound
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have hpositiveResource :
      hybridFormulaStructuralPayloadBound positiveCertificate <=
        positiveResource :=
    (closedPositiveCertificate_structuralPayloadBound_le_public sourceCount
      hpositive).trans
    (compactAdditiveSyntaxTaskListUnconsRowsPositivePayloadPolynomial_le_fullyFixed
      sourceCount bitBound hsourceCountSize)
  have htailResource :
      hybridFormulaStructuralPayloadBound tailCertificate <= tailResource := by
    simpa only [tailCertificate, tailResource] using
      parserSyntaxRepeatUnconsTail23456Certificate_structuralPayloadBound_le_fixed
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize binderArity repeatCount numericBound
        bitBound hdrop htriple hcons hsize harea hwidth htokenCount
        hsourceCount htailCount htokenTableSize hsourceBoundarySize
        htailBoundarySize hbinderSize hrepeatSize hnumericSize
  have hpositiveClosed : positiveFormula.freeVariables = ∅ := by
    simp [positiveFormula, shortBinaryNumeralTerm_freeVariables_eq_empty,
      LO.FirstOrder.Semiterm.Operator.operator]
  have htailClosed : tailFormula.freeVariables = ∅ := by
    simpa only [tailFormula] using
      parserSyntaxRepeatUnconsTail23456Formula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize binderArity repeatCount
  have hpair :=
    closedPairCertificate_structuralPayloadBound_le_fixed
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      positiveFormula tailFormula positiveCertificate tailCertificate
      positiveResource tailResource hpositiveClosed htailClosed
      hpositiveResource htailResource
  unfold parserSyntaxRepeatUnconsFullCertificate
    parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        positiveCertificate tailCertificate) <=
    hybridConjunctionGeneralPayloadEnvelope
      (repeatClosedPairSyntaxResource positiveResource tailResource)
      positiveResource tailResource
  exact hpair

noncomputable def parserSyntaxRepeatUnconsGraphCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize 2 binderArity repeatCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadKindFormula
        tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
        tailCount tailBoundarySize binderArity repeatCount
        (FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          2)) :=
  CheckedHybridValuationBoundedFormulaCertificate.cast
    (parserSyntaxRepeatUnconsFullFormula_alignment tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount).symm
    (parserSyntaxRepeatUnconsFullCertificate tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      binderArity repeatCount hgraph.1 hgraph.2.1 hgraph.2.2.1
      hgraph.2.2.2.1 hgraph.2.2.2.2.1 hgraph.2.2.2.2.2)

theorem
    parserSyntaxRepeatUnconsGraphCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount numericBound
      bitBound : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListUnconsRowsWithSize tokenTable width
      tokenCount sourceBoundary sourceCount tailBoundary tailCount
      tailBoundarySize 2 binderArity repeatCount)
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
        (parserSyntaxRepeatUnconsGraphCertificate tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          binderArity repeatCount hgraph) <=
      parserSyntaxRepeatUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound := by
  unfold parserSyntaxRepeatUnconsGraphCertificate
  exact
    parserSyntaxRepeatUnconsFullCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount tailBoundary
      tailCount tailBoundarySize binderArity repeatCount numericBound bitBound
      hgraph.1 hgraph.2.1 hgraph.2.2.1 hgraph.2.2.2.1
      hgraph.2.2.2.2.1 hgraph.2.2.2.2.2 hwidth htokenCount hsourceCount
      htailCount htokenTableSize hsourceBoundarySize htailBoundarySize
      hbinderSize hrepeatSize hnumericSize

end FoundationCompactNumericListedDirectParserSyntaxRepeatUnconsFullyFixedBounds
