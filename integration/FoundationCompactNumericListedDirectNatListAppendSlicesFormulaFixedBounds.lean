import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fixed code and closedness for the full append-slices formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables

def appendSlicesClosedTerms
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    Fin 12 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm leftStart,
    shortBinaryNumeralTerm leftFinish,
    shortBinaryNumeralTerm leftCount,
    shortBinaryNumeralTerm rightStart,
    shortBinaryNumeralTerm rightFinish,
    shortBinaryNumeralTerm rightCount,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetFinish,
    shortBinaryNumeralTerm targetCount]

def appendSlicesFullFormulaCodePolynomial (bitBound : Nat) : Nat :=
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 12 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendSlicesDef.val
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0 termCode
    (binaryFormulaCode source).length

theorem compactAdditiveNatListAppendSlicesClosedFormula_code_length_le_fixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount bitBound : Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hleftStartSize : Nat.size leftStart <= bitBound)
    (hleftFinishSize : Nat.size leftFinish <= bitBound)
    (hleftCountSize : Nat.size leftCount <= bitBound)
    (hrightStartSize : Nat.size rightStart <= bitBound)
    (hrightFinishSize : Nat.size rightFinish <= bitBound)
    (hrightCountSize : Nat.size rightCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount)).length <=
      appendSlicesFullFormulaCodePolynomial bitBound := by
  let terms := appendSlicesClosedTerms tokenTable width tokenCount leftStart
    leftFinish leftCount rightStart rightFinish rightCount targetStart
    targetFinish targetCount
  let termCode := appendSourcePrefixCompositeTermCodePolynomial bitBound
  let source : LO.FirstOrder.ArithmeticSemiformula Nat 12 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAppendSlicesDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      simp only [terms, appendSlicesClosedTerms] <;>
      apply appendSourcePrefixShortNumeral_code_le <;> assumption
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveNatListAppendSlicesClosedFormula
    appendSlicesFullFormulaCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, termCode, source,
    appendSlicesClosedTerms] using hraw

theorem compactAdditiveNatListAppendSlicesExplicitFormula_closed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat) :
    (compactAdditiveNatListAppendSlicesExplicitFormula tokenTable width
      tokenCount leftStart leftFinish leftCount rightStart rightFinish
      rightCount targetStart targetFinish targetCount).freeVariables = ∅ := by
  rw [← compactAdditiveNatListAppendSlicesClosedFormula_alignment]
  unfold compactAdditiveNatListAppendSlicesClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

theorem
    compactAdditiveNatListAppendSlicesClosedFormula_code_length_le_fixed_of_graph
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hrightCountBound : rightCount <= numericBound)
    (htargetCountBound : targetCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount leftStart leftFinish leftCount rightStart rightFinish
        rightCount targetStart targetFinish targetCount)).length <=
      appendSlicesFullFormulaCodePolynomial bitBound := by
  have hleft := Classical.choose_spec hgraph.2.1
  have hright := Classical.choose_spec hgraph.2.2
  apply compactAdditiveNatListAppendSlicesClosedFormula_code_length_le_fixed
  · exact htableSize
  · exact (Nat.size_le_size hwidthBound).trans hnumericSize
  · exact (Nat.size_le_size htokenCountBound).trans hnumericSize
  · exact (Nat.size_le_size (show leftStart <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size (show leftFinish <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size (show leftCount <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size (show rightStart <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size (show rightFinish <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size hrightCountBound).trans
      hnumericSize
  · exact (Nat.size_le_size (show targetStart <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size (show targetFinish <= numericBound by omega)).trans
      hnumericSize
  · exact (Nat.size_le_size htargetCountBound).trans
      hnumericSize

#print axioms
  compactAdditiveNatListAppendSlicesClosedFormula_code_length_le_fixed
#print axioms compactAdditiveNatListAppendSlicesExplicitFormula_closed
#print axioms
  compactAdditiveNatListAppendSlicesClosedFormula_code_length_le_fixed_of_graph

end FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
