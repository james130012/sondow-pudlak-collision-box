import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-! # Fully fixed tail 16--21 at an arbitrary valuation context -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail16AtValuationFullyFixedBound

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FullyFixedBound

private theorem arithmeticAddTerm_freeVariables_tail16
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables = left.freeVariables ∪ right.freeVariables
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    fin_cases coordinate
    · exact Finset.mem_union_left _ hcoordinate
    · exact Finset.mem_union_right _ hcoordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticZeroTerm_freeVariables_tail16 :
    (‘0’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem arithmeticOneTerm_freeVariables_tail16 :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem compactSequentFormulaStepTail16Formula_freeVariables_eq_empty
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) :
    (compactSequentFormulaStepTail16Formula tokenTable width tokenCount suffixCount
      valueCount row).freeVariables = ∅ := by
  have hcurrent :
      (compactSequentFormulaStepTail16CurrentFormula tokenTable width tokenCount
        row).freeVariables = ∅ := by
    unfold compactSequentFormulaStepTail16CurrentFormula
      compactAdditiveNatListWitnessRowsClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hnext :
      (compactSequentFormulaStepTail16NextFormula tokenTable width tokenCount
        row).freeVariables = ∅ := by
    unfold compactSequentFormulaStepTail16NextFormula
      compactAdditiveNatListWitnessRowsClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hvalue :
      (compactSequentFormulaStepTail16ValueFormula tokenTable width tokenCount
        row).freeVariables = ∅ := by
    unfold compactSequentFormulaStepTail16ValueFormula
      compactAdditiveNatListWitnessRowsClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hparser :
      (compactSequentFormulaStepTail16ParserFormula tokenTable width tokenCount
        row).freeVariables = ∅ := by
    unfold compactSequentFormulaStepTail16ParserFormula
      compactSequentFormulaStepParserClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      simp [compactSequentFormulaStepParserPublicTerms,
        shortBinaryNumeralTerm_freeVariables_eq_empty,
        arithmeticAddTerm_freeVariables_tail16,
        arithmeticZeroTerm_freeVariables_tail16,
        FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality.compactParserSyntaxExactFuelTerm_freeVariables_eq_empty]
  have happend :
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
        row.value.start row.value.finish row.value.count row.next.start
        row.next.finish row.next.count row.current.start row.current.finish
        row.current.count).freeVariables = ∅ := by
    unfold compactAdditiveNatListAppendSlicesClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  have hcount :
      ((“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula).freeVariables) =
        ∅ := by
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty,
      arithmeticAddTerm_freeVariables_tail16]
  unfold compactSequentFormulaStepTail16Formula
    compactSequentFormulaStepTail17Formula
    compactSequentFormulaStepTail18Formula
    compactSequentFormulaStepTail19Formula
    compactSequentFormulaStepTail20Formula
  rw [LO.FirstOrder.Semiformula.freeVariables_and, hcurrent,
    LO.FirstOrder.Semiformula.freeVariables_and, hnext,
    LO.FirstOrder.Semiformula.freeVariables_and, hvalue,
    LO.FirstOrder.Semiformula.freeVariables_and, hparser,
    LO.FirstOrder.Semiformula.freeVariables_and, happend, hcount]
  simp

noncomputable def compactSequentFormulaStepTail16AtValuationFullyFixedBoundOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ExplicitDirectFormulaBound valuation
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount row)
      (compactSequentFormulaStepTail16FullyFixedPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount row) := by
  let closed :=
    compactSequentFormulaStepTail16FullyFixedEmptyBoundOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex row
      hgraph
  have hclosed :
      (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
        tokenCount suffixCount valueCount row).freeVariables = ∅ := by
    rw [<- compactSequentFormulaStepTail16Formula_eq_direct]
    exact compactSequentFormulaStepTail16Formula_freeVariables_eq_empty tokenTable
      width tokenCount suffixCount valueCount row
  have hcontext : (∅ : Finset ValuationFormula) =
      valuationContext
        (compactSequentFormulaStepDirectTail16AtValuationIndex tokenTable width
          tokenCount suffixCount valueCount row).freeVariables valuation := by
    rw [hclosed]
    simp [valuationContext]
  let proof := CertifiedPAContextProof.castContext hcontext closed.proof
  refine { proof := proof, payloadLength_le := ?_ }
  dsimp only [proof]
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact closed.payloadLength_le

#print axioms compactSequentFormulaStepTail16Formula_freeVariables_eq_empty
#print axioms
  compactSequentFormulaStepTail16AtValuationFullyFixedBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail16AtValuationFullyFixedBound
