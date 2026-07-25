import integration.FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsExplicitHybridCertificate
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed syntax for closed NatListAtRows formulas with a native numeral index

The syntax-formula relation branch uses the native closed terms `1` and `2`
as lookup indices.  This file bounds those exact formulas, without replacing
the index terms by definitionally different short binary numerals.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactSyntaxUniformRewritingCodeBounds
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private def natListAtRowsFixedIndexTerms
    (tokenTable width tokenCount boundaryTable count value index : Nat) :
    Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count, fixedNumeralTerm index,
    shortBinaryNumeralTerm value]

def natListAtRowsFixedIndexTermCodePolynomial (bitBound : Nat) : Nat :=
  binaryNumeralTermCodeEnvelope bitBound +
    (binaryTermCode (fixedNumeralTerm 0)).length +
    (binaryTermCode (fixedNumeralTerm 1)).length +
    (binaryTermCode (fixedNumeralTerm 2)).length + 1

def natListAtRowsFixedIndexFormulaCodePolynomial (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (natListAtRowsFixedIndexTermCodePolynomial bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveNatListAtRowsDef.val)).length

def natListAtRowsFixedIndexInstalledTerminalCodePolynomial
    (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound)
    (natListAtRowsFixedIndexFormulaCodePolynomial bitBound)

theorem fixedNumeralTerm_code_length_le_relationIndex
    (index bitBound : Nat) (hindex : index <= 2) :
    (binaryTermCode (fixedNumeralTerm index)).length <=
      natListAtRowsFixedIndexTermCodePolynomial bitBound := by
  have hcases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
  rcases hcases with rfl | rfl | rfl <;>
    unfold natListAtRowsFixedIndexTermCodePolynomial <;> omega

theorem shortNumeralTerm_code_length_le_relationIndex
    (value bitBound : Nat) (hvalue : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      natListAtRowsFixedIndexTermCodePolynomial bitBound := by
  have hraw :=
    binaryNumeralTerm_code_length_le_envelope value bitBound hvalue
  unfold natListAtRowsFixedIndexTermCodePolynomial
  omega

theorem
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count value index bitBound :
      Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindex : index <= 2) :
    (binaryFormulaCode
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value
        (fixedNumeralTerm index))).length <=
      natListAtRowsFixedIndexFormulaCodePolynomial bitBound := by
  let terms := natListAtRowsFixedIndexTerms tokenTable width tokenCount
    boundaryTable count value index
  let termCode := natListAtRowsFixedIndexTermCodePolynomial bitBound
  let source : ArithmeticSemiformula Nat 7 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val
  have hterms :
      ∀ coordinate, (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact shortNumeralTerm_code_length_le_relationIndex tokenTable bitBound
        htableSize
    · exact shortNumeralTerm_code_length_le_relationIndex width bitBound
        hwidthSize
    · exact shortNumeralTerm_code_length_le_relationIndex tokenCount bitBound
        htokenCountSize
    · exact shortNumeralTerm_code_length_le_relationIndex boundaryTable
        bitBound hboundarySize
    · exact shortNumeralTerm_code_length_le_relationIndex count bitBound
        hcountSize
    · exact fixedNumeralTerm_code_length_le_relationIndex index bitBound hindex
    · exact shortNumeralTerm_code_length_le_relationIndex value bitBound
        hvalueSize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold sourceSubstitutionQpow at hraw
  rw [
    compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  unfold natListAtRowsFixedIndexFormulaCodePolynomial
  simpa only [terms, termCode, source, natListAtRowsFixedIndexTerms] using hraw

private theorem binaryFormulaCode_right_length_le_and_fixedNumeralIndex
    {arity : Nat}
    (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_exists_fixedNumeralIndex
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1)) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode
        (∃⁰ body : ArithmeticSemiformula Nat arity)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem
    binaryFormulaCode_body_length_le_bexsLTSucc_fixedNumeralIndex
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (body.bexsLTSucc bound)).length := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  exact
    (binaryFormulaCode_right_length_le_and_fixedNumeralIndex _ body).trans
      (binaryFormulaCode_body_length_le_exists_fixedNumeralIndex _)

private theorem body_closed_of_bexsLTSucc_closed_fixedNumeralIndex
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hclosed : (body.bexsLTSucc bound).freeVariables = ∅) :
    body.freeVariables = ∅ := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT at hclosed
  rw [Semiformula.bexs_eq] at hclosed
  have hand :
      (“#0 < !!(Rew.bShift (‘!!bound + 1’))” ⋏ body).freeVariables = ∅ := by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_exs] using hclosed
  have hunion :
      (“#0 < !!(Rew.bShift (‘!!bound + 1’))”).freeVariables ∪
          body.freeVariables = ∅ := by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_and] using hand
  exact (Finset.union_eq_empty.mp hunion).2

theorem
    compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count value index bitBound :
      Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindex : index <= 2) :
    (binaryFormulaCode
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value (fixedNumeralTerm index))).length <=
      natListAtRowsFixedIndexFormulaCodePolynomial bitBound := by
  let terminal :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (fixedNumeralTerm index)
  let witness :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value (fixedNumeralTerm index)
  let guard : ValuationFormula :=
    “!!(fixedNumeralTerm index) < !!(shortBinaryNumeralTerm count)”
  have hterminalWitness :
      (binaryFormulaCode terminal).length <=
        (binaryFormulaCode witness).length := by
    unfold witness
      compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex
    exact
      (binaryFormulaCode_body_length_le_bexsLTSucc_fixedNumeralIndex _ _).trans
        (binaryFormulaCode_body_length_le_bexsLTSucc_fixedNumeralIndex _ _)
  have hwitnessFull :
      (binaryFormulaCode witness).length <=
        (binaryFormulaCode (guard ⋏ witness)).length :=
    binaryFormulaCode_right_length_le_and_fixedNumeralIndex guard witness
  have hfull :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count value index bitBound
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize
      hindex
  have halignment :
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
          tokenCount boundaryTable count value (fixedNumeralTerm index) =
        guard ⋏ witness := by
    rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment]
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex
    rfl
  rw [halignment] at hfull
  simpa only [terminal] using
    hterminalWitness.trans (hwitnessFull.trans hfull)

@[simp] theorem
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count value index : Nat) :
    (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount boundaryTable count value
      (fixedNumeralTerm index)).freeVariables = ∅ := by
  rw [
    compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
  · simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]
  · exact shortBinaryNumeralTerm_freeVariables_eq_empty value

theorem
    compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable value index : Nat) :
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value
      (fixedNumeralTerm index)).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (fixedNumeralTerm index)
  let witness :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value (fixedNumeralTerm index)
  have hfull :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
      tokenTable width tokenCount boundaryTable 0 value index
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment] at hfull
  change
    (“!!(fixedNumeralTerm index) <
        !!(shortBinaryNumeralTerm 0)” ⋏ witness).freeVariables = ∅ at hfull
  have hwitnessClosed : witness.freeVariables = ∅ := by
    have hunion :
        (“!!(fixedNumeralTerm index) <
          !!(shortBinaryNumeralTerm 0)”).freeVariables ∪
            witness.freeVariables = ∅ := by
      simpa only [LO.FirstOrder.Semiformula.freeVariables_and] using hfull
    exact (Finset.union_eq_empty.mp hunion).2
  unfold witness
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex at hwitnessClosed
  have hinnerClosed :=
    body_closed_of_bexsLTSucc_closed_fixedNumeralIndex _ _ hwitnessClosed
  have hterminalClosed :=
    body_closed_of_bexsLTSucc_closed_fixedNumeralIndex _ _ hinnerClosed
  simpa only [terminal] using hterminalClosed

theorem
    compactAdditiveNatListAtRowsInstalledTerminalAtFixedNumeralIndex_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count value index bitBound :
      Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindex : index <= 2) :
    (binaryFormulaCode
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value (fixedNumeralTerm index)) ⇜
        fun coordinate : Fin 2 =>
          shortBinaryNumeralTerm (![data.right, data.left] coordinate))).length <=
      natListAtRowsFixedIndexInstalledTerminalCodePolynomial bitBound := by
  let terms : Fin 2 -> ValuationTerm :=
    fun coordinate => shortBinaryNumeralTerm (![data.right, data.left] coordinate)
  let source :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (fixedNumeralTerm index)
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let sourceCode := natListAtRowsFixedIndexFormulaCodePolynomial bitBound
  have hleftSize : Nat.size data.left <= bitBound :=
    (Nat.size_le_size data.left_le).trans htokenCountSize
  have hrightSize : Nat.size data.right <= bitBound :=
    (Nat.size_le_size data.right_le).trans htokenCountSize
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact binaryNumeralTerm_code_length_le_envelope data.right bitBound
        hrightSize
    · exact binaryNumeralTerm_code_length_le_envelope data.left bitBound
        hleftSize
  have hsource : (binaryFormulaCode source).length <= sourceCode := by
    simpa only [source, sourceCode] using
      compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_code_length_le_fixed
        tokenTable width tokenCount boundaryTable count value index bitBound
        htableSize hwidthSize htokenCountSize hboundarySize hcountSize hvalueSize
        hindex
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode sourceCode terms source hterms hsource
  unfold natListAtRowsFixedIndexInstalledTerminalCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source, termCode, sourceCode] using
    hraw

#print axioms
  compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_code_length_le_fixed
#print axioms
  compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
#print axioms
  compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_code_length_le_fixed
#print axioms
  compactAdditiveNatListAtRowsTerminalAtFixedNumeralIndex_freeVariables_eq_empty
#print axioms
  compactAdditiveNatListAtRowsInstalledTerminalAtFixedNumeralIndex_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
