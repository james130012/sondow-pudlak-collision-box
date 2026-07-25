import integration.FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Fixed syntax bound for the row-lookup terminal formula

The real mapped-prefix caller supplies a closed short-binary row index.  We
first bound the complete seven-coordinate source substitution, then use
constructor-local code monotonicity to descend through the outer conjunction
and the two bounded existential shells to the exact terminal body.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 120000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactPAEmbeddedPredicateFreeVariables

def natListAtRowsClosedTerms
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    shortBinaryNumeralTerm index,
    shortBinaryNumeralTerm value]

def natListAtRowsFullFormulaCodePolynomial (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveNatListAtRowsDef.val)).length

def natListAtRowsInstalledTerminalCodePolynomial (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (binaryNumeralTermCodeEnvelope bitBound)
    (natListAtRowsFullFormulaCodePolynomial bitBound)

theorem compactAdditiveNatListAtRowsAtShortIndexFormula_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count index value bitBound :
      Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount boundaryTable count value
        (shortBinaryNumeralTerm index))).length <=
      natListAtRowsFullFormulaCodePolynomial bitBound := by
  let terms := natListAtRowsClosedTerms tokenTable width tokenCount
    boundaryTable count index value
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let source : ArithmeticSemiformula Nat 7 :=
    Rewriting.emb (ξ := Nat) compactAdditiveNatListAtRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate <;>
      simp only [terms, natListAtRowsClosedTerms] <;>
      exact binaryNumeralTerm_code_length_le_envelope _ bitBound (by
        assumption)
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold sourceSubstitutionQpow at hraw
  rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  unfold natListAtRowsFullFormulaCodePolynomial
  simpa only [terms, termCode, source, natListAtRowsClosedTerms] using hraw

private theorem binaryFormulaCode_right_length_le_and_terminalSyntax
    {arity : Nat}
    (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_exists_terminalSyntax
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1)) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (∃⁰ body :
        ArithmeticSemiformula Nat arity)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_bexsLTSucc_terminalSyntax
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (body.bexsLTSucc bound)).length := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  exact
    (binaryFormulaCode_right_length_le_and_terminalSyntax _ body).trans
      (binaryFormulaCode_body_length_le_exists_terminalSyntax _)

private theorem body_closed_of_bexsLTSucc_closed_terminalSyntax
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

theorem compactAdditiveNatListAtRowsTerminalAtShortIndex_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count index value bitBound :
      Nat)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
        tokenCount boundaryTable value
        (shortBinaryNumeralTerm index))).length <=
      natListAtRowsFullFormulaCodePolynomial bitBound := by
  let terminal :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (shortBinaryNumeralTerm index)
  let witness :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value (shortBinaryNumeralTerm index)
  let guard : ValuationFormula :=
    “!!(shortBinaryNumeralTerm index) <
      !!(shortBinaryNumeralTerm count)”
  have hterminalWitness :
      (binaryFormulaCode terminal).length <=
        (binaryFormulaCode witness).length := by
    unfold witness
      compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex
    exact
      (binaryFormulaCode_body_length_le_bexsLTSucc_terminalSyntax _ _).trans
        (binaryFormulaCode_body_length_le_bexsLTSucc_terminalSyntax _ _)
  have hwitnessFull :
      (binaryFormulaCode witness).length <=
        (binaryFormulaCode (guard ⋏ witness)).length :=
    binaryFormulaCode_right_length_le_and_terminalSyntax guard witness
  have hfull :=
    compactAdditiveNatListAtRowsAtShortIndexFormula_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count index value bitBound
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hindexSize
      hvalueSize
  have halignment :
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
          tokenCount boundaryTable count value
          (shortBinaryNumeralTerm index) =
        guard ⋏ witness := by
    rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment]
    unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndex
    rfl
  rw [halignment] at hfull
  simpa only [terminal] using
    hterminalWitness.trans (hwitnessFull.trans hfull)

theorem compactAdditiveNatListAtRowsAtShortIndexFormula_closed
    (tokenTable width tokenCount boundaryTable count index value : Nat) :
    (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount boundaryTable count value
      (shortBinaryNumeralTerm index)).freeVariables = ∅ := by
  let terms := natListAtRowsClosedTerms tokenTable width tokenCount
    boundaryTable count index value
  have hterms : forall coordinate,
      (terms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate <;>
      simp only [terms, natListAtRowsClosedTerms] <;>
      apply shortBinaryNumeralTerm_freeVariables_eq_empty
  rw [
    compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
  change
    ((Rewriting.emb (ξ := Nat)
      compactAdditiveNatListAtRowsDef.val) ⇜ terms).freeVariables = ∅
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    _ terms hterms

theorem compactAdditiveNatListAtRowsTerminalAtShortIndex_closed
    (tokenTable width tokenCount boundaryTable value index : Nat) :
    (compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value
      (shortBinaryNumeralTerm index)).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (shortBinaryNumeralTerm index)
  let witness :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex tokenTable width
      tokenCount boundaryTable value (shortBinaryNumeralTerm index)
  have hwitnessClosed :
      witness.freeVariables = ∅ := by
    have hfull :
        (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
          tokenCount boundaryTable 0 value
          (shortBinaryNumeralTerm index)).freeVariables = ∅ := by
      let terms := natListAtRowsClosedTerms tokenTable width tokenCount
        boundaryTable 0 index value
      have hterms : forall coordinate,
          (terms coordinate).freeVariables = ∅ := by
        intro coordinate
        fin_cases coordinate
        · change
            (shortBinaryNumeralTerm tokenTable).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
        · change (shortBinaryNumeralTerm width).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
        · change (shortBinaryNumeralTerm tokenCount).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
        · change (shortBinaryNumeralTerm boundaryTable).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
        · change (shortBinaryNumeralTerm 0).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
        · change (shortBinaryNumeralTerm index).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
        · change (shortBinaryNumeralTerm value).freeVariables = ∅
          exact shortBinaryNumeralTerm_freeVariables_eq_empty _
      rw [
        compactAdditiveNatListAtRowsAtValuationIndexFormula_eq_explicitSubstitution]
      change
        ((Rewriting.emb (ξ := Nat)
          compactAdditiveNatListAtRowsDef.val) ⇜ terms).freeVariables = ∅
      exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
        _ terms hterms
    rw [compactAdditiveNatListAtRowsAtValuationIndexFormula_alignment] at hfull
    change
      (“!!(shortBinaryNumeralTerm index) <
          !!(shortBinaryNumeralTerm 0)” ⋏ witness).freeVariables = ∅ at hfull
    have hunion :
        (“!!(shortBinaryNumeralTerm index) <
          !!(shortBinaryNumeralTerm 0)”).freeVariables ∪
            witness.freeVariables = ∅ := by
      simpa only [LO.FirstOrder.Semiformula.freeVariables_and] using hfull
    exact (Finset.union_eq_empty.mp hunion).2
  unfold witness
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndex at hwitnessClosed
  have hinnerClosed :=
    body_closed_of_bexsLTSucc_closed_terminalSyntax _ _ hwitnessClosed
  have hterminalClosed :=
    body_closed_of_bexsLTSucc_closed_terminalSyntax _ _ hinnerClosed
  simpa only [terminal] using hterminalClosed

theorem
    compactAdditiveNatListAtRowsInstalledTerminalAtShortIndex_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count index value bitBound :
      Nat)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexSize : Nat.size index <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    (binaryFormulaCode
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
          tokenCount boundaryTable value (shortBinaryNumeralTerm index)) ⇜
        fun coordinate : Fin 2 =>
          shortBinaryNumeralTerm (![data.right, data.left] coordinate))).length <=
      natListAtRowsInstalledTerminalCodePolynomial bitBound := by
  let terms : Fin 2 -> ValuationTerm :=
    fun coordinate => shortBinaryNumeralTerm (![data.right, data.left] coordinate)
  let source :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndex tokenTable width
      tokenCount boundaryTable value (shortBinaryNumeralTerm index)
  let termCode := binaryNumeralTermCodeEnvelope bitBound
  let sourceCode := natListAtRowsFullFormulaCodePolynomial bitBound
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
      compactAdditiveNatListAtRowsTerminalAtShortIndex_code_length_le_fixed
        tokenTable width tokenCount boundaryTable count index value bitBound
        htableSize hwidthSize htokenCountSize hboundarySize hcountSize
        hindexSize hvalueSize
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode sourceCode terms source hterms hsource
  unfold natListAtRowsInstalledTerminalCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source, termCode, sourceCode] using
    hraw

#print axioms
  compactAdditiveNatListAtRowsAtShortIndexFormula_code_length_le_fixed
#print axioms
  compactAdditiveNatListAtRowsTerminalAtShortIndex_code_length_le_fixed
#print axioms compactAdditiveNatListAtRowsAtShortIndexFormula_closed
#print axioms compactAdditiveNatListAtRowsTerminalAtShortIndex_closed
#print axioms
  compactAdditiveNatListAtRowsInstalledTerminalAtShortIndex_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
