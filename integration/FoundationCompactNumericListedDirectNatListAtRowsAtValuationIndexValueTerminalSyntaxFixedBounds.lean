import integration.FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueSyntaxFixedBounds

/-!
# Fixed installed-terminal syntax for exact row index and value terms

The terminal is extracted from the complete row formula through constructor
code monotonicity.  Installing the two bounded row witnesses is then charged
by the same fixed source-substitution polynomial as the numeral-only route.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 60000

namespace FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalSyntaxFixedBounds

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
open FoundationCompactNumericListedDirectNatListAtRowsTerminalSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueSyntaxFixedBounds

private theorem binaryFormulaCode_right_length_le_and_terminalValueSyntax
    {arity : Nat} (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_exists_terminalValueSyntax
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1)) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode
        (∃⁰ body : ArithmeticSemiformula Nat arity)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem
    binaryFormulaCode_body_length_le_bexsLTSucc_terminalValueSyntax
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (body.bexsLTSucc bound)).length := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  exact
    (binaryFormulaCode_right_length_le_and_terminalValueSyntax _ body).trans
      (binaryFormulaCode_body_length_le_exists_terminalValueSyntax _)

private theorem body_closed_of_bexsLTSucc_closed_terminalValueSyntax
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1))
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
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
        width tokenCount boundaryTable indexTerm valueTerm)).length <=
      natListAtRowsFullFormulaCodePolynomial bitBound := by
  let terminal :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm
  let witness :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
      width tokenCount boundaryTable indexTerm valueTerm
  let guard : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  have hterminalWitness :
      (binaryFormulaCode terminal).length <=
        (binaryFormulaCode witness).length := by
    unfold witness
      compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue
    exact
      (binaryFormulaCode_body_length_le_bexsLTSucc_terminalValueSyntax _ _).trans
        (binaryFormulaCode_body_length_le_bexsLTSucc_terminalValueSyntax _ _)
  have hwitnessFull :
      (binaryFormulaCode witness).length <=
        (binaryFormulaCode (guard ⋏ witness)).length :=
    binaryFormulaCode_right_length_le_and_terminalValueSyntax guard witness
  have hfull :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_code_length_le_fixed
      tokenTable width tokenCount boundaryTable count bitBound indexTerm
      valueTerm htableSize hwidthSize htokenCountSize hboundarySize hcountSize
      hindexCode hvalueCode
  have halignment :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_alignment
      tokenTable width tokenCount boundaryTable count indexTerm valueTerm
  rw [halignment] at hfull
  unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue at hfull
  simpa only [terminal, witness, guard] using
    hterminalWitness.trans (hwitnessFull.trans hfull)

theorem compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_closed
    (tokenTable width tokenCount boundaryTable : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hvalueClosed : valueTerm.freeVariables = ∅) :
    (compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm).freeVariables = ∅ := by
  let terminal :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm
  let witness :=
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue tokenTable
      width tokenCount boundaryTable indexTerm valueTerm
  have hfull :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_closed tokenTable
      width tokenCount boundaryTable 0 indexTerm valueTerm hindexClosed
      hvalueClosed
  have halignment :=
    compactAdditiveNatListAtRowsAtValuationIndexValueFormula_alignment
      tokenTable width tokenCount boundaryTable 0 indexTerm valueTerm
  rw [halignment] at hfull
  unfold compactAdditiveNatListAtRowsExplicitFormulaAtValuationIndexValue at hfull
  have hwitnessClosed : witness.freeVariables = ∅ := by
    have hunion :
        (“!!indexTerm < !!(shortBinaryNumeralTerm 0)” :
          ValuationFormula).freeVariables ∪ witness.freeVariables = ∅ := by
      simpa only [LO.FirstOrder.Semiformula.freeVariables_and, witness] using
        hfull
    exact (Finset.union_eq_empty.mp hunion).2
  unfold witness
    compactAdditiveNatListAtRowsWitnessBodyAtValuationIndexValue at hwitnessClosed
  have hinnerClosed :=
    body_closed_of_bexsLTSucc_closed_terminalValueSyntax _ _ hwitnessClosed
  have hterminalClosed :=
    body_closed_of_bexsLTSucc_closed_terminalValueSyntax _ _ hinnerClosed
  simpa only [terminal] using hterminalClosed

theorem
    compactAdditiveNatListAtRowsInstalledTerminalAtValuationIndexValue_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count index value bitBound : Nat)
    (indexTerm valueTerm : ValuationTerm)
    (data : CompactAdditiveNatListAtRowData tokenTable width tokenCount
      boundaryTable index value)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound)
    (hvalueCode : (binaryTermCode valueTerm).length <=
      binaryNumeralTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      ((compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable
          width tokenCount boundaryTable indexTerm valueTerm) ⇜
        fun coordinate : Fin 2 =>
          shortBinaryNumeralTerm
            (![data.right, data.left] coordinate))).length <=
      natListAtRowsInstalledTerminalCodePolynomial bitBound := by
  let terms : Fin 2 -> ValuationTerm :=
    fun coordinate =>
      shortBinaryNumeralTerm (![data.right, data.left] coordinate)
  let source :=
    compactAdditiveNatListAtRowsTerminalAtValuationIndexValue tokenTable width
      tokenCount boundaryTable indexTerm valueTerm
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
      compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_code_length_le_fixed
        tokenTable width tokenCount boundaryTable count bitBound indexTerm
        valueTerm htableSize hwidthSize htokenCountSize hboundarySize
        hcountSize hindexCode hvalueCode
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode sourceCode terms source hterms hsource
  unfold natListAtRowsInstalledTerminalCodePolynomial
  simpa only [sourceSubstitutionQpow, terms, source, termCode, sourceCode] using
    hraw

#print axioms
  compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_code_length_le_fixed
#print axioms
  compactAdditiveNatListAtRowsTerminalAtValuationIndexValue_closed
#print axioms
  compactAdditiveNatListAtRowsInstalledTerminalAtValuationIndexValue_code_length_le_fixed

end FoundationCompactNumericListedDirectNatListAtRowsAtValuationIndexValueTerminalSyntaxFixedBounds
