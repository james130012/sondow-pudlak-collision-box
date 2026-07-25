import integration.FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryTerminalFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-!
# Fully fixed code bound for a binary syntax-task row body

For the two parser-selected row indices, the genuine open two-witness body is
bounded by the code of the complete closed `AtRows` formula.  The proof bounds
the nine source-substitution terms and then descends through the outer guard
and the two bounded existential shells.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate

def syntaxTaskAtRowsBinaryTermCodeEnvelope (bitBound : Nat) : Nat :=
  max (binaryNumeralTermCodeEnvelope bitBound)
    (max (binaryTermCode (nativeNumeralTerm 0)).length
      (binaryTermCode (nativeNumeralTerm 1)).length)

def syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveSyntaxTaskListAtRowsDef.val)).length

def syntaxTaskAtRowsBinaryClosedTerms
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat) :
    Fin 9 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    nativeNumeralTerm index,
    nativeNumeralTerm 1,
    shortBinaryNumeralTerm binderArity,
    nativeNumeralTerm 0]

private theorem shortBinary_code_le_binaryAtRowsTermEnvelope
    (value bitBound : Nat) (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound := by
  exact (binaryNumeralTerm_code_length_le_envelope value bitBound hsize).trans
    (Nat.le_max_left _ _)

private theorem nativeZero_code_le_binaryAtRowsTermEnvelope
    (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 0)).length <=
      syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound := by
  unfold syntaxTaskAtRowsBinaryTermCodeEnvelope
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

private theorem nativeOne_code_le_binaryAtRowsTermEnvelope
    (bitBound : Nat) :
    (binaryTermCode (nativeNumeralTerm 1)).length <=
      syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound := by
  unfold syntaxTaskAtRowsBinaryTermCodeEnvelope
  exact le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)

private theorem nativeSelectedIndex_code_le_binaryAtRowsTermEnvelope
    (index bitBound : Nat) (hindex : index < 2) :
    (binaryTermCode (nativeNumeralTerm index)).length <=
      syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound := by
  have hcases : index = 0 ∨ index = 1 := by omega
  rcases hcases with rfl | rfl
  · exact nativeZero_code_le_binaryAtRowsTermEnvelope bitBound
  · exact nativeOne_code_le_binaryAtRowsTermEnvelope bitBound

theorem syntaxTaskAtRowsBinaryFullFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity bitBound :
      Nat)
    (hindex : index < 2)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count (nativeNumeralTerm index)
        (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
        (nativeNumeralTerm 0))).length <=
      syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound := by
  let terms := syntaxTaskAtRowsBinaryClosedTerms tokenTable width tokenCount
    boundaryTable count index binderArity
  let termCode := syntaxTaskAtRowsBinaryTermCodeEnvelope bitBound
  let source : ArithmeticSemiformula Nat 9 :=
    Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListAtRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact shortBinary_code_le_binaryAtRowsTermEnvelope tokenTable bitBound
        htableSize
    · exact shortBinary_code_le_binaryAtRowsTermEnvelope width bitBound
        hwidthSize
    · exact shortBinary_code_le_binaryAtRowsTermEnvelope tokenCount bitBound
        htokenCountSize
    · exact shortBinary_code_le_binaryAtRowsTermEnvelope boundaryTable bitBound
        hboundarySize
    · exact shortBinary_code_le_binaryAtRowsTermEnvelope count bitBound
        hcountSize
    · exact nativeSelectedIndex_code_le_binaryAtRowsTermEnvelope index bitBound
        hindex
    · exact nativeOne_code_le_binaryAtRowsTermEnvelope bitBound
    · exact shortBinary_code_le_binaryAtRowsTermEnvelope binderArity bitBound
        hbinderSize
    · exact nativeZero_code_le_binaryAtRowsTermEnvelope bitBound
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  unfold syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope sourceSubstitutionQpow at *
  simpa only [terms, termCode, source,
    syntaxTaskAtRowsBinaryClosedTerms] using hraw

private theorem binaryFormulaCode_right_length_le_and_binaryAtRows
    {arity : Nat} (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_exists_binaryAtRows
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1)) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode
        (∃⁰ body : ArithmeticSemiformula Nat arity)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_bexsLTSucc_binaryAtRows
    {arity : Nat}
    (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (body.bexsLTSucc bound)).length := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  exact
    (binaryFormulaCode_right_length_le_and_binaryAtRows _ body).trans
      (binaryFormulaCode_body_length_le_exists_binaryAtRows _)

theorem syntaxTaskAtRowsBinaryTerminalBody_code_length_le_fullyFixed
    (tokenTable width tokenCount boundaryTable count index binderArity bitBound :
      Nat)
    (hindex : index < 2)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
        width tokenCount boundaryTable (nativeNumeralTerm index)
        (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
        (nativeNumeralTerm 0))).length <=
      syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound := by
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable (nativeNumeralTerm index)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)
  let witness :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable (nativeNumeralTerm index)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)
  let guard : ValuationFormula :=
    “!!(nativeNumeralTerm index) < !!(shortBinaryNumeralTerm count)”
  have hbodyWitness :
      (binaryFormulaCode body).length <=
        (binaryFormulaCode witness).length := by
    unfold witness
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
    exact
      (binaryFormulaCode_body_length_le_bexsLTSucc_binaryAtRows _ _).trans
        (binaryFormulaCode_body_length_le_bexsLTSucc_binaryAtRows _ _)
  have hwitnessFull :
      (binaryFormulaCode witness).length <=
        (binaryFormulaCode (guard ⋏ witness)).length :=
    binaryFormulaCode_right_length_le_and_binaryAtRows guard witness
  have hfull :=
    syntaxTaskAtRowsBinaryFullFormula_code_length_le_fullyFixed tokenTable width
      tokenCount boundaryTable count index binderArity bitBound hindex
      htableSize hwidthSize htokenCountSize hboundarySize hcountSize hbinderSize
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment] at hfull
  change
    (binaryFormulaCode (guard ⋏ witness)).length <=
      syntaxTaskAtRowsBinaryFullFormulaCodeEnvelope bitBound at hfull
  simpa only [body] using hbodyWitness.trans (hwitnessFull.trans hfull)

private theorem nativeNumeralTerm_freeVariables_eq_empty_binaryAtRowsBody
    (value : Nat) :
    (nativeNumeralTerm value).freeVariables = ∅ := by
  unfold nativeNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

theorem syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count index binderArity : Nat) :
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
      width tokenCount boundaryTable count (nativeNumeralTerm index)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)).freeVariables = ∅ := by
  let terms := syntaxTaskAtRowsBinaryClosedTerms tokenTable width tokenCount
    boundaryTable count index binderArity
  have hterms : forall coordinate, (terms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
    · exact nativeNumeralTerm_freeVariables_eq_empty_binaryAtRowsBody index
    · exact nativeNumeralTerm_freeVariables_eq_empty_binaryAtRowsBody 1
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty binderArity
    · exact nativeNumeralTerm_freeVariables_eq_empty_binaryAtRowsBody 0
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  change
    ((Rewriting.emb (ξ := Nat)
      compactAdditiveSyntaxTaskListAtRowsDef.val) ⇜ terms).freeVariables = ∅
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    _ terms hterms

private theorem body_closed_of_bexsLTSucc_closed_binaryAtRows
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

theorem syntaxTaskAtRowsBinaryTerminalBody_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable index binderArity : Nat) :
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable (nativeNumeralTerm index)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)).freeVariables = ∅ := by
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
      width tokenCount boundaryTable (nativeNumeralTerm index)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)
  let witness :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable (nativeNumeralTerm index)
      (nativeNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (nativeNumeralTerm 0)
  have hfull :=
    syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty tokenTable width
      tokenCount boundaryTable 0 index binderArity
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment] at hfull
  change
    (“!!(nativeNumeralTerm index) < !!(shortBinaryNumeralTerm 0)” ⋏
      witness).freeVariables = ∅ at hfull
  have hwitness : witness.freeVariables = ∅ := by
    have hunion :
        (“!!(nativeNumeralTerm index) <
          !!(shortBinaryNumeralTerm 0)”).freeVariables ∪
            witness.freeVariables = ∅ := by
      simpa only [LO.FirstOrder.Semiformula.freeVariables_and] using hfull
    exact (Finset.union_eq_empty.mp hunion).2
  unfold witness
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula at hwitness
  have hinner := body_closed_of_bexsLTSucc_closed_binaryAtRows _ _ hwitness
  have hbody := body_closed_of_bexsLTSucc_closed_binaryAtRows _ _ hinner
  simpa only [body] using hbody

#print axioms syntaxTaskAtRowsBinaryFullFormula_code_length_le_fullyFixed
#print axioms syntaxTaskAtRowsBinaryTerminalBody_code_length_le_fullyFixed
#print axioms syntaxTaskAtRowsBinaryFullFormula_freeVariables_eq_empty
#print axioms syntaxTaskAtRowsBinaryTerminalBody_freeVariables_eq_empty

end FoundationCompactNumericListedDirectSyntaxTaskListAtRowsBinaryBodyFullyFixedBounds
