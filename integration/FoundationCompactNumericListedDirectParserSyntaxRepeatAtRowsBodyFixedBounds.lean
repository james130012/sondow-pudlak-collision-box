import integration.FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsSpecificTerminalFixedBounds
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-! # Uniform exact-term body bounds for the two Repeat task-row lookups -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListAtRows
open FoundationCompactNumericListedDirectSyntaxTaskListAtRowsExplicitHybridCertificate

def repeatAtRowsTermCodeEnvelope (bitBound : Nat) : Nat :=
  max (binaryNumeralTermCodeEnvelope bitBound)
    (max (binaryTermCode (fixedNumeralTerm 0)).length
      (max (binaryTermCode (fixedNumeralTerm 1)).length
        (binaryTermCode (fixedNumeralTerm 2)).length))

def repeatAtRowsFullFormulaCodeEnvelope (bitBound : Nat) : Nat :=
  sourceSubstitutionPolynomialFormulaCodeEnvelopeOfTermBound 0
    (repeatAtRowsTermCodeEnvelope bitBound)
    (binaryFormulaCode
      (Rewriting.emb (ξ := Nat)
        compactAdditiveSyntaxTaskListAtRowsDef.val)).length

def repeatAtRowsClosedTerms
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm) :
    Fin 9 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm boundaryTable,
    shortBinaryNumeralTerm count,
    indexTerm, kindTerm, binderArityTerm, repeatCountTerm]

theorem shortBinary_code_le_repeatAtRowsTermEnvelope
    (value bitBound : Nat) (hsize : Nat.size value <= bitBound) :
    (binaryTermCode (shortBinaryNumeralTerm value)).length <=
      repeatAtRowsTermCodeEnvelope bitBound := by
  exact (binaryNumeralTerm_code_length_le_envelope value bitBound hsize).trans
    (Nat.le_max_left _ _)

theorem fixedZero_code_le_repeatAtRowsTermEnvelope (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 0)).length <=
      repeatAtRowsTermCodeEnvelope bitBound := by
  unfold repeatAtRowsTermCodeEnvelope
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem fixedOne_code_le_repeatAtRowsTermEnvelope (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 1)).length <=
      repeatAtRowsTermCodeEnvelope bitBound := by
  unfold repeatAtRowsTermCodeEnvelope
  exact le_trans (Nat.le_max_left _ _)
    (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem fixedTwo_code_le_repeatAtRowsTermEnvelope (bitBound : Nat) :
    (binaryTermCode (fixedNumeralTerm 2)).length <=
      repeatAtRowsTermCodeEnvelope bitBound := by
  unfold repeatAtRowsTermCodeEnvelope
  exact le_trans (Nat.le_max_right _ _)
    (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem repeatAtRowsFullFormula_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count bitBound : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hboundarySize : Nat.size boundaryTable <= bitBound)
    (hcountSize : Nat.size count <= bitBound)
    (hindexCode :
      (binaryTermCode indexTerm).length <= repeatAtRowsTermCodeEnvelope bitBound)
    (hkindCode :
      (binaryTermCode kindTerm).length <= repeatAtRowsTermCodeEnvelope bitBound)
    (hbinderCode :
      (binaryTermCode binderArityTerm).length <=
        repeatAtRowsTermCodeEnvelope bitBound)
    (hrepeatCode :
      (binaryTermCode repeatCountTerm).length <=
        repeatAtRowsTermCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
        repeatCountTerm)).length <=
      repeatAtRowsFullFormulaCodeEnvelope bitBound := by
  let terms := repeatAtRowsClosedTerms tokenTable width tokenCount boundaryTable
    count indexTerm kindTerm binderArityTerm repeatCountTerm
  let termCode := repeatAtRowsTermCodeEnvelope bitBound
  let source : ArithmeticSemiformula Nat 9 :=
    Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListAtRowsDef.val
  have hterms : forall coordinate,
      (binaryTermCode (terms coordinate)).length <= termCode := by
    intro coordinate
    fin_cases coordinate
    · exact shortBinary_code_le_repeatAtRowsTermEnvelope tokenTable bitBound
        htableSize
    · exact shortBinary_code_le_repeatAtRowsTermEnvelope width bitBound
        hwidthSize
    · exact shortBinary_code_le_repeatAtRowsTermEnvelope tokenCount bitBound
        htokenCountSize
    · exact shortBinary_code_le_repeatAtRowsTermEnvelope boundaryTable bitBound
        hboundarySize
    · exact shortBinary_code_le_repeatAtRowsTermEnvelope count bitBound hcountSize
    · exact hindexCode
    · exact hkindCode
    · exact hbinderCode
    · exact hrepeatCode
  have hraw :=
    binaryFormulaCode_sourceSubstitutionQpow_length_le_polynomial_of_termBound
      0 termCode (binaryFormulaCode source).length terms source hterms le_rfl
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  unfold repeatAtRowsFullFormulaCodeEnvelope sourceSubstitutionQpow at *
  simpa only [terms, termCode, source, repeatAtRowsClosedTerms] using hraw

private theorem binaryFormulaCode_right_length_le_and_repeatAtRows
    {arity : Nat} (left right : ArithmeticSemiformula Nat arity) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_exists_repeatAtRows
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1)) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode
        (∃⁰ body : ArithmeticSemiformula Nat arity)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_body_length_le_bexsLTSucc_repeatAtRows
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity) :
    (binaryFormulaCode body).length <=
      (binaryFormulaCode (body.bexsLTSucc bound)).length := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT
  exact
    (binaryFormulaCode_right_length_le_and_repeatAtRows _ body).trans
      (binaryFormulaCode_body_length_le_exists_repeatAtRows _)

theorem repeatAtRowsTerminalBody_code_length_le_fixed
    (tokenTable width tokenCount boundaryTable count bitBound : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hfull :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
          width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
          repeatCountTerm)).length <=
        repeatAtRowsFullFormulaCodeEnvelope bitBound) :
    (binaryFormulaCode
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable
        width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
        repeatCountTerm)).length <=
      repeatAtRowsFullFormulaCodeEnvelope bitBound := by
  let body :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width
      tokenCount boundaryTable indexTerm kindTerm binderArityTerm repeatCountTerm
  let witness :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm
  let guard : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm count)”
  have hbodyWitness :
      (binaryFormulaCode body).length <=
        (binaryFormulaCode witness).length := by
    unfold witness
      compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula
    exact
      (binaryFormulaCode_body_length_le_bexsLTSucc_repeatAtRows _ _).trans
        (binaryFormulaCode_body_length_le_bexsLTSucc_repeatAtRows _ _)
  have hwitnessFull :
      (binaryFormulaCode witness).length <=
        (binaryFormulaCode (guard ⋏ witness)).length :=
    binaryFormulaCode_right_length_le_and_repeatAtRows guard witness
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment] at hfull
  change
    (binaryFormulaCode (guard ⋏ witness)).length <=
      repeatAtRowsFullFormulaCodeEnvelope bitBound at hfull
  simpa only [body] using hbodyWitness.trans (hwitnessFull.trans hfull)

private theorem body_closed_of_bexsLTSucc_closed_repeatAtRows
    {arity : Nat} (body : ArithmeticSemiformula Nat (arity + 1))
    (bound : ArithmeticSemiterm Nat arity)
    (hclosed : (body.bexsLTSucc bound).freeVariables = ∅) :
    body.freeVariables = ∅ := by
  unfold Semiformula.bexsLTSucc Semiformula.bexsLT at hclosed
  rw [Semiformula.bexs_eq] at hclosed
  have hand :
      (“#0 < !!(Rew.bShift (‘!!bound + 1’))” ⋏ body).freeVariables = ∅ := by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_exs] using hclosed
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hand
  exact (Finset.union_eq_empty.mp hand).2

theorem repeatAtRowsFullFormula_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅) :
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
      width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
      repeatCountTerm).freeVariables = ∅ := by
  let terms := repeatAtRowsClosedTerms tokenTable width tokenCount boundaryTable
    count indexTerm kindTerm binderArityTerm repeatCountTerm
  have hterms : forall coordinate, (terms coordinate).freeVariables = ∅ := by
    intro coordinate
    fin_cases coordinate
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty width
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty boundaryTable
    · exact shortBinaryNumeralTerm_freeVariables_eq_empty count
    · exact hindexClosed
    · exact hkindClosed
    · exact hbinderClosed
    · exact hrepeatClosed
  unfold compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula
  change
    ((Rewriting.emb (ξ := Nat)
      compactAdditiveSyntaxTaskListAtRowsDef.val) ⇜ terms).freeVariables = ∅
  exact embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    _ terms hterms

theorem repeatAtRowsTerminalBody_freeVariables_eq_empty
    (tokenTable width tokenCount boundaryTable count : Nat)
    (indexTerm kindTerm binderArityTerm repeatCountTerm : ValuationTerm)
    (hindexClosed : indexTerm.freeVariables = ∅)
    (hkindClosed : kindTerm.freeVariables = ∅)
    (hbinderClosed : binderArityTerm.freeVariables = ∅)
    (hrepeatClosed : repeatCountTerm.freeVariables = ∅) :
    (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsTerminal tokenTable width
      tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm).freeVariables = ∅ := by
  have hfull :
      (compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula tokenTable
        width tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
        repeatCountTerm).freeVariables = ∅ := by
    exact repeatAtRowsFullFormula_freeVariables_eq_empty tokenTable width
      tokenCount boundaryTable count indexTerm kindTerm binderArityTerm
      repeatCountTerm hindexClosed hkindClosed hbinderClosed hrepeatClosed
  rw [compactAdditiveSyntaxTaskListAtRowsAtValuationTermsFormula_alignment] at hfull
  let witness :=
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula tokenTable
      width tokenCount boundaryTable indexTerm kindTerm binderArityTerm
      repeatCountTerm
  change
    (“!!indexTerm < !!(shortBinaryNumeralTerm count)” ⋏ witness).freeVariables =
      ∅ at hfull
  rw [LO.FirstOrder.Semiformula.freeVariables_and] at hfull
  have hwitness :=
    (Finset.union_eq_empty.mp hfull).2
  unfold witness
    compactAdditiveSyntaxTaskListAtRowsAtValuationTermsWitnessFormula at hwitness
  exact body_closed_of_bexsLTSucc_closed_repeatAtRows _ _ <|
    body_closed_of_bexsLTSucc_closed_repeatAtRows _ _ hwitness

#print axioms repeatAtRowsFullFormula_code_length_le_fixed
#print axioms repeatAtRowsTerminalBody_code_length_le_fixed
#print axioms repeatAtRowsFullFormula_freeVariables_eq_empty
#print axioms repeatAtRowsTerminalBody_freeVariables_eq_empty

end FoundationCompactNumericListedDirectParserSyntaxRepeatAtRowsBodyFixedBounds
