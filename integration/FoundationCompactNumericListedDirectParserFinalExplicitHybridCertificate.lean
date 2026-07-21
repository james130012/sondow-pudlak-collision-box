import integration.FoundationCompactNumericListedDirectParserFinalFormula
import integration.FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

/-!
# Explicit hybrid certificate for the numeric parser final state

The public constructor consumes the original final-state graph.  Its completed
status prefix, output layout, row equality, binary size, and area bound are
certified directly and assembled in the exact source-formula order.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserFinalFormula
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

def compactUnifiedParserFinalStateRowsClosedFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserFinalStateRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tokensFinish,
      shortBinaryNumeralTerm coordinates.tasksFinish,
      shortBinaryNumeralTerm coordinates.tokensBoundary,
      shortBinaryNumeralTerm coordinates.tokensCount,
      shortBinaryNumeralTerm coordinates.tasksBoundary,
      shortBinaryNumeralTerm coordinates.tasksCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm outputStart,
      shortBinaryNumeralTerm outputBoundary,
      shortBinaryNumeralTerm outputBoundarySize]

def compactUnifiedParserFinalStateRowsExplicitFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) : ValuationFormula :=
  compactBinaryNatCompletedStatusPrefixClosedFormula
      tokenTable width tokenCount coordinates.tasksFinish outputStart ⋏
    (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount outputStart sourceCount
          coordinates.finish outputBoundary ⋏
      (compactAdditiveNatListSameRowsClosedFormula
          tokenTable width tokenCount sourceBoundary sourceCount
            outputBoundary sourceCount ⋏
        (compactNatSizeClosedFormula outputBoundarySize outputBoundary ⋏
          “!!(shortBinaryNumeralTerm outputBoundarySize) ≤
            (!!(shortBinaryNumeralTerm sourceCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)”)))

theorem compactUnifiedParserFinalStateRowsClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) :
    compactUnifiedParserFinalStateRowsClosedFormula
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
          outputStart outputBoundary outputBoundarySize =
      compactUnifiedParserFinalStateRowsExplicitFormula
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
          outputStart outputBoundary outputBoundarySize := by
  unfold compactUnifiedParserFinalStateRowsClosedFormula
  unfold compactUnifiedParserFinalStateRowsExplicitFormula
  unfold compactUnifiedParserFinalStateRowsDef
  unfold compactBinaryNatCompletedStatusPrefixClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactAdditiveNatListSameRowsClosedFormula
  unfold compactNatSizeClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def boundaryAreaCertificate
    (boundarySize count tokenCount : Nat)
    (hbound : boundarySize ≤ (count + 1) * tokenCount) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm boundarySize) ≤
        (!!(shortBinaryNumeralTerm count) + 1) *
          !!(shortBinaryNumeralTerm tokenCount)” := by
  let rightTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm count) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  exact valuationLeCertificate
    (shortBinaryNumeralTerm boundarySize) rightTerm (by
      simpa [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticMul,
        termValue_arithmeticOne] using hbound)

noncomputable def compactUnifiedParserFinalStateRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat)
    (hgraph : CompactUnifiedParserFinalStateRows
      tokenTable width tokenCount coordinates sourceBoundary sourceCount
        outputStart outputBoundary outputBoundarySize) :
    HybridCertificate
      (compactUnifiedParserFinalStateRowsClosedFormula
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
          outputStart outputBoundary outputBoundarySize) := by
  rcases hgraph with ⟨⟨hprefix, hlayout, hsame⟩, hsize, harea⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactBinaryNatCompletedStatusPrefixExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates.tasksFinish outputStart hprefix)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
        tokenTable width tokenCount outputStart sourceCount
          coordinates.finish outputBoundary hlayout)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListSameRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount
            outputBoundary sourceCount hsame)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactNatSizeExplicitHybridCertificateOfEq
            outputBoundarySize outputBoundary hsize)
          (boundaryAreaCertificate outputBoundarySize sourceCount tokenCount
            harea))))
  exact .cast
    (compactUnifiedParserFinalStateRowsClosedFormula_alignment
      tokenTable width tokenCount coordinates sourceBoundary sourceCount
        outputStart outputBoundary outputBoundarySize).symm parts

#print axioms compactUnifiedParserFinalStateRowsClosedFormula_alignment
#print axioms compactUnifiedParserFinalStateRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
