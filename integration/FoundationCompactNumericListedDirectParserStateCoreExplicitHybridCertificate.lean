import integration.FoundationCompactNumericListedDirectParserStateFormula
import integration.FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

/-!
# Explicit hybrid certificate for the numeric parser-state core

The public constructor consumes the original thirteen-coordinate core graph.
Its ten conjuncts are certified directly by the corresponding structural,
binary-length, and arithmetic leaves.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectAdditiveProductSplitExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatSizeExplicitHybridCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

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

def compactUnifiedParserStateCoreClosedFormula
    (tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactUnifiedParserStateCoreGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm tokensFinish,
      shortBinaryNumeralTerm tasksFinish,
      shortBinaryNumeralTerm tokensBoundary,
      shortBinaryNumeralTerm tokensCount,
      shortBinaryNumeralTerm tasksBoundary,
      shortBinaryNumeralTerm tasksCount,
      shortBinaryNumeralTerm tokensBoundarySize,
      shortBinaryNumeralTerm tasksBoundarySize]

def compactUnifiedParserStateCoreExplicitFormula
    (tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize : Nat) : ValuationFormula :=
  compactAdditiveProductSplitClosedFormula
      tokenCount start tokensFinish finish ⋏
    (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start tokensCount
          tokensFinish tokensBoundary ⋏
      (compactAdditiveUnitBoundaryRowsClosedFormula
          tokenCount tokensCount tokensBoundary ⋏
        (compactAdditiveProductSplitClosedFormula
            tokenCount tokensFinish tasksFinish finish ⋏
          (compactAdditiveStructuredListLayoutClosedFormula
              tokenTable width tokenCount tokensFinish tasksCount
                tasksFinish tasksBoundary ⋏
            (compactAdditiveTripleBoundaryRowsClosedFormula
                tokenCount tasksCount tasksBoundary ⋏
              (compactNatSizeClosedFormula
                  tokensBoundarySize tokensBoundary ⋏
                (“!!(shortBinaryNumeralTerm tokensBoundarySize) ≤
                    (!!(shortBinaryNumeralTerm tokensCount) + 1) *
                      !!(shortBinaryNumeralTerm tokenCount)” ⋏
                  (compactNatSizeClosedFormula
                      tasksBoundarySize tasksBoundary ⋏
                    “!!(shortBinaryNumeralTerm tasksBoundarySize) ≤
                      (!!(shortBinaryNumeralTerm tasksCount) + 1) *
                        !!(shortBinaryNumeralTerm tokenCount)”))))))))

theorem compactUnifiedParserStateCoreClosedFormula_alignment
    (tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      tokensBoundarySize tasksBoundarySize : Nat) :
    compactUnifiedParserStateCoreClosedFormula
        tokenTable width tokenCount start finish tokensFinish tasksFinish
        tokensBoundary tokensCount tasksBoundary tasksCount
        tokensBoundarySize tasksBoundarySize =
      compactUnifiedParserStateCoreExplicitFormula
        tokenTable width tokenCount start finish tokensFinish tasksFinish
        tokensBoundary tokensCount tasksBoundary tasksCount
        tokensBoundarySize tasksBoundarySize := by
  unfold compactUnifiedParserStateCoreClosedFormula
  unfold compactUnifiedParserStateCoreExplicitFormula
  unfold compactUnifiedParserStateCoreGraphDef
  unfold compactAdditiveProductSplitClosedFormula
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactAdditiveUnitBoundaryRowsClosedFormula
  unfold compactAdditiveTripleBoundaryRowsClosedFormula
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

noncomputable def valuationLeCertificate
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

noncomputable def boundaryAreaCertificate
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

noncomputable def compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    HybridCertificate
      (compactUnifiedParserStateCoreClosedFormula
        tokenTable width tokenCount
        coordinates.start coordinates.finish
        coordinates.tokensFinish coordinates.tasksFinish
        coordinates.tokensBoundary coordinates.tokensCount
        coordinates.tasksBoundary coordinates.tasksCount
        sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize) := by
  rcases hgraph with
    ⟨houter, htokensLayout, htokensRows,
      hinner, htasksLayout, htasksRows,
      htokensSize, htokensArea, htasksSize, htasksArea⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveProductSplitExplicitHybridCertificateOfGraph
      tokenCount coordinates.start coordinates.tokensFinish
        coordinates.finish houter)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
        tokenTable width tokenCount coordinates.start coordinates.tokensCount
          coordinates.tokensFinish coordinates.tokensBoundary htokensLayout)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
          tokenCount coordinates.tokensCount coordinates.tokensBoundary
            htokensRows)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveProductSplitExplicitHybridCertificateOfGraph
            tokenCount coordinates.tokensFinish coordinates.tasksFinish
              coordinates.finish hinner)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
              tokenTable width tokenCount coordinates.tokensFinish
                coordinates.tasksCount coordinates.tasksFinish
                coordinates.tasksBoundary htasksLayout)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveTripleBoundaryRowsExplicitHybridCertificateOfGraph
                tokenCount coordinates.tasksCount coordinates.tasksBoundary
                  htasksRows)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactNatSizeExplicitHybridCertificateOfEq
                  sizeWitness.tokensBoundarySize coordinates.tokensBoundary
                    htokensSize)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (boundaryAreaCertificate sizeWitness.tokensBoundarySize
                    coordinates.tokensCount tokenCount htokensArea)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactNatSizeExplicitHybridCertificateOfEq
                      sizeWitness.tasksBoundarySize coordinates.tasksBoundary
                        htasksSize)
                    (boundaryAreaCertificate sizeWitness.tasksBoundarySize
                      coordinates.tasksCount tokenCount htasksArea)))))))))
  exact .cast
    (compactUnifiedParserStateCoreClosedFormula_alignment
      tokenTable width tokenCount
      coordinates.start coordinates.finish
      coordinates.tokensFinish coordinates.tasksFinish
      coordinates.tokensBoundary coordinates.tokensCount
      coordinates.tasksBoundary coordinates.tasksCount
      sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize).symm parts

#print axioms compactUnifiedParserStateCoreClosedFormula_alignment
#print axioms compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
