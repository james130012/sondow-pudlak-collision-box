import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for natural-list witness rows

The closed eight-coordinate predicate is decomposed into its original four
conjuncts.  The graph constructor consumes each semantic field independently:
the structured layout, unit boundary rows, exact boundary-table size, and the
size bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

/-- The original eight-coordinate witness-row predicate closed by short numerals. -/
def compactAdditiveNatListWitnessRowsClosedFormula
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListWitnessRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm count,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm boundaryTable,
      shortBinaryNumeralTerm boundarySize]

/-- The four immediate conjuncts of the closed witness-row predicate. -/
def compactAdditiveNatListWitnessRowsPartsFormula
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) :
    ValuationFormula :=
  compactAdditiveStructuredListLayoutClosedFormula
      tokenTable width tokenCount start count finish boundaryTable ⋏
    (compactAdditiveUnitBoundaryRowsClosedFormula
        tokenCount count boundaryTable ⋏
      (binaryLengthAtValuationFormula
          (shortBinaryNumeralTerm boundarySize)
          (shortBinaryNumeralTerm boundaryTable) ⋏
        “!!(shortBinaryNumeralTerm boundarySize) ≤
            (!!(shortBinaryNumeralTerm count) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)”))

/-- Exact syntactic alignment with the original witness-row definition. -/
theorem compactAdditiveNatListWitnessRowsClosedFormula_alignment
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat) :
    compactAdditiveNatListWitnessRowsClosedFormula
        tokenTable width tokenCount start count finish boundaryTable
          boundarySize =
      compactAdditiveNatListWitnessRowsPartsFormula
        tokenTable width tokenCount start count finish boundaryTable
          boundarySize := by
  unfold compactAdditiveNatListWitnessRowsClosedFormula
  unfold compactAdditiveNatListWitnessRowsPartsFormula
  unfold compactAdditiveNatListWitnessRowsDef
  simp [compactAdditiveStructuredListLayoutClosedFormula,
    compactAdditiveUnitBoundaryRowsClosedFormula,
    compactNatSizeDef, binaryLengthAtValuationFormula,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
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
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

/-- Close the exact witness-row predicate directly from its semantic graph. -/
noncomputable def
    compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount start count finish boundaryTable
      boundarySize : Nat)
    (hrows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount start count finish boundaryTable
        boundarySize) :
    HybridCertificate
      (compactAdditiveNatListWitnessRowsClosedFormula
        tokenTable width tokenCount start count finish boundaryTable
          boundarySize) := by
  rw [compactAdditiveNatListWitnessRowsClosedFormula_alignment]
  rcases hrows with ⟨hlayout, hunit, hsizeEq, hsizeBound⟩
  let sizeBoundTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm count) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount start count finish boundaryTable hlayout)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveUnitBoundaryRowsExplicitHybridCertificateOfGraph
        tokenCount count boundaryTable hunit)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (.binaryLength zeroValuation
          (shortBinaryNumeralTerm boundarySize)
          (shortBinaryNumeralTerm boundaryTable) (by
            simpa [termValue_shortBinaryNumeralTerm] using hsizeEq))
        (valuationLeCertificate
          (shortBinaryNumeralTerm boundarySize) sizeBoundTerm (by
            simpa [sizeBoundTerm, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticMul,
              termValue_arithmeticOne] using hsizeBound))))
  simpa only [compactAdditiveNatListWitnessRowsPartsFormula, sizeBoundTerm,
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation] using parts

#print axioms compactAdditiveNatListWitnessRowsClosedFormula
#print axioms compactAdditiveNatListWitnessRowsPartsFormula
#print axioms compactAdditiveNatListWitnessRowsClosedFormula_alignment
#print axioms compactAdditiveNatListWitnessRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectNatListWitnessRowsExplicitHybridCertificate
