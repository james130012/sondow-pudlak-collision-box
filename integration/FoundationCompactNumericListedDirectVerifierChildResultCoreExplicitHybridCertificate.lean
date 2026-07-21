import integration.FoundationCompactNumericListedDirectVerifierChildResultFormula
import integration.FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate

/-!
# Explicit hybrid certificates for verifier child-result cores

The fixed ten-coordinate instance is exposed as exactly five components: the
structured-list layout, its natural-list rows, the binary-length equation, the
closed area inequality, and the final Boolean slice.  The public constructor
consumes the concrete core graph and builds each certificate independently.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveOptionBoolExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

/-- The original ten-coordinate child-result core closed by short numerals. -/
def compactNumericChildResultCoreClosedFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericChildResultRowCoordinates)
    (sizeWitness : CompactNumericChildResultSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultCoreGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.gammaFinish,
      shortBinaryNumeralTerm coordinates.gammaCount,
      shortBinaryNumeralTerm coordinates.gammaBoundary,
      shortBinaryNumeralTerm coordinates.boolValue,
      shortBinaryNumeralTerm sizeWitness.gammaBoundarySize]

/-- The exact five immediate components of the closed child-result core. -/
def compactNumericChildResultCorePartsFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericChildResultRowCoordinates)
    (sizeWitness : CompactNumericChildResultSizeWitness) :
    ValuationFormula :=
  compactAdditiveStructuredListLayoutClosedFormula
      tokenTable width tokenCount coordinates.start coordinates.gammaCount
        coordinates.gammaFinish coordinates.gammaBoundary ⋏
    (compactAdditiveNatListListRowsClosedFormula
        tokenTable width tokenCount coordinates.gammaBoundary
          coordinates.gammaCount ⋏
      (binaryLengthAtValuationFormula
          (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
          (shortBinaryNumeralTerm coordinates.gammaBoundary) ⋏
        (“!!(shortBinaryNumeralTerm sizeWitness.gammaBoundarySize) ≤
            (!!(shortBinaryNumeralTerm coordinates.gammaCount) + 1) *
              !!(shortBinaryNumeralTerm tokenCount)” ⋏
          compactAdditiveBoolSliceClosedFormula
            tokenTable width tokenCount coordinates.gammaFinish
              coordinates.boolValue coordinates.finish)))

/-- Exact syntactic alignment of the closed core with its five components. -/
theorem compactNumericChildResultCoreClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericChildResultRowCoordinates)
    (sizeWitness : CompactNumericChildResultSizeWitness) :
    compactNumericChildResultCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness =
      compactNumericChildResultCorePartsFormula
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases coordinates with
    ⟨start, finish, gammaFinish, gammaCount, gammaBoundary, boolValue⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  unfold compactNumericChildResultCoreClosedFormula
  unfold compactNumericChildResultCorePartsFormula
  unfold compactNumericChildResultCoreGraphDef
  simp [compactAdditiveStructuredListLayoutClosedFormula,
    compactAdditiveNatListListRowsClosedFormula,
    compactNatSizeDef, binaryLengthAtValuationFormula,
    compactAdditiveBoolSliceClosedFormula,
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
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

/-- Build the genuine explicit certificate from the five fields of `hcore`. -/
noncomputable def compactNumericChildResultCoreExplicitHybridCertificate
    {tokenTable width tokenCount : Nat}
    {coordinates : CompactNumericChildResultRowCoordinates}
    {sizeWitness : CompactNumericChildResultSizeWitness}
    (hcore : CompactNumericChildResultCoreGraph
      tokenTable width tokenCount coordinates sizeWitness) :
    HybridCertificate
      (compactNumericChildResultCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness) := by
  rw [compactNumericChildResultCoreClosedFormula_alignment]
  rcases hcore with
    ⟨hlayout, hrows, hsize, hbound, hbool⟩
  let sizeBoundTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm coordinates.gammaCount) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
      tokenTable width tokenCount coordinates.start coordinates.gammaCount
        coordinates.gammaFinish coordinates.gammaBoundary hlayout)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveNatListListRowsExplicitHybridCertificate
        tokenTable width tokenCount coordinates.gammaBoundary
          coordinates.gammaCount hrows)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (.binaryLength zeroValuation
          (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
          (shortBinaryNumeralTerm coordinates.gammaBoundary) (by
            simpa [termValue_shortBinaryNumeralTerm] using hsize))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (valuationLeCertificate
            (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
            sizeBoundTerm (by
              simpa [sizeBoundTerm, termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticMul,
                termValue_arithmeticOne] using hbound))
          (compactAdditiveBoolSliceExplicitHybridCertificateOfSlice
            tokenTable width tokenCount coordinates.gammaFinish
              coordinates.boolValue coordinates.finish hbool))))
  simpa only [compactNumericChildResultCorePartsFormula, sizeBoundTerm,
    FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation,
    FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate.zeroValuation,
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.zeroValuation] using parts

#print axioms compactNumericChildResultCoreClosedFormula_alignment
#print axioms compactNumericChildResultCoreExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
