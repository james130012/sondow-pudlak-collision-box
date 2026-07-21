import integration.FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
import integration.FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-!
# Explicit hybrid certificates for exposed child-result rows

This file closes every public coordinate of
`CompactNumericChildResultBoundedRowExposed` by a short numeral.  The
certificate is assembled directly from the seven public bounds, the two
fixed-width entries, and the child-result core graph.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectChildResultBoundedRowExposedExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

private abbrev zeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate.zeroValuation

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

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

/-- The exposed row predicate with all thirteen coordinates closed. -/
def compactNumericChildResultBoundedRowExposedClosedFormula
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericChildResultBoundedRowExposedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm valueBoundary,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm rowIndex,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm gammaFinish,
      shortBinaryNumeralTerm gammaCount,
      shortBinaryNumeralTerm gammaBoundary,
      shortBinaryNumeralTerm boolValue,
      shortBinaryNumeralTerm gammaBoundarySize]

private def compactNumericChildResultBoundedRowExposedPartsFormula
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat) : ValuationFormula :=
  (“!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm valueBound)” ⋏
    (“!!(shortBinaryNumeralTerm finish) ≤
        !!(shortBinaryNumeralTerm valueBound)” ⋏
      (“!!(shortBinaryNumeralTerm gammaFinish) ≤
          !!(shortBinaryNumeralTerm valueBound)” ⋏
        (“!!(shortBinaryNumeralTerm gammaCount) ≤
            !!(shortBinaryNumeralTerm valueBound)” ⋏
          (“!!(shortBinaryNumeralTerm gammaBoundary) ≤
              !!(shortBinaryNumeralTerm valueBound)” ⋏
            (“!!(shortBinaryNumeralTerm boolValue) ≤
                !!(shortBinaryNumeralTerm valueBound)” ⋏
              (“!!(shortBinaryNumeralTerm gammaBoundarySize) ≤
                  !!(shortBinaryNumeralTerm valueBound)” ⋏
                (compactFixedWidthEntryAtValuationFormula
                    (shortBinaryNumeralTerm valueBoundary)
                    (shortBinaryNumeralTerm tokenCount)
                    (shortBinaryNumeralTerm rowIndex)
                    (shortBinaryNumeralTerm start) ⋏
                  (compactFixedWidthEntryAtValuationFormula
                      (shortBinaryNumeralTerm valueBoundary)
                      (shortBinaryNumeralTerm tokenCount)
                      (‘!!(shortBinaryNumeralTerm rowIndex) + 1’ :
                        ValuationTerm)
                      (shortBinaryNumeralTerm finish) ⋏
                    compactNumericChildResultCoreClosedFormula
                      tokenTable width tokenCount
                      (compactNumericChildResultRowCoordinatesOf
                        start finish gammaFinish gammaCount gammaBoundary
                          boolValue)
                      { gammaBoundarySize := gammaBoundarySize })))))))))

theorem compactNumericChildResultBoundedRowExposedClosedFormula_alignment
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat) :
    compactNumericChildResultBoundedRowExposedClosedFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        start finish gammaFinish gammaCount gammaBoundary boolValue
          gammaBoundarySize =
      compactNumericChildResultBoundedRowExposedPartsFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        start finish gammaFinish gammaCount gammaBoundary boolValue
          gammaBoundarySize := by
  unfold compactNumericChildResultBoundedRowExposedClosedFormula
  unfold compactNumericChildResultBoundedRowExposedPartsFormula
  unfold compactNumericChildResultBoundedRowExposedDef
  simp [compactFixedWidthEntryAtValuationFormula,
    compactNumericChildResultCoreClosedFormula,
    compactNumericChildResultRowCoordinatesOf,
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

/-! The direct constructor below mirrors the semantic conjunction exactly. -/

noncomputable def
    compactNumericChildResultBoundedRowExposedExplicitHybridCertificate
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat)
    (hrow : CompactNumericChildResultBoundedRowExposed
      tokenTable width tokenCount valueBoundary valueBound rowIndex
      start finish gammaFinish gammaCount gammaBoundary boolValue
        gammaBoundarySize) :
    HybridCertificate
      (compactNumericChildResultBoundedRowExposedClosedFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
        start finish gammaFinish gammaCount gammaBoundary boolValue
          gammaBoundarySize) := by
  rcases hrow with
    ⟨hstart, hfinish, hgammaFinish, hgammaCount, hgammaBoundary,
      hboolValue, hgammaBoundarySize, hstartEntry, hfinishEntry, hcore⟩
  rw [compactNumericChildResultBoundedRowExposedClosedFormula_alignment]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (valuationLeCertificate
      (shortBinaryNumeralTerm start)
      (shortBinaryNumeralTerm valueBound) (by
        simpa [termValue_shortBinaryNumeralTerm] using hstart))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (valuationLeCertificate
        (shortBinaryNumeralTerm finish)
        (shortBinaryNumeralTerm valueBound) (by
          simpa [termValue_shortBinaryNumeralTerm] using hfinish))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (valuationLeCertificate
          (shortBinaryNumeralTerm gammaFinish)
          (shortBinaryNumeralTerm valueBound) (by
            simpa [termValue_shortBinaryNumeralTerm] using hgammaFinish))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (valuationLeCertificate
            (shortBinaryNumeralTerm gammaCount)
            (shortBinaryNumeralTerm valueBound) (by
              simpa [termValue_shortBinaryNumeralTerm] using hgammaCount))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (valuationLeCertificate
              (shortBinaryNumeralTerm gammaBoundary)
              (shortBinaryNumeralTerm valueBound) (by
                simpa [termValue_shortBinaryNumeralTerm] using
                  hgammaBoundary))
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (valuationLeCertificate
                (shortBinaryNumeralTerm boolValue)
                (shortBinaryNumeralTerm valueBound) (by
                  simpa [termValue_shortBinaryNumeralTerm] using hboolValue))
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (valuationLeCertificate
                  (shortBinaryNumeralTerm gammaBoundarySize)
                  (shortBinaryNumeralTerm valueBound) (by
                    simpa [termValue_shortBinaryNumeralTerm] using
                      hgammaBoundarySize))
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                    zeroValuation
                    (shortBinaryNumeralTerm valueBoundary)
                    (shortBinaryNumeralTerm tokenCount)
                    (shortBinaryNumeralTerm rowIndex)
                    (shortBinaryNumeralTerm start) (by
                      simpa [zeroValuation, termValue_shortBinaryNumeralTerm]
                        using hstartEntry))
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                      zeroValuation
                      (shortBinaryNumeralTerm valueBoundary)
                      (shortBinaryNumeralTerm tokenCount)
                      (‘!!(shortBinaryNumeralTerm rowIndex) + 1’ :
                        ValuationTerm)
                      (shortBinaryNumeralTerm finish) (by
                        simpa [zeroValuation, termValue_shortBinaryNumeralTerm,
                          termValue_arithmeticAdd, termValue_arithmeticOne]
                          using hfinishEntry))
                    (compactNumericChildResultCoreExplicitHybridCertificate
                      hcore)))))))))

#print axioms compactNumericChildResultBoundedRowExposedClosedFormula_alignment
#print axioms
  compactNumericChildResultBoundedRowExposedExplicitHybridCertificate

end FoundationCompactNumericListedDirectChildResultBoundedRowExposedExplicitHybridCertificate
