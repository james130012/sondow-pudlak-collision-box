import integration.FoundationCompactNumericListedDirectCrossTableFormulaSetSingleton
import integration.FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for a singleton cross-table formula set

The semantic graph supplies the positive row count and, for each live row,
the two bounded cursors and the cross-table slice data.  This file installs
those witnesses directly and never derives certificate payloads from formula
truth.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCrossTableFormulaSetSingletonExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectCrossTableFormulaSetSingleton
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches

private abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

private def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      (Rewriting.app right :
        ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
          ArithmeticSemiformula targetVariables targetArity) := by
  cases h
  rfl

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

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)),
            Rew.bShift bound] =
        ![(#0 : ArithmeticSemiterm targetVariables (targetArity + 1)),
          Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation arithmeticZeroTerm = 0 := by
  exact termValue_zero valuation ![]

/-- The original eight-coordinate graph closed by short binary numerals. -/
def compactCrossTableFormulaSetEqSingletonClosedFormula
    (actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactCrossTableFormulaSetEqSingletonDef.val) ⇜
    ![shortBinaryNumeralTerm actualTable,
      shortBinaryNumeralTerm actualWidth,
      shortBinaryNumeralTerm actualTokenCount,
      shortBinaryNumeralTerm actualBoundary,
      shortBinaryNumeralTerm actualCount,
      shortBinaryNumeralTerm formulaTable,
      shortBinaryNumeralTerm formulaWidth,
      shortBinaryNumeralTerm formulaTokenCount]

/-- The three row facts before the two bounded cursor witnesses close. -/
def compactCrossTableFormulaSetEqSingletonTerminal
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount : Nat) :
    ArithmeticSemiformula Nat 3 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 3 (shortBinaryNumeralTerm actualBoundary),
        closedShift 3 (shortBinaryNumeralTerm actualTokenCount),
        (#2 : ArithmeticSemiterm Nat 3),
        (#1 : ArithmeticSemiterm Nat 3)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm actualBoundary),
          closedShift 3 (shortBinaryNumeralTerm actualTokenCount),
          ‘#2 + 1’,
          (#0 : ArithmeticSemiterm Nat 3)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactFixedWidthCrossTableSlicesEqDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm actualTable),
          closedShift 3 (shortBinaryNumeralTerm actualWidth),
          closedShift 3 (shortBinaryNumeralTerm actualTokenCount),
          ‘#1 + 1’,
          (#0 : ArithmeticSemiterm Nat 3),
          closedShift 3 (shortBinaryNumeralTerm formulaTable),
          closedShift 3 (shortBinaryNumeralTerm formulaWidth),
          closedShift 3 (shortBinaryNumeralTerm formulaTokenCount),
          closedShift 3 (shortBinaryNumeralTerm 0),
          closedShift 3 (shortBinaryNumeralTerm formulaTokenCount)]))

/-- One row branch, with its two cursors bounded by `actualTokenCount`. -/
def compactCrossTableFormulaSetEqSingletonBody
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount : Nat) :
    ArithmeticSemiformula Nat 1 :=
  ((compactCrossTableFormulaSetEqSingletonTerminal
      actualTable actualWidth actualTokenCount actualBoundary
        formulaTable formulaWidth formulaTokenCount).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm actualTokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm actualTokenCount))

/-- Hand-unfolded positive-count and bounded-row presentation. -/
def compactCrossTableFormulaSetEqSingletonExplicitFormula
    (actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm 0) <
      !!(shortBinaryNumeralTerm actualCount)” ⋏
    (compactCrossTableFormulaSetEqSingletonBody
      actualTable actualWidth actualTokenCount actualBoundary
        formulaTable formulaWidth formulaTokenCount).ballLT
      (shortBinaryNumeralTerm actualCount)

/-- Exact syntactic alignment of the closed source graph and its manual form. -/
theorem compactCrossTableFormulaSetEqSingletonClosedFormula_alignment
    (actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount : Nat) :
    compactCrossTableFormulaSetEqSingletonClosedFormula
        actualTable actualWidth actualTokenCount actualBoundary actualCount
        formulaTable formulaWidth formulaTokenCount =
      compactCrossTableFormulaSetEqSingletonExplicitFormula
        actualTable actualWidth actualTokenCount actualBoundary actualCount
        formulaTable formulaWidth formulaTokenCount := by
  unfold compactCrossTableFormulaSetEqSingletonClosedFormula
  unfold compactCrossTableFormulaSetEqSingletonExplicitFormula
  unfold compactCrossTableFormulaSetEqSingletonBody
  unfold compactCrossTableFormulaSetEqSingletonTerminal
  unfold compactCrossTableFormulaSetEqSingletonDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    rewriting_ballLT, ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  constructor
  · simp [arithmeticZeroTerm,
      Semiterm.Operator.operator,
      Semiterm.Operator.numeral_zero,
      Semiterm.Operator.Zero.term_eq,
      Rew.func, Matrix.empty_eq]
  · congr 1
    congr 1
    congr 1
    congr 1
    congr 1
    congr 1
    · apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      · congr 1
        congr 1
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
        · intro coordinate
          exact Empty.elim coordinate
      · congr 1
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
        · intro coordinate
          exact Empty.elim coordinate

/-- The terminal exposed below the universal index. -/
def compactCrossTableFormulaSetEqSingletonBranchTerminal
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount : Nat) :
    ArithmeticSemiformula Nat 2 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 2 (shortBinaryNumeralTerm actualBoundary),
        closedShift 2 (shortBinaryNumeralTerm actualTokenCount),
        closedShift 2 (&0 : ValuationTerm),
        (#1 : ArithmeticSemiterm Nat 2)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm actualBoundary),
          closedShift 2 (shortBinaryNumeralTerm actualTokenCount),
          closedShift 2 (‘&0 + 1’),
          (#0 : ArithmeticSemiterm Nat 2)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactFixedWidthCrossTableSlicesEqDef.val) ⇜
        ![closedShift 2 (shortBinaryNumeralTerm actualTable),
          closedShift 2 (shortBinaryNumeralTerm actualWidth),
          closedShift 2 (shortBinaryNumeralTerm actualTokenCount),
          ‘#1 + 1’,
          (#0 : ArithmeticSemiterm Nat 2),
          closedShift 2 (shortBinaryNumeralTerm formulaTable),
          closedShift 2 (shortBinaryNumeralTerm formulaWidth),
          closedShift 2 (shortBinaryNumeralTerm formulaTokenCount),
          closedShift 2 (shortBinaryNumeralTerm 0),
          closedShift 2 (shortBinaryNumeralTerm formulaTokenCount)]))

private def closedShiftRewriting :
    (k : Nat) -> Rew ℒₒᵣ Nat 0 Nat k
  | 0 => Rew.id
  | k + 1 => Rew.bShift.comp (closedShiftRewriting k)

@[simp] private theorem closedShiftRewriting_apply
    (k : Nat) (term : ValuationTerm) :
    closedShiftRewriting k term = closedShift k term := by
  induction k with
  | zero => exact Rew.id_app term
  | succ k inductionHypothesis =>
      simp [closedShiftRewriting, closedShift, Rew.comp_app,
        inductionHypothesis]

@[simp] private theorem free_closedShift_shortBinaryNumeralTerm
    (k value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := k))
        (closedShift (k + 1) (shortBinaryNumeralTerm value)) =
      closedShift k (shortBinaryNumeralTerm value) := by
  let leftRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    (Rew.free (L := ℒₒᵣ) (n := k)).comp
      (closedShiftRewriting (k + 1))
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    closedShiftRewriting k
  have h := Semiterm.rew_eq_of_funEqOn
    leftRewriting rightRewriting (shortBinaryNumeralTerm value)
    (fun coordinate => Fin.elim0 coordinate)
    (fun coordinate hcoordinate => by
      have : coordinate ∈
          (shortBinaryNumeralTerm value).freeVariables := hcoordinate
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [leftRewriting, rightRewriting, Rew.comp_app] using h

@[simp] private theorem shift_shortBinaryNumeralTerm (value : Nat) :
    Rew.shift (shortBinaryNumeralTerm value) =
      shortBinaryNumeralTerm value := by
  simpa [closedShift, free_bShift_term] using
    (free_closedShift_shortBinaryNumeralTerm 0 value)

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 1 value)

@[simp] private theorem free_closedShift_arithmeticZeroTerm (k : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := k))
        (closedShift (k + 1) arithmeticZeroTerm) =
      closedShift k arithmeticZeroTerm := by
  let leftRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    (Rew.free (L := ℒₒᵣ) (n := k)).comp
      (closedShiftRewriting (k + 1))
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    closedShiftRewriting k
  have h := Semiterm.rew_eq_of_funEqOn
    leftRewriting rightRewriting arithmeticZeroTerm
    (fun coordinate => Fin.elim0 coordinate)
    (fun coordinate hcoordinate => by
      simpa [arithmeticZeroTerm] using hcoordinate)
  simpa [leftRewriting, rightRewriting, Rew.comp_app] using h

@[simp] private theorem free_bShift3_arithmeticZeroTerm :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (Rew.bShift (Rew.bShift (Rew.bShift arithmeticZeroTerm))) =
      Rew.bShift (Rew.bShift arithmeticZeroTerm) := by
  simpa [closedShift] using free_closedShift_arithmeticZeroTerm 2

@[simp] private theorem free_bvar_two_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#2 : ArithmeticSemiterm Nat 3) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 2)) (#(Fin.last 2)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_one_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#1 : ArithmeticSemiterm Nat 3) = #1 := by
  rfl

private theorem compactCrossTableFormulaSetEqSingletonTerminal_free_alignment
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount : Nat) :
    Rewriting.free
        (compactCrossTableFormulaSetEqSingletonTerminal
          actualTable actualWidth actualTokenCount actualBoundary
            formulaTable formulaWidth formulaTokenCount) =
      compactCrossTableFormulaSetEqSingletonBranchTerminal
        actualTable actualWidth actualTokenCount actualBoundary
          formulaTable formulaWidth formulaTokenCount := by
  unfold compactCrossTableFormulaSetEqSingletonTerminal
  unfold compactCrossTableFormulaSetEqSingletonBranchTerminal
  simp [closedShift, free_closedShift_arithmeticZeroTerm,
    free_bShift3_arithmeticZeroTerm,
    free_bvar_two_fin3, free_bvar_one_fin3,
    ← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate

/-- Releasing the row index exposes exactly the two bounded cursor witnesses. -/
private theorem explicitBoundedWitnessFormula_two
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 2) :
    explicitBoundedWitnessFormula bound 2 body =
      (body.bexsLTSucc (Rew.bShift bound)).bexsLTSucc bound := by
  rfl

theorem compactCrossTableFormulaSetEqSingletonBody_free_alignment
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount : Nat) :
    Rewriting.free
        (compactCrossTableFormulaSetEqSingletonBody
          actualTable actualWidth actualTokenCount actualBoundary
            formulaTable formulaWidth formulaTokenCount) =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm actualTokenCount) 2
        (compactCrossTableFormulaSetEqSingletonBranchTerminal
          actualTable actualWidth actualTokenCount actualBoundary
            formulaTable formulaWidth formulaTokenCount) := by
  rw [explicitBoundedWitnessFormula_two]
  unfold compactCrossTableFormulaSetEqSingletonBody
  simp [Rew.q_free, closedShift,
    compactCrossTableFormulaSetEqSingletonTerminal_free_alignment]

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin k => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift) (closedShift k term) := by
              simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := inductionHypothesis _

/-- Substitution of the two explicit cursor witnesses exposes the two entries
and the arbitrary-valuation cross-table certificate target. -/
theorem compactCrossTableFormulaSetEqSingletonBranchTerminal_substitution_alignment
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount
      formulaStart formulaFinish : Nat) :
    (compactCrossTableFormulaSetEqSingletonBranchTerminal
        actualTable actualWidth actualTokenCount actualBoundary
          formulaTable formulaWidth formulaTokenCount) ⇜
        ![shortBinaryNumeralTerm formulaFinish,
          shortBinaryNumeralTerm formulaStart] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm actualBoundary)
          (shortBinaryNumeralTerm actualTokenCount)
          (&0 : ValuationTerm)
          (shortBinaryNumeralTerm formulaStart) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm actualBoundary)
            (shortBinaryNumeralTerm actualTokenCount)
            (‘&0 + 1’)
            (shortBinaryNumeralTerm formulaFinish) ⋏
          compactFixedWidthCrossTableSlicesEqAtValuationFormula
            (shortBinaryNumeralTerm actualTable)
            (shortBinaryNumeralTerm actualWidth)
            (shortBinaryNumeralTerm actualTokenCount)
            (‘!!(shortBinaryNumeralTerm formulaStart) + 1’)
            (shortBinaryNumeralTerm formulaFinish)
            (shortBinaryNumeralTerm formulaTable)
            (shortBinaryNumeralTerm formulaWidth)
            (shortBinaryNumeralTerm formulaTokenCount)
            (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm formulaTokenCount))) := by
  unfold compactCrossTableFormulaSetEqSingletonBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactFixedWidthCrossTableSlicesEqAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
      · intro coordinate
        exact Empty.elim coordinate

private noncomputable def positiveActualCountCertificate
    (actualCount : Nat) (hpositive : 0 < actualCount) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm 0) <
        !!(shortBinaryNumeralTerm actualCount)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm 0, shortBinaryNumeralTerm actualCount] (by
      change termValue zeroValuation (shortBinaryNumeralTerm 0) <
        termValue zeroValuation (shortBinaryNumeralTerm actualCount)
      simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticZero]
        using hpositive)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def compactCrossTableFormulaSetEqSingletonBranchCertificate
    (actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount index : Nat)
    (hrow : ∃ formulaStart, formulaStart ≤ actualTokenCount ∧
      ∃ formulaFinish, formulaFinish ≤ actualTokenCount ∧
        CompactFixedWidthEntry actualBoundary actualTokenCount
          index formulaStart ∧
        CompactFixedWidthEntry actualBoundary actualTokenCount
          (index + 1) formulaFinish ∧
        CompactFixedWidthCrossTableSlicesEq
          actualTable actualWidth actualTokenCount
            (formulaStart + 1) formulaFinish
          formulaTable formulaWidth formulaTokenCount 0 formulaTokenCount) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (compactCrossTableFormulaSetEqSingletonBody
          actualTable actualWidth actualTokenCount actualBoundary
            formulaTable formulaWidth formulaTokenCount)) := by
  let formulaStart := Classical.choose hrow
  have hformulaStartData := Classical.choose_spec hrow
  let formulaFinish := Classical.choose hformulaStartData.2
  have hformulaFinishData := Classical.choose_spec hformulaStartData.2
  have hstartBound := hformulaStartData.1
  have hfinishBound := hformulaFinishData.1
  have hstartEntry := hformulaFinishData.2.1
  have hfinishEntry := hformulaFinishData.2.2.1
  have hcross := hformulaFinishData.2.2.2
  let valuation := extendValuation index zeroValuation
  let count := Classical.choose hcross
  have hcrossData := Classical.choose_spec hcross
  have hsourceCountBound := hcrossData.1
  have htargetCountBound := hcrossData.2.1
  have hsourceEndpoint := hcrossData.2.2.1
  have htargetEndpoint := hcrossData.2.2.2.1
  have hsourceFinishBound := hcrossData.2.2.2.2.1
  have htargetFinishBound := hcrossData.2.2.2.2.2.1
  have hbits := hcrossData.2.2.2.2.2.2
  let values : Fin 2 -> Nat := ![formulaFinish, formulaStart]
  have hvalueTerms :
      (fun coordinate : Fin 2 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm formulaFinish,
          shortBinaryNumeralTerm formulaStart] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let cross :=
    compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
      valuation
      (shortBinaryNumeralTerm actualTable)
      (shortBinaryNumeralTerm actualWidth)
      (shortBinaryNumeralTerm actualTokenCount)
      (‘!!(shortBinaryNumeralTerm formulaStart) + 1’)
      (shortBinaryNumeralTerm formulaFinish)
      (shortBinaryNumeralTerm formulaTable)
      (shortBinaryNumeralTerm formulaWidth)
      (shortBinaryNumeralTerm formulaTokenCount)
      (shortBinaryNumeralTerm 0)
      (shortBinaryNumeralTerm formulaTokenCount)
      count (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero]
          using hsourceCountBound) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero]
          using htargetCountBound) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          termValue_arithmeticZero]
          using hsourceEndpoint) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero]
          using htargetEndpoint) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero]
          using hsourceFinishBound) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticZero]
          using htargetFinishBound) (by
        simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne,
          termValue_arithmeticZero]
          using hbits)
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm actualBoundary)
        (shortBinaryNumeralTerm actualTokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm formulaStart) (by
          simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using hstartEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm actualBoundary)
          (shortBinaryNumeralTerm actualTokenCount)
          (‘&0 + 1’)
          (shortBinaryNumeralTerm formulaFinish) (by
            simpa [valuation, zeroValuation, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using hfinishEntry))
        cross)
  let terminal : HybridCertificate valuation
      ((compactCrossTableFormulaSetEqSingletonBranchTerminal
          actualTable actualWidth actualTokenCount actualBoundary
            formulaTable formulaWidth formulaTokenCount) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactCrossTableFormulaSetEqSingletonBranchTerminal_substitution_alignment
          actualTable actualWidth actualTokenCount actualBoundary
          formulaTable formulaWidth formulaTokenCount
          formulaStart formulaFinish).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate
    actualTokenCount
    (compactCrossTableFormulaSetEqSingletonBranchTerminal
      actualTable actualWidth actualTokenCount actualBoundary
        formulaTable formulaWidth formulaTokenCount)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hfinishBound
      · exact hstartBound) terminal
  exact .cast
    (compactCrossTableFormulaSetEqSingletonBody_free_alignment
      actualTable actualWidth actualTokenCount actualBoundary
        formulaTable formulaWidth formulaTokenCount).symm installed

/-- Explicit checked hybrid certificate directly from the semantic graph. -/
noncomputable def compactCrossTableFormulaSetEqSingletonExplicitHybridCertificateOfGraph
    (actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount : Nat)
    (hgraph : CompactCrossTableFormulaSetEqSingleton
      actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount) :
    HybridCertificate zeroValuation
      (compactCrossTableFormulaSetEqSingletonClosedFormula
        actualTable actualWidth actualTokenCount actualBoundary actualCount
        formulaTable formulaWidth formulaTokenCount) := by
  have hpositive := hgraph.1
  have hrows := hgraph.2
  let body := compactCrossTableFormulaSetEqSingletonBody
    actualTable actualWidth actualTokenCount actualBoundary
      formulaTable formulaWidth formulaTokenCount
  let branches := buildExplicitHybridUniversalBranches actualCount
    (fun index hindex =>
      compactCrossTableFormulaSetEqSingletonBranchCertificate
        actualTable actualWidth actualTokenCount actualBoundary
        formulaTable formulaWidth formulaTokenCount index
        (hrows index hindex))
  let universal := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm actualCount) body (by
      simpa [termValue_shortBinaryNumeralTerm] using branches)
  let universalBall : HybridCertificate zeroValuation
      (body.ballLT (shortBinaryNumeralTerm actualCount)) := .cast (by
        change (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm actualCount)) body) =
            body.ballLT (shortBinaryNumeralTerm actualCount)
        rw [termBoundedUniversal_eq_ball]
        rfl) universal
  exact .cast
    (compactCrossTableFormulaSetEqSingletonClosedFormula_alignment
      actualTable actualWidth actualTokenCount actualBoundary actualCount
      formulaTable formulaWidth formulaTokenCount).symm
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (positiveActualCountCertificate actualCount hpositive)
      universalBall)

#print axioms compactCrossTableFormulaSetEqSingletonClosedFormula_alignment
#print axioms compactCrossTableFormulaSetEqSingletonBody_free_alignment
#print axioms
  compactCrossTableFormulaSetEqSingletonBranchTerminal_substitution_alignment
#print axioms compactCrossTableFormulaSetEqSingletonExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectCrossTableFormulaSetSingletonExplicitHybridCertificate
