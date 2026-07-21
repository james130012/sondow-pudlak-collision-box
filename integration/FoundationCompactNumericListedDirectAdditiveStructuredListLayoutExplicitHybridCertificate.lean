import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificates for additive structured-list layouts

The boundary-table constructor receives both endpoint rows and a deterministic
row provider.  Each bounded-universal branch installs its left and right
witnesses explicitly.  The structured-list constructor likewise installs the
supplied body start and composes the public list-header certificate with the
boundary-table certificate.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

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
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_termOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiterm.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting (operator.operator terms) =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiterm.Operator.operator
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting (Rew.subst terms (Rew.emb operator.term)) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity)) operator.term := by
      rw [Rew.comp_app, Rew.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity)) operator.term := by
      rw [hcomposition]
    _ = Rew.subst (rewriting ∘ terms) (Rew.emb operator.term) := by
      rw [Rew.comp_app]

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

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  let composite :=
    ((Rew.free (L := ℒₒᵣ) (n := 1)).comp Rew.bShift).comp Rew.bShift
  have h := Semiterm.rew_eq_of_funEqOn
    composite Rew.bShift (shortBinaryNumeralTerm value)
    (fun index => Fin.elim0 index)
    (fun index hindex => by
      have : index ∈ (shortBinaryNumeralTerm value).freeVariables := hindex
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [composite, Rew.comp_app] using h

private theorem subst_q_free_bShift3_shortBinaryNumeralTerm
    (witness value : Nat) :
    (Rew.subst ![shortBinaryNumeralTerm witness]).q
        ((Rew.free (L := ℒₒᵣ) (n := 2))
          (Rew.bShift (Rew.bShift
            (Rew.bShift (shortBinaryNumeralTerm value))))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  let leftRewriting : Rew ℒₒᵣ Nat 0 Nat 1 :=
    ((Rew.subst ![shortBinaryNumeralTerm witness]).q.comp
      (Rew.free (L := ℒₒᵣ) (n := 2))).comp
        ((Rew.bShift : Rew ℒₒᵣ Nat 2 Nat 3).comp
          ((Rew.bShift : Rew ℒₒᵣ Nat 1 Nat 2).comp
            (Rew.bShift : Rew ℒₒᵣ Nat 0 Nat 1)))
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat 1 := Rew.bShift
  have h := Semiterm.rew_eq_of_funEqOn
    leftRewriting rightRewriting (shortBinaryNumeralTerm value)
    (fun coordinate => Fin.elim0 coordinate)
    (fun coordinate hcoordinate => by
      have : coordinate ∈
          (shortBinaryNumeralTerm value).freeVariables := hcoordinate
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [leftRewriting, rightRewriting, Rew.comp_app] using h

@[simp] private theorem free_bvar_two_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#2 : ArithmeticSemiterm Nat 3) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 2)) (#(Fin.last 2)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_one_fin3 :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (#1 : ArithmeticSemiterm Nat 3) = #1 := by
  rfl

@[simp] private theorem subst_q_bvar_one (term : ValuationTerm) :
    (Rew.subst ![term]).q (#1 : ArithmeticSemiterm Nat 2) =
      Rew.bShift term := by
  change (Rew.subst ![term]).q (#((0 : Fin 1).succ)) =
    Rew.bShift term
  rw [Rew.q_bvar_succ, Rew.subst_bvar]
  rfl

def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

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

@[simp] theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simp

/-- The five-coordinate boundary-table predicate closed by short numerals. -/
def compactAdditiveBoundaryTableClosedFormula
    (tokenCount partCount start finish boundaryTable : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveBoundaryTableDef.val) ⇜
    ![shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm partCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm boundaryTable]

def compactAdditiveBoundaryTableRowTerminal
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 3 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
        closedShift 3 (shortBinaryNumeralTerm tokenCount),
        (#2 : ArithmeticSemiterm Nat 3),
        (#1 : ArithmeticSemiterm Nat 3)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
          closedShift 3 (shortBinaryNumeralTerm tokenCount),
          ‘#2 + 1’,
          (#0 : ArithmeticSemiterm Nat 3)]) ⋏
      “#1 < #0”)

def compactAdditiveBoundaryTableRowBody
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 1 :=
  ((compactAdditiveBoundaryTableRowTerminal tokenCount boundaryTable).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount))

def compactAdditiveBoundaryTableExplicitFormula
    (tokenCount partCount start finish boundaryTable : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
    (“!!(shortBinaryNumeralTerm finish) ≤
        !!(shortBinaryNumeralTerm tokenCount)” ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm start) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm partCount)
            (shortBinaryNumeralTerm finish) ⋏
          (compactAdditiveBoundaryTableRowBody
            tokenCount boundaryTable).ballLT
              (shortBinaryNumeralTerm partCount))))

/-- Exact syntactic decomposition of the closed boundary-table predicate. -/
theorem compactAdditiveBoundaryTableClosedFormula_alignment
    (tokenCount partCount start finish boundaryTable : Nat) :
    compactAdditiveBoundaryTableClosedFormula
        tokenCount partCount start finish boundaryTable =
      compactAdditiveBoundaryTableExplicitFormula
        tokenCount partCount start finish boundaryTable := by
  unfold compactAdditiveBoundaryTableClosedFormula
  unfold compactAdditiveBoundaryTableExplicitFormula
  unfold compactAdditiveBoundaryTableRowBody
  unfold compactAdditiveBoundaryTableRowTerminal
  unfold compactAdditiveBoundaryTableDef
  unfold compactFixedWidthEntryAtValuationFormula
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT, rewriting_ballLT,
    ← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, unaryNumeralTerm]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
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
        congr 1
        · congr 1
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate

/-- All explicit data needed for one branch of the boundary-table universal. -/
structure CompactAdditiveBoundaryTableRowData
    (tokenCount boundaryTable index : Nat) where
  left : Nat
  right : Nat
  left_le : left ≤ tokenCount
  right_le : right ≤ tokenCount
  left_entry : CompactFixedWidthEntry
    boundaryTable tokenCount index left
  right_entry : CompactFixedWidthEntry
    boundaryTable tokenCount (index + 1) right
  left_lt_right : left < right

noncomputable def valuationLeCertificate
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hle : termValue valuation leftTerm ≤ termValue valuation rightTerm) :
    HybridCertificate valuation “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue valuation leftTerm = termValue valuation rightTerm then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue valuation leftTerm < termValue valuation rightTerm :=
      Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

noncomputable def closedLeCertificate
    (valuation : Nat -> Nat) (left right : Nat) (hle : left ≤ right) :
    HybridCertificate valuation
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” :=
  valuationLeCertificate valuation
    (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right) (by
      simpa only [termValue_shortBinaryNumeralTerm] using hle)

noncomputable def boundedWitnessGuardCertificate
    (valuation : Nat -> Nat) (value bound : Nat) (hvalue : value ≤ bound) :
    HybridCertificate valuation
      “!!(shortBinaryNumeralTerm value) <
        !!(shortBinaryNumeralTerm bound) + 1” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bound) + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm value, rightTerm] (by
      change termValue valuation (shortBinaryNumeralTerm value) <
        termValue valuation rightTerm
      simp only [rightTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne]
      omega)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

noncomputable def closedLtCertificate
    (valuation : Nat -> Nat) (left right : Nat) (hlt : left < right) :
    HybridCertificate valuation
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue valuation (shortBinaryNumeralTerm left) <
        termValue valuation (shortBinaryNumeralTerm right)
      simpa only [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (Semiformula.Operator.lt_def _ _).symm direct

def boundaryRowRightWitnessBody
    (tokenCount boundaryTable left : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm boundaryTable),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (&0 : ValuationTerm),
        Rew.bShift (shortBinaryNumeralTerm left)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm boundaryTable),
          Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (‘&0 + 1’ : ValuationTerm),
          (#0 : ArithmeticSemiterm Nat 1)]) ⋏
        “!!(Rew.bShift (shortBinaryNumeralTerm left)) < #0”))

theorem boundaryRowRightWitnessBody_subst
    (tokenCount boundaryTable left right : Nat) :
    (boundaryRowRightWitnessBody tokenCount boundaryTable left)/[
        shortBinaryNumeralTerm right] =
      (“!!(shortBinaryNumeralTerm right) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (&0 : ValuationTerm)
            (shortBinaryNumeralTerm left) ⋏
          (compactFixedWidthEntryAtValuationFormula
              (shortBinaryNumeralTerm boundaryTable)
              (shortBinaryNumeralTerm tokenCount)
              (‘&0 + 1’ : ValuationTerm)
              (shortBinaryNumeralTerm right) ⋏
            “!!(shortBinaryNumeralTerm left) <
              !!(shortBinaryNumeralTerm right)”))) := by
  unfold boundaryRowRightWitnessBody
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

def boundaryRowLeftWitnessBody
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    Rewriting.free
      ((compactAdditiveBoundaryTableRowTerminal tokenCount boundaryTable).bexsLTSucc
        (closedShift 2 (shortBinaryNumeralTerm tokenCount)))

theorem boundaryRowLeftWitnessBody_subst
    (tokenCount boundaryTable left : Nat) :
    (boundaryRowLeftWitnessBody tokenCount boundaryTable)/[
        shortBinaryNumeralTerm left] =
      (“!!(shortBinaryNumeralTerm left) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (∃⁰ (boundaryRowRightWitnessBody tokenCount boundaryTable left))) := by
  unfold boundaryRowLeftWitnessBody
  unfold boundaryRowRightWitnessBody
  unfold compactAdditiveBoundaryTableRowTerminal
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT, closedShift,
    ← TransitiveRewriting.comp_app]
  congr 1
  · simp only [subst_q_free_bShift3_shortBinaryNumeralTerm]
  · congr 1
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar,
            subst_q_free_bShift3_shortBinaryNumeralTerm]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar,
            subst_q_free_bShift3_shortBinaryNumeralTerm]
      · intro coordinate
        exact Empty.elim coordinate

theorem boundaryRowBody_free_alignment
    (tokenCount boundaryTable : Nat) :
    Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable) =
      ∃⁰ (boundaryRowLeftWitnessBody tokenCount boundaryTable) := by
  unfold compactAdditiveBoundaryTableRowBody
  unfold boundaryRowLeftWitnessBody
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT, closedShift]
  rfl

noncomputable def boundaryRowBranchCertificate
    (tokenCount boundaryTable index : Nat)
    (data : CompactAdditiveBoundaryTableRowData
      tokenCount boundaryTable index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)) := by
  let valuation := extendValuation index zeroValuation
  let indexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let leftTerm := shortBinaryNumeralTerm data.left
  let rightTerm := shortBinaryNumeralTerm data.right
  let terminal :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate
      valuation (shortBinaryNumeralTerm boundaryTable)
      (shortBinaryNumeralTerm tokenCount) indexTerm leftTerm (by
        simpa [valuation, indexTerm, leftTerm, zeroValuation,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.left_entry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation (shortBinaryNumeralTerm boundaryTable)
        (shortBinaryNumeralTerm tokenCount) nextIndexTerm rightTerm (by
          simpa [valuation, nextIndexTerm, rightTerm, zeroValuation,
            termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
            termValue_arithmeticOne,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.right_entry))
      (closedLtCertificate valuation data.left data.right data.left_lt_right))
  let rightGuarded :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (boundedWitnessGuardCertificate valuation data.right tokenCount data.right_le)
    terminal
  let rightBody :=
    boundaryRowRightWitnessBody tokenCount boundaryTable data.left
  let rightInstalled : HybridCertificate valuation (∃⁰ rightBody) :=
    .existsWitness rightBody data.right (.cast
      (boundaryRowRightWitnessBody_subst tokenCount boundaryTable
        data.left data.right).symm rightGuarded)
  let leftGuarded :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (boundedWitnessGuardCertificate valuation data.left tokenCount data.left_le)
    rightInstalled
  exact .cast (boundaryRowBody_free_alignment
      tokenCount boundaryTable).symm
    (.existsWitness
      (boundaryRowLeftWitnessBody tokenCount boundaryTable) data.left
      (.cast (boundaryRowLeftWitnessBody_subst tokenCount boundaryTable
        data.left).symm leftGuarded))

/-- The concrete boundary-row branches before transporting the evaluated
short-numeral bound. -/
noncomputable def boundaryTableDirectHybridBranchesAtCount
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
      partCount :=
  buildExplicitHybridUniversalBranches partCount
    (fun index hindex => boundaryRowBranchCertificate tokenCount boundaryTable
      index (rows ⟨index, hindex⟩))

theorem boundaryTableShortNumeralBound_eq_partCount (partCount : Nat) :
    termValue zeroValuation (shortBinaryNumeralTerm partCount) =
      partCount := by
  exact termValue_shortBinaryNumeralTerm zeroValuation partCount

noncomputable def boundaryTableDirectHybridBranches
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveBoundaryTableRowBody tokenCount boundaryTable)
      (termValue zeroValuation (shortBinaryNumeralTerm partCount)) :=
  (boundaryTableShortNumeralBound_eq_partCount partCount).symm ▸
    boundaryTableDirectHybridBranchesAtCount
      tokenCount partCount boundaryTable rows

noncomputable def boundaryTableUniversalCertificate
    (tokenCount partCount boundaryTable : Nat)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      ((compactAdditiveBoundaryTableRowBody tokenCount boundaryTable).ballLT
        (shortBinaryNumeralTerm partCount)) := by
  let body := compactAdditiveBoundaryTableRowBody tokenCount boundaryTable
  let branches := boundaryTableDirectHybridBranches
    tokenCount partCount boundaryTable rows
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm partCount) body branches
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm partCount)) body) =
        body.ballLT (shortBinaryNumeralTerm partCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Audit-clean constructor for the closed additive boundary-table formula. -/
noncomputable def compactAdditiveBoundaryTableExplicitHybridCertificate
    (tokenCount partCount start finish boundaryTable : Nat)
    (hstartBound : start ≤ tokenCount)
    (hfinishBound : finish ≤ tokenCount)
    (hstartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 start)
    (hfinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount partCount finish)
    (rows : (index : Fin partCount) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      (compactAdditiveBoundaryTableClosedFormula
        tokenCount partCount start finish boundaryTable) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLeCertificate zeroValuation start tokenCount hstartBound)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLeCertificate zeroValuation finish tokenCount hfinishBound)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm start) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_unaryNumeralTerm] using hstartEntry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm partCount)
            (shortBinaryNumeralTerm finish) (by
              simpa only [termValue_shortBinaryNumeralTerm] using hfinishEntry))
          (boundaryTableUniversalCertificate
            tokenCount partCount boundaryTable rows))))
  exact .cast
    (compactAdditiveBoundaryTableClosedFormula_alignment
      tokenCount partCount start finish boundaryTable).symm parts

/-- The seven-coordinate structured-list predicate closed by short numerals. -/
def compactAdditiveStructuredListLayoutClosedFormula
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveStructuredListLayoutDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm count,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm boundaryTable]

def compactAdditiveStructuredListLayoutWitnessBody
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (shortBinaryNumeralTerm start),
        Rew.bShift (shortBinaryNumeralTerm count),
        (#0 : ArithmeticSemiterm Nat 1)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveBoundaryTableDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm count),
          (#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm finish),
          Rew.bShift (shortBinaryNumeralTerm boundaryTable)]))

/-- Exact syntactic existential decomposition of the closed list layout. -/
theorem compactAdditiveStructuredListLayoutClosedFormula_alignment
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start count finish boundaryTable =
      ∃⁰ compactAdditiveStructuredListLayoutWitnessBody
        tokenTable width tokenCount start count finish boundaryTable := by
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactAdditiveStructuredListLayoutWitnessBody
  unfold compactAdditiveStructuredListLayoutDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

theorem compactAdditiveStructuredListLayoutWitnessBody_subst
    (tokenTable width tokenCount start count finish boundaryTable bodyStart :
      Nat) :
    (compactAdditiveStructuredListLayoutWitnessBody
      tokenTable width tokenCount start count finish boundaryTable)/[
        shortBinaryNumeralTerm bodyStart] =
      (“!!(shortBinaryNumeralTerm bodyStart) <
          !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
        (FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula
            tokenTable width tokenCount start count bodyStart ⋏
          compactAdditiveBoundaryTableClosedFormula
            tokenCount count bodyStart finish boundaryTable)) := by
  simp [compactAdditiveStructuredListLayoutWitnessBody,
    FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.compactAdditiveListHeaderClosedFormula,
    compactAdditiveBoundaryTableClosedFormula,
    ← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

/-- Audit-clean constructor for the closed additive structured-list layout. -/
noncomputable def compactAdditiveStructuredListLayoutExplicitHybridCertificate
    (tokenTable width tokenCount start count finish boundaryTable bodyStart : Nat)
    (hbodyStart : bodyStart ≤ tokenCount)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart)
    (hboundaryFinish : finish ≤ tokenCount)
    (hboundaryStartEntry : CompactFixedWidthEntry
      boundaryTable tokenCount 0 bodyStart)
    (hboundaryFinishEntry : CompactFixedWidthEntry
      boundaryTable tokenCount count finish)
    (rows : (index : Fin count) ->
      CompactAdditiveBoundaryTableRowData
        tokenCount boundaryTable index) :
    HybridCertificate zeroValuation
      (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start count finish boundaryTable) := by
  let witnessBody := compactAdditiveStructuredListLayoutWitnessBody
    tokenTable width tokenCount start count finish boundaryTable
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (boundedWitnessGuardCertificate zeroValuation bodyStart tokenCount
      hbodyStart)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveListHeaderExplicitHybridCertificate
        tokenTable width tokenCount start count bodyStart hheader)
      (compactAdditiveBoundaryTableExplicitHybridCertificate
        tokenCount count bodyStart finish boundaryTable
        hbodyStart hboundaryFinish hboundaryStartEntry
        hboundaryFinishEntry rows))
  let installed : HybridCertificate zeroValuation
      (witnessBody/[shortBinaryNumeralTerm bodyStart]) :=
    .cast
      (compactAdditiveStructuredListLayoutWitnessBody_subst
        tokenTable width tokenCount start count finish boundaryTable
        bodyStart).symm post
  let direct : HybridCertificate zeroValuation (∃⁰ witnessBody) :=
    .existsWitness witnessBody bodyStart installed
  exact .cast
    (compactAdditiveStructuredListLayoutClosedFormula_alignment
      tokenTable width tokenCount start count finish boundaryTable).symm
    direct

/-- Concrete witnesses extracted from one semantic structured-list layout. -/
structure CompactAdditiveStructuredListLayoutData
    (tokenTable width tokenCount start count finish boundaryTable : Nat) where
  bodyStart : Nat
  bodyStart_le_tokenCount : bodyStart <= tokenCount
  header : CompactAdditiveListHeader
    tokenTable width tokenCount start count bodyStart
  boundaryFinish_le_tokenCount : finish <= tokenCount
  boundaryStartEntry : CompactFixedWidthEntry
    boundaryTable tokenCount 0 bodyStart
  boundaryFinishEntry : CompactFixedWidthEntry
    boundaryTable tokenCount count finish
  rows : (index : Fin count) ->
    CompactAdditiveBoundaryTableRowData tokenCount boundaryTable index

/-- Name all choices made when a semantic structured-list layout is opened. -/
noncomputable def compactAdditiveStructuredListLayoutDataOfLayout
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable := by
  let bodyStart := Classical.choose hlayout
  have hbody := Classical.choose_spec hlayout
  have hboundary : CompactAdditiveBoundaryTable
      tokenCount count bodyStart finish boundaryTable := hbody.2.2
  have hrows := hboundary.2.2.2.2
  exact
    { bodyStart := bodyStart
      bodyStart_le_tokenCount := hbody.1
      header := hbody.2.1
      boundaryFinish_le_tokenCount := hboundary.2.1
      boundaryStartEntry := hboundary.2.2.1
      boundaryFinishEntry := hboundary.2.2.2.1
      rows := fun index => by
        let leftExists := hrows index index.isLt
        let left := Classical.choose leftExists
        have hleft := Classical.choose_spec leftExists
        let rightExists := hleft.2
        let right := Classical.choose rightExists
        have hright := Classical.choose_spec rightExists
        exact
          { left := left
            right := right
            left_le := hleft.1
            right_le := hright.1
            left_entry := hright.2.1
            right_entry := hright.2.2.1
            left_lt_right := hright.2.2.2 } }

/-- Build the certificate from a named semantic-witness package. -/
noncomputable def
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (data : CompactAdditiveStructuredListLayoutData
      tokenTable width tokenCount start count finish boundaryTable) :
    HybridCertificate zeroValuation
      (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start count finish boundaryTable) :=
  compactAdditiveStructuredListLayoutExplicitHybridCertificate
    tokenTable width tokenCount start count finish boundaryTable data.bodyStart
    data.bodyStart_le_tokenCount data.header
    data.boundaryFinish_le_tokenCount data.boundaryStartEntry
    data.boundaryFinishEntry data.rows

/-- Derive the explicit certificate directly from the concrete layout data. -/
noncomputable def
    compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout
    (tokenTable width tokenCount start count finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    HybridCertificate zeroValuation
      (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start count finish boundaryTable) := by
  exact compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData
    tokenTable width tokenCount start count finish boundaryTable
    (compactAdditiveStructuredListLayoutDataOfLayout
      tokenTable width tokenCount start count finish boundaryTable hlayout)

#print axioms compactAdditiveBoundaryTableClosedFormula
#print axioms compactAdditiveBoundaryTableClosedFormula_alignment
#print axioms compactAdditiveBoundaryTableExplicitHybridCertificate
#print axioms compactAdditiveStructuredListLayoutClosedFormula
#print axioms compactAdditiveStructuredListLayoutClosedFormula_alignment
#print axioms compactAdditiveStructuredListLayoutExplicitHybridCertificate
#print axioms compactAdditiveStructuredListLayoutDataOfLayout
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificateOfData
#print axioms
  compactAdditiveStructuredListLayoutExplicitHybridCertificateOfLayout

end FoundationCompactNumericListedDirectAdditiveStructuredListLayoutExplicitHybridCertificate
