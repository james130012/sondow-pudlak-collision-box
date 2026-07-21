import integration.FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
import integration.FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificates for child-result list rows

The list-row constructor preserves the original exponential conjunct and
bounded universal.  Every live row branch installs all seven bounded
witnesses before certifying the two open-index entries and the child-result
core.  A second public constructor closes the fixed-row, fixed-Boolean
variant used by finish rows and installs its six bounded witnesses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierChildResultListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAEmbeddedPredicateFreeVariables

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

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

private theorem emb_comp_subst_eq_subst_comp_emb
    {predicateArity targetArity : Nat}
    (sourceTerms : Fin predicateArity ->
      ArithmeticSemiterm Empty targetArity)
    (targetTerms : Fin predicateArity ->
      ArithmeticSemiterm Nat targetArity)
    (hterms : ∀ coordinate,
      (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity)
          (sourceTerms coordinate) = targetTerms coordinate) :
    (Rew.emb : Rew ℒₒᵣ Empty targetArity Nat targetArity).comp
        (Rew.subst sourceTerms) =
      (Rew.subst targetTerms).comp
        (Rew.emb : Rew ℒₒᵣ Empty predicateArity Nat predicateArity) := by
  apply Rew.ext
  · intro coordinate
    simpa [Rew.comp_app, Rew.subst_bvar] using hterms coordinate
  · intro coordinate
    exact Empty.elim coordinate

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

@[simp] private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

private def sourceSubstitutionQpow
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    (depth : Nat) ->
      Rew ℒₒᵣ Nat (sourceArity + depth) Nat (targetArity + depth)
  | 0 => Rew.subst terms
  | depth + 1 => (sourceSubstitutionQpow terms depth).q

private def sourceSubstitutionLift
    {targetArity : Nat} :
    (depth : Nat) -> ArithmeticSemiterm Nat targetArity ->
      ArithmeticSemiterm Nat (targetArity + depth)
  | 0, term => term
  | depth + 1, term =>
      Rew.bShift (sourceSubstitutionLift depth term)

private def sourceSubstitutionNormalizedBVarResult
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (index : Fin (sourceArity + depth)) :
    ArithmeticSemiterm Nat (targetArity + depth) :=
  if hlocal : index.val < depth then
    (#(⟨index.val, by omega⟩ : Fin (targetArity + depth)) :
      ArithmeticSemiterm Nat (targetArity + depth))
  else
    sourceSubstitutionLift depth
      (terms ⟨index.val - depth, by omega⟩)

private theorem sourceSubstitutionNormalizedBVarResult_eq
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity) :
    ∀ (depth : Nat) (index : Fin (sourceArity + depth)),
      sourceSubstitutionNormalizedBVarResult terms depth index =
        sourceSubstitutionQpow terms depth
          (#index : ArithmeticSemiterm Nat (sourceArity + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp [sourceSubstitutionNormalizedBVarResult,
        sourceSubstitutionQpow, sourceSubstitutionLift,
        Rew.subst_bvar]
  | succ depth inductionHypothesis =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [sourceSubstitutionNormalizedBVarResult,
            sourceSubstitutionQpow]
      | succ index =>
          rw [show
            sourceSubstitutionQpow terms (depth + 1)
                (#index.succ : ArithmeticSemiterm Nat
                  (sourceArity + (depth + 1))) =
              Rew.bShift
                (sourceSubstitutionQpow terms depth
                  (#index : ArithmeticSemiterm Nat
                    (sourceArity + depth))) by
            change (sourceSubstitutionQpow terms depth).q
                (#index.succ) = _
            rw [Rew.q_bvar_succ]]
          rw [← inductionHypothesis index]
          by_cases hlocal : index.val < depth
          · have hlocalSucc : index.val + 1 < depth + 1 := by omega
            simp [sourceSubstitutionNormalizedBVarResult,
              hlocal, hlocalSucc]
          · have hlocalSucc : ¬index.val + 1 < depth + 1 := by omega
            simp [sourceSubstitutionNormalizedBVarResult,
              hlocal, hlocalSucc, sourceSubstitutionLift]

@[simp] private theorem sourceSubstitutionQpow_bvar
    {sourceArity targetArity : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (depth : Nat) (index : Fin (sourceArity + depth)) :
    sourceSubstitutionQpow terms depth
        (#index : ArithmeticSemiterm Nat (sourceArity + depth)) =
      sourceSubstitutionNormalizedBVarResult terms depth index :=
  (sourceSubstitutionNormalizedBVarResult_eq terms depth index).symm

@[simp] private theorem sourceSubstitutionQpow_bexsLTSucc
    {sourceArity targetArity depth : Nat}
    (terms : Fin sourceArity ->
      ArithmeticSemiterm Nat targetArity)
    (bound : ArithmeticSemiterm Nat (sourceArity + depth))
    (body : ArithmeticSemiformula Nat (sourceArity + (depth + 1))) :
    sourceSubstitutionQpow terms depth ▹ body.bexsLTSucc bound =
      (sourceSubstitutionQpow terms (depth + 1) ▹ body).bexsLTSucc
        (sourceSubstitutionQpow terms depth bound) := by
  simpa [sourceSubstitutionQpow] using
    (rewriting_bexsLTSucc
      (sourceSubstitutionQpow terms depth) bound body)

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) =
          Rew.id := by
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
            ((Rew.subst values).comp Rew.bShift)
              (closedShift k term) := by
                simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := inductionHypothesis _

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

@[simp] private theorem free_bShift3_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))) =
      Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value)) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 2 value)

@[simp] private theorem free_bShift4_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value))))) =
      Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 3 value)

@[simp] private theorem free_bShift5_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))))) =
      Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value)))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 4 value)

@[simp] private theorem free_bShift6_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 5))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm value))))))) =
      Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value))))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 5 value)

@[simp] private theorem free_bShift7_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 6))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm value)))))))) =
      Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm value)))))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 6 value)

@[simp] private theorem free_bShift8_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm value))))))))) =
      Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm value))))))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 7 value)

@[simp] private theorem free_bvar_seven_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#7 : ArithmeticSemiterm Nat 8) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 7))
      (#(Fin.last 7)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_six_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#6 : ArithmeticSemiterm Nat 8) = #6 := by
  exact Rew.free_bvar_castSucc (6 : Fin 7)

@[simp] private theorem free_bvar_five_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#5 : ArithmeticSemiterm Nat 8) = #5 := by
  exact Rew.free_bvar_castSucc (5 : Fin 7)

@[simp] private theorem free_bvar_four_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#4 : ArithmeticSemiterm Nat 8) = #4 := by
  exact Rew.free_bvar_castSucc (4 : Fin 7)

@[simp] private theorem free_bvar_three_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#3 : ArithmeticSemiterm Nat 8) = #3 := by
  exact Rew.free_bvar_castSucc (3 : Fin 7)

@[simp] private theorem free_bvar_two_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#2 : ArithmeticSemiterm Nat 8) = #2 := by
  exact Rew.free_bvar_castSucc (2 : Fin 7)

@[simp] private theorem free_bvar_one_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#1 : ArithmeticSemiterm Nat 8) = #1 := by
  exact Rew.free_bvar_castSucc (1 : Fin 7)

@[simp] private theorem free_bvar_zero_fin8 :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (#0 : ArithmeticSemiterm Nat 8) = #0 := by
  exact Rew.free_bvar_castSucc (0 : Fin 7)

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
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hle : termValue valuation leftTerm ≤
      termValue valuation rightTerm) :
    HybridCertificate valuation “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue valuation leftTerm =
      termValue valuation rightTerm then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue valuation leftTerm <
        termValue valuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

/-! ## Arbitrary-count list rows -/

/-- The original seven-coordinate list-row graph closed by short numerals. -/
def compactNumericChildResultListRowsClosedFormula
    (tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultListRowsGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm valueBoundary,
      shortBinaryNumeralTerm valueCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactNumericChildResultListRowsExponentialClosedFormula
    (tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm tableWidth]

/-- The row conjunction under the universal and all seven witnesses. -/
def compactNumericChildResultListRowsTerminal
    (tokenTable width tokenCount valueBoundary : Nat) :
    ArithmeticSemiformula Nat 8 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 8 (shortBinaryNumeralTerm valueBoundary),
        closedShift 8 (shortBinaryNumeralTerm tokenCount),
        (#7 : ArithmeticSemiterm Nat 8),
        (#6 : ArithmeticSemiterm Nat 8)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 8 (shortBinaryNumeralTerm valueBoundary),
          closedShift 8 (shortBinaryNumeralTerm tokenCount),
          ‘#7 + 1’,
          (#5 : ArithmeticSemiterm Nat 8)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactNumericChildResultCoreGraphDef.val) ⇜
        ![closedShift 8 (shortBinaryNumeralTerm tokenTable),
          closedShift 8 (shortBinaryNumeralTerm width),
          closedShift 8 (shortBinaryNumeralTerm tokenCount),
          (#6 : ArithmeticSemiterm Nat 8),
          (#5 : ArithmeticSemiterm Nat 8),
          (#4 : ArithmeticSemiterm Nat 8),
          (#3 : ArithmeticSemiterm Nat 8),
          (#2 : ArithmeticSemiterm Nat 8),
          (#1 : ArithmeticSemiterm Nat 8),
          (#0 : ArithmeticSemiterm Nat 8)]))

private def compactNumericChildResultListRowsRawTerminal :
    ArithmeticSemiformula Nat 13 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![(#10 : ArithmeticSemiterm Nat 13), #9, #12, #6]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![(#10 : ArithmeticSemiterm Nat 13), #9, ‘#12 + 1’, #5]) ⋏
      ((Rewriting.emb (ξ := Nat)
          compactNumericChildResultCoreGraphDef.val) ⇜
        ![(#7 : ArithmeticSemiterm Nat 13), #8, #9, #6, #5, #4,
          #3, #2, #1, #0]))

private def compactNumericChildResultListRowsRawBody :
    ArithmeticSemiformula Nat 6 :=
  (((((((compactNumericChildResultListRowsRawTerminal.bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 9)).bexsLTSucc
      (#6 : ArithmeticSemiterm Nat 8)).bexsLTSucc
      (#5 : ArithmeticSemiterm Nat 7)).bexsLTSucc
      (#4 : ArithmeticSemiterm Nat 6))

private theorem compactNumericChildResultBoundedRowDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowDef.val =
      compactNumericChildResultListRowsRawBody := by
  have hstart :
      (Rew.emb : Rew ℒₒᵣ Empty 13 Nat 13).comp
          (Rew.subst
            ![(#10 : ArithmeticSemiterm Empty 13), #9, #12, #6]) =
        (Rew.subst
          ![(#10 : ArithmeticSemiterm Nat 13), #9, #12, #6]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hfinish :
      (Rew.emb : Rew ℒₒᵣ Empty 13 Nat 13).comp
          (Rew.subst
            ![(#10 : ArithmeticSemiterm Empty 13), #9, ‘#12 + 1’, #5]) =
        (Rew.subst
          ![(#10 : ArithmeticSemiterm Nat 13), #9, ‘#12 + 1’, #5]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hcore :
      (Rew.emb : Rew ℒₒᵣ Empty 13 Nat 13).comp
          (Rew.subst
            ![(#7 : ArithmeticSemiterm Empty 13), #8, #9, #6, #5,
              #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#7 : ArithmeticSemiterm Nat 13), #8, #9, #6, #5,
            #4, #3, #2, #1, #0]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactNumericChildResultBoundedRowDef
  unfold compactNumericChildResultListRowsRawBody
  unfold compactNumericChildResultListRowsRawTerminal
  simp [rewriting_bexsLTSucc,
    rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hstart, hfinish, hcore]

private def compactNumericChildResultListRowsSourceTerms
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    Fin 6 -> ArithmeticSemiterm Nat 1 :=
  ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
    Rew.bShift (shortBinaryNumeralTerm width),
    Rew.bShift (shortBinaryNumeralTerm tokenCount),
    Rew.bShift (shortBinaryNumeralTerm valueBoundary),
    Rew.bShift (shortBinaryNumeralTerm valueBound),
    (#0 : ArithmeticSemiterm Nat 1)]

@[simp] private theorem
    compactNumericChildResultListRowsSourceQpow_valueBound
    (tokenTable width tokenCount valueBoundary valueBound depth : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) depth
        (#(⟨depth + 4, by omega⟩ : Fin (6 + depth)) :
          ArithmeticSemiterm Nat (6 + depth)) =
      sourceSubstitutionLift depth
        (Rew.bShift (shortBinaryNumeralTerm valueBound)) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactNumericChildResultListRowsSourceTerms]

private theorem compactNumericChildResultListRowsSourceQpow_bound0
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 0
        (#4 : ArithmeticSemiterm Nat 6) =
      closedShift 1 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 0)

private theorem compactNumericChildResultListRowsSourceQpow_bound1
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 1
        (#5 : ArithmeticSemiterm Nat 7) =
      closedShift 2 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 1)

private theorem compactNumericChildResultListRowsSourceQpow_bound2
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 2
        (#6 : ArithmeticSemiterm Nat 8) =
      closedShift 3 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 2)

private theorem compactNumericChildResultListRowsSourceQpow_bound3
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 3
        (#7 : ArithmeticSemiterm Nat 9) =
      closedShift 4 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 3)

private theorem compactNumericChildResultListRowsSourceQpow_bound4
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 4
        (#8 : ArithmeticSemiterm Nat 10) =
      closedShift 5 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 4)

private theorem compactNumericChildResultListRowsSourceQpow_bound5
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 5
        (#9 : ArithmeticSemiterm Nat 11) =
      closedShift 6 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 5)

private theorem compactNumericChildResultListRowsSourceQpow_bound6
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 6
        (#10 : ArithmeticSemiterm Nat 12) =
      closedShift 7 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultListRowsSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound 6)

private theorem compactNumericChildResultListRowsRawTerminal_rewriting
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 7 ▹
      compactNumericChildResultListRowsRawTerminal =
    compactNumericChildResultListRowsTerminal
      tokenTable width tokenCount valueBoundary := by
  unfold compactNumericChildResultListRowsRawTerminal
  unfold compactNumericChildResultListRowsTerminal
  simp [rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionQpow,
          Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
          Rew.comp_app, Rew.subst_bvar,
          compactNumericChildResultListRowsSourceTerms,
          sourceSubstitutionLift, closedShift]
    · intro coordinate
      exact Empty.elim coordinate

/-- The source row body with the original seven bounded existential binders. -/
def compactNumericChildResultListRowsBody
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (((((((compactNumericChildResultListRowsTerminal
      tokenTable width tokenCount valueBoundary).bexsLTSucc
        (closedShift 7 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 6 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 5 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm valueBound))

private def compactNumericChildResultListRowsSourceBody
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowDef.val) ⇜
    compactNumericChildResultListRowsSourceTerms
      tokenTable width tokenCount valueBoundary valueBound

private theorem compactNumericChildResultListRowsSourceBody_alignment
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    compactNumericChildResultListRowsSourceBody
        tokenTable width tokenCount valueBoundary valueBound =
      compactNumericChildResultListRowsBody
        tokenTable width tokenCount valueBoundary valueBound := by
  unfold compactNumericChildResultListRowsSourceBody
  rw [compactNumericChildResultBoundedRowDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactNumericChildResultListRowsSourceTerms
          tokenTable width tokenCount valueBoundary valueBound) 0 ▹
      compactNumericChildResultListRowsRawBody = _
  unfold compactNumericChildResultListRowsBody
  unfold compactNumericChildResultListRowsRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactNumericChildResultListRowsSourceQpow_bound0,
    compactNumericChildResultListRowsSourceQpow_bound1,
    compactNumericChildResultListRowsSourceQpow_bound2,
    compactNumericChildResultListRowsSourceQpow_bound3,
    compactNumericChildResultListRowsSourceQpow_bound4,
    compactNumericChildResultListRowsSourceQpow_bound5,
    compactNumericChildResultListRowsSourceQpow_bound6,
    compactNumericChildResultListRowsRawTerminal_rewriting]

def compactNumericChildResultListRowsExplicitFormula
    (tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound : Nat) : ValuationFormula :=
  compactNumericChildResultListRowsExponentialClosedFormula
      tableWidth valueBound ⋏
    (compactNumericChildResultListRowsBody
      tokenTable width tokenCount valueBoundary valueBound).ballLT
        (shortBinaryNumeralTerm valueCount)

/-- Exact syntactic decomposition of the original closed list-row graph. -/
theorem compactNumericChildResultListRowsClosedFormula_alignment
    (tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound : Nat) :
    compactNumericChildResultListRowsClosedFormula
        tokenTable width tokenCount valueBoundary valueCount
          tableWidth valueBound =
      compactNumericChildResultListRowsExplicitFormula
        tokenTable width tokenCount valueBoundary valueCount
          tableWidth valueBound := by
  unfold compactNumericChildResultListRowsExplicitFormula
  rw [← compactNumericChildResultListRowsSourceBody_alignment]
  unfold compactNumericChildResultListRowsClosedFormula
  unfold compactNumericChildResultListRowsExponentialClosedFormula
  unfold compactNumericChildResultListRowsSourceBody
  unfold compactNumericChildResultListRowsGraphDef
  simp [rewriting_ballLT, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [compactNumericChildResultListRowsSourceTerms,
          Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

/-- The row terminal after releasing the universal index as free variable 0. -/
def compactNumericChildResultListRowsBranchTerminal
    (tokenTable width tokenCount valueBoundary : Nat) :
    ArithmeticSemiformula Nat 7 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 7 (shortBinaryNumeralTerm valueBoundary),
        closedShift 7 (shortBinaryNumeralTerm tokenCount),
        closedShift 7 (&0 : ValuationTerm),
        (#6 : ArithmeticSemiterm Nat 7)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 7 (shortBinaryNumeralTerm valueBoundary),
          closedShift 7 (shortBinaryNumeralTerm tokenCount),
          closedShift 7 (‘&0 + 1’ : ValuationTerm),
          (#5 : ArithmeticSemiterm Nat 7)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactNumericChildResultCoreGraphDef.val) ⇜
        ![closedShift 7 (shortBinaryNumeralTerm tokenTable),
          closedShift 7 (shortBinaryNumeralTerm width),
          closedShift 7 (shortBinaryNumeralTerm tokenCount),
          (#6 : ArithmeticSemiterm Nat 7),
          (#5 : ArithmeticSemiterm Nat 7),
          (#4 : ArithmeticSemiterm Nat 7),
          (#3 : ArithmeticSemiterm Nat 7),
          (#2 : ArithmeticSemiterm Nat 7),
          (#1 : ArithmeticSemiterm Nat 7),
          (#0 : ArithmeticSemiterm Nat 7)]))

private theorem compactNumericChildResultListRowsTerminal_free_alignment
    (tokenTable width tokenCount valueBoundary : Nat) :
    Rewriting.free
        (compactNumericChildResultListRowsTerminal
          tokenTable width tokenCount valueBoundary) =
      compactNumericChildResultListRowsBranchTerminal
        tokenTable width tokenCount valueBoundary := by
  unfold compactNumericChildResultListRowsTerminal
  unfold compactNumericChildResultListRowsBranchTerminal
  simp [closedShift, free_bShift8_shortBinaryNumeralTerm,
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

/-- Releasing a row index exposes exactly seven bounded witnesses. -/
theorem compactNumericChildResultListRowsBody_free_alignment
    (tokenTable width tokenCount valueBoundary valueBound : Nat) :
    Rewriting.free
        (compactNumericChildResultListRowsBody
          tokenTable width tokenCount valueBoundary valueBound) =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm valueBound) 7
        (compactNumericChildResultListRowsBranchTerminal
          tokenTable width tokenCount valueBoundary) := by
  unfold compactNumericChildResultListRowsBody
  simp [explicitBoundedWitnessFormula,
    Rew.q_free, closedShift, shift_shortBinaryNumeralTerm,
    free_bShift2_shortBinaryNumeralTerm,
    free_bShift3_shortBinaryNumeralTerm,
    free_bShift4_shortBinaryNumeralTerm,
    free_bShift5_shortBinaryNumeralTerm,
    free_bShift6_shortBinaryNumeralTerm,
    free_bShift7_shortBinaryNumeralTerm,
    compactNumericChildResultListRowsTerminal_free_alignment]
  rfl

/-- Installing the seven row witnesses leaves the two open-index entries and
the exact closed child-result core. -/
theorem compactNumericChildResultListRowsBranchTerminal_substitution_alignment
    (tokenTable width tokenCount valueBoundary
      start finish gammaFinish gammaCount gammaBoundary boolValue
      gammaBoundarySize : Nat) :
    (compactNumericChildResultListRowsBranchTerminal
        tokenTable width tokenCount valueBoundary) ⇜
        ![shortBinaryNumeralTerm gammaBoundarySize,
          shortBinaryNumeralTerm boolValue,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm start] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm valueBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (&0 : ValuationTerm)
          (shortBinaryNumeralTerm start) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm valueBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘&0 + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm finish) ⋏
          compactNumericChildResultCoreClosedFormula
            tokenTable width tokenCount
            (compactNumericChildResultRowCoordinatesOf
              start finish gammaFinish gammaCount gammaBoundary boolValue)
            { gammaBoundarySize := gammaBoundarySize })) := by
  unfold compactNumericChildResultListRowsBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactNumericChildResultCoreClosedFormula
  unfold compactNumericChildResultRowCoordinatesOf
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

private theorem compactNumericChildResultCoreClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericChildResultRowCoordinates)
    (sizeWitness : CompactNumericChildResultSizeWitness) :
    (compactNumericChildResultCoreClosedFormula
      tokenTable width tokenCount coordinates sizeWitness).freeVariables =
        ∅ := by
  unfold compactNumericChildResultCoreClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

private noncomputable def
    compactNumericChildResultListRowsExponentialCertificate
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    HybridCertificate zeroValuation
      (compactNumericChildResultListRowsExponentialClosedFormula
        tableWidth valueBound) := by
  change HybridCertificate zeroValuation
    (exponentialAtValuationFormula
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))
  exact .exponential zeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

private noncomputable def compactNumericChildResultListRowsBranchCertificate
    (tokenTable width tokenCount valueBoundary valueBound rowIndex : Nat)
    (hrow : CompactNumericChildResultBoundedRow
      tokenTable width tokenCount valueBoundary valueBound rowIndex) :
    HybridCertificate (extendValuation rowIndex zeroValuation)
      (Rewriting.free
        (compactNumericChildResultListRowsBody
          tokenTable width tokenCount valueBoundary valueBound)) := by
  let start := Classical.choose hrow
  have hstartData := Classical.choose_spec hrow
  have hstart := hstartData.1
  let finish := Classical.choose hstartData.2
  have hfinishData := Classical.choose_spec hstartData.2
  have hfinish := hfinishData.1
  let gammaFinish := Classical.choose hfinishData.2
  have hgammaFinishData := Classical.choose_spec hfinishData.2
  have hgammaFinish := hgammaFinishData.1
  let gammaCount := Classical.choose hgammaFinishData.2
  have hgammaCountData := Classical.choose_spec hgammaFinishData.2
  have hgammaCount := hgammaCountData.1
  let gammaBoundary := Classical.choose hgammaCountData.2
  have hgammaBoundaryData := Classical.choose_spec hgammaCountData.2
  have hgammaBoundary := hgammaBoundaryData.1
  let boolValue := Classical.choose hgammaBoundaryData.2
  have hboolValueData := Classical.choose_spec hgammaBoundaryData.2
  have hboolValue := hboolValueData.1
  let gammaBoundarySize := Classical.choose hboolValueData.2
  have hgammaBoundarySizeData := Classical.choose_spec hboolValueData.2
  have hgammaBoundarySize := hgammaBoundarySizeData.1
  have hstartEntry := hgammaBoundarySizeData.2.1
  have hfinishEntry := hgammaBoundarySizeData.2.2.1
  have hcore := hgammaBoundarySizeData.2.2.2
  let valuation := extendValuation rowIndex zeroValuation
  let values : Fin 7 -> Nat :=
    ![gammaBoundarySize, boolValue, gammaBoundary, gammaCount,
      gammaFinish, finish, start]
  have hvalueTerms :
      (fun coordinate : Fin 7 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm gammaBoundarySize,
          shortBinaryNumeralTerm boolValue,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm start] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let coreAtZero :=
    compactNumericChildResultCoreExplicitHybridCertificate hcore
  let coreAtValuation := revalueClosedHybridCertificate coreAtZero
    (compactNumericChildResultCoreClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount
      (compactNumericChildResultRowCoordinatesOf
        start finish gammaFinish gammaCount gammaBoundary boolValue)
      { gammaBoundarySize := gammaBoundarySize }) valuation
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm valueBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (&0 : ValuationTerm)
        (shortBinaryNumeralTerm start) (by
          simpa [valuation, zeroValuation,
            termValue_shortBinaryNumeralTerm,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using hstartEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm valueBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘&0 + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm finish) (by
            simpa [valuation, zeroValuation,
              termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using hfinishEntry))
        coreAtValuation)
  let terminal : HybridCertificate valuation
      ((compactNumericChildResultListRowsBranchTerminal
          tokenTable width tokenCount valueBoundary) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactNumericChildResultListRowsBranchTerminal_substitution_alignment
          tokenTable width tokenCount valueBoundary
          start finish gammaFinish gammaCount gammaBoundary boolValue
          gammaBoundarySize).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate
    valueBound
    (compactNumericChildResultListRowsBranchTerminal
      tokenTable width tokenCount valueBoundary)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hgammaBoundarySize
      · exact hboolValue
      · exact hgammaBoundary
      · exact hgammaCount
      · exact hgammaFinish
      · exact hfinish
      · exact hstart) terminal
  exact .cast
    (compactNumericChildResultListRowsBody_free_alignment
      tokenTable width tokenCount valueBoundary valueBound).symm installed

private noncomputable def compactNumericChildResultListRowsUniversalCertificate
    (tokenTable width tokenCount valueBoundary valueCount valueBound : Nat)
    (hrows : ∀ rowIndex < valueCount,
      CompactNumericChildResultBoundedRow
        tokenTable width tokenCount valueBoundary valueBound rowIndex) :
    HybridCertificate zeroValuation
      ((compactNumericChildResultListRowsBody
        tokenTable width tokenCount valueBoundary valueBound).ballLT
          (shortBinaryNumeralTerm valueCount)) := by
  let body := compactNumericChildResultListRowsBody
    tokenTable width tokenCount valueBoundary valueBound
  let branches := buildExplicitHybridUniversalBranches valueCount
    (fun rowIndex hrowIndex =>
      compactNumericChildResultListRowsBranchCertificate
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          (hrows rowIndex hrowIndex))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm valueCount) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm valueCount)) body) =
        body.ballLT (shortBinaryNumeralTerm valueCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Public arbitrary-count constructor from the semantic list-row graph. -/
noncomputable def compactNumericChildResultListRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount valueBoundary valueCount
      tableWidth valueBound : Nat)
    (hgraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount valueBoundary valueCount
        tableWidth valueBound) :
    HybridCertificate zeroValuation
      (compactNumericChildResultListRowsClosedFormula
        tokenTable width tokenCount valueBoundary valueCount
          tableWidth valueBound) := by
  rw [compactNumericChildResultListRowsClosedFormula_alignment]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactNumericChildResultListRowsExponentialCertificate
      tableWidth valueBound hgraph.1)
    (compactNumericChildResultListRowsUniversalCertificate
      tokenTable width tokenCount valueBoundary valueCount valueBound
        hgraph.2)

/-! ## Fixed row with a prescribed Boolean value -/

/-- The original seven-coordinate fixed-row predicate closed by numerals. -/
def compactNumericChildResultBoundedRowWithBoolClosedFormula
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericChildResultBoundedRowWithBoolDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm valueBoundary,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm rowIndex,
      shortBinaryNumeralTerm expectedBool]

private def compactNumericChildResultBoundedRowWithBoolRawTerminal :
    ArithmeticSemiformula Nat 13 :=
  “#12 ≤ #10” ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![(#9 : ArithmeticSemiterm Nat 13), #8, #11, #5]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![(#9 : ArithmeticSemiterm Nat 13), #8, ‘#11 + 1’, #4]) ⋏
        ((Rewriting.emb (ξ := Nat)
            compactNumericChildResultCoreGraphDef.val) ⇜
          ![(#6 : ArithmeticSemiterm Nat 13), #7, #8, #5, #4, #3,
            #2, #1, #12, #0])))

private def compactNumericChildResultBoundedRowWithBoolRawBody :
    ArithmeticSemiformula Nat 7 :=
  ((((((compactNumericChildResultBoundedRowWithBoolRawTerminal.bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#6 : ArithmeticSemiterm Nat 9)).bexsLTSucc
      (#5 : ArithmeticSemiterm Nat 8)).bexsLTSucc
      (#4 : ArithmeticSemiterm Nat 7))

private theorem
    compactNumericChildResultBoundedRowWithBoolDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat)
        compactNumericChildResultBoundedRowWithBoolDef.val =
      compactNumericChildResultBoundedRowWithBoolRawBody := by
  have hstart :
      (Rew.emb : Rew ℒₒᵣ Empty 13 Nat 13).comp
          (Rew.subst
            ![(#9 : ArithmeticSemiterm Empty 13), #8, #11, #5]) =
        (Rew.subst
          ![(#9 : ArithmeticSemiterm Nat 13), #8, #11, #5]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hfinish :
      (Rew.emb : Rew ℒₒᵣ Empty 13 Nat 13).comp
          (Rew.subst
            ![(#9 : ArithmeticSemiterm Empty 13), #8, ‘#11 + 1’, #4]) =
        (Rew.subst
          ![(#9 : ArithmeticSemiterm Nat 13), #8, ‘#11 + 1’, #4]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hcore :
      (Rew.emb : Rew ℒₒᵣ Empty 13 Nat 13).comp
          (Rew.subst
            ![(#6 : ArithmeticSemiterm Empty 13), #7, #8, #5, #4,
              #3, #2, #1, #12, #0]) =
        (Rew.subst
          ![(#6 : ArithmeticSemiterm Nat 13), #7, #8, #5, #4,
            #3, #2, #1, #12, #0]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 10 Nat 10) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactNumericChildResultBoundedRowWithBoolDef
  unfold compactNumericChildResultBoundedRowWithBoolRawBody
  unfold compactNumericChildResultBoundedRowWithBoolRawTerminal
  simp [rewriting_bexsLTSucc,
    rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hstart, hfinish, hcore]

private def compactNumericChildResultBoundedRowWithBoolSourceTerms
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm valueBoundary,
    shortBinaryNumeralTerm valueBound,
    shortBinaryNumeralTerm rowIndex,
    shortBinaryNumeralTerm expectedBool]

@[simp] private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool depth : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) depth
        (#(⟨depth + 4, by omega⟩ : Fin (7 + depth)) :
          ArithmeticSemiterm Nat (7 + depth)) =
      sourceSubstitutionLift depth
        (shortBinaryNumeralTerm valueBound) := by
  rw [sourceSubstitutionQpow_bvar]
  simp [sourceSubstitutionNormalizedBVarResult,
    compactNumericChildResultBoundedRowWithBoolSourceTerms]

private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound0
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 0
        (#4 : ArithmeticSemiterm Nat 7) =
      closedShift 0 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool 0)

private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound1
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 1
        (#5 : ArithmeticSemiterm Nat 8) =
      closedShift 1 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool 1)

private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound2
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 2
        (#6 : ArithmeticSemiterm Nat 9) =
      closedShift 2 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool 2)

private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound3
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 3
        (#7 : ArithmeticSemiterm Nat 10) =
      closedShift 3 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool 3)

private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound4
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 4
        (#8 : ArithmeticSemiterm Nat 11) =
      closedShift 4 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool 4)

private theorem
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound5
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 5
        (#9 : ArithmeticSemiterm Nat 12) =
      closedShift 5 (shortBinaryNumeralTerm valueBound) := by
  simpa [sourceSubstitutionLift, closedShift] using
    (compactNumericChildResultBoundedRowWithBoolSourceQpow_valueBound
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool 5)

/-- The six-witness terminal, including the prescribed Boolean bound. -/
def compactNumericChildResultBoundedRowWithBoolTerminal
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) : ArithmeticSemiformula Nat 6 :=
  “!!(closedShift 6 (shortBinaryNumeralTerm expectedBool)) ≤
      !!(closedShift 6 (shortBinaryNumeralTerm valueBound))” ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 6 (shortBinaryNumeralTerm valueBoundary),
          closedShift 6 (shortBinaryNumeralTerm tokenCount),
          closedShift 6 (shortBinaryNumeralTerm rowIndex),
          (#5 : ArithmeticSemiterm Nat 6)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 6 (shortBinaryNumeralTerm valueBoundary),
            closedShift 6 (shortBinaryNumeralTerm tokenCount),
            closedShift 6
              (‘!!(shortBinaryNumeralTerm rowIndex) + 1’ : ValuationTerm),
            (#4 : ArithmeticSemiterm Nat 6)]) ⋏
        ((Rewriting.emb (ξ := Nat)
            compactNumericChildResultCoreGraphDef.val) ⇜
          ![closedShift 6 (shortBinaryNumeralTerm tokenTable),
            closedShift 6 (shortBinaryNumeralTerm width),
            closedShift 6 (shortBinaryNumeralTerm tokenCount),
            (#5 : ArithmeticSemiterm Nat 6),
            (#4 : ArithmeticSemiterm Nat 6),
            (#3 : ArithmeticSemiterm Nat 6),
            (#2 : ArithmeticSemiterm Nat 6),
            (#1 : ArithmeticSemiterm Nat 6),
            closedShift 6 (shortBinaryNumeralTerm expectedBool),
            (#0 : ArithmeticSemiterm Nat 6)])))

private theorem
    compactNumericChildResultBoundedRowWithBoolRawTerminal_rewriting
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 6 ▹
      compactNumericChildResultBoundedRowWithBoolRawTerminal =
    compactNumericChildResultBoundedRowWithBoolTerminal
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool := by
  unfold compactNumericChildResultBoundedRowWithBoolRawTerminal
  unfold compactNumericChildResultBoundedRowWithBoolTerminal
  simp [rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app,
    sourceSubstitutionQpow,
    Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
    compactNumericChildResultBoundedRowWithBoolSourceTerms,
    sourceSubstitutionLift, closedShift]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionQpow,
          Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
          Rew.comp_app, Rew.subst_bvar,
          compactNumericChildResultBoundedRowWithBoolSourceTerms,
          sourceSubstitutionLift, closedShift]
    · intro coordinate
      exact Empty.elim coordinate

def compactNumericChildResultBoundedRowWithBoolExplicitFormula
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) : ValuationFormula :=
  ((((((compactNumericChildResultBoundedRowWithBoolTerminal
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool).bexsLTSucc
      (closedShift 5 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 0 (shortBinaryNumeralTerm valueBound))

private theorem
    compactNumericChildResultBoundedRowWithBoolExplicitFormula_eq_boundedWitness
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    compactNumericChildResultBoundedRowWithBoolExplicitFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 6
        (compactNumericChildResultBoundedRowWithBoolTerminal
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) := by
  rfl

/-- Exact six-witness presentation of the fixed-row source formula. -/
theorem compactNumericChildResultBoundedRowWithBoolClosedFormula_alignment
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat) :
    compactNumericChildResultBoundedRowWithBoolClosedFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool =
      compactNumericChildResultBoundedRowWithBoolExplicitFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool := by
  unfold compactNumericChildResultBoundedRowWithBoolClosedFormula
  rw [compactNumericChildResultBoundedRowWithBoolDef_emb_eq_rawBody]
  change
    sourceSubstitutionQpow
        (compactNumericChildResultBoundedRowWithBoolSourceTerms
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) 0 ▹
      compactNumericChildResultBoundedRowWithBoolRawBody = _
  unfold compactNumericChildResultBoundedRowWithBoolExplicitFormula
  unfold compactNumericChildResultBoundedRowWithBoolRawBody
  simp only [sourceSubstitutionQpow_bexsLTSucc]
  rw [compactNumericChildResultBoundedRowWithBoolSourceQpow_bound0,
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound1,
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound2,
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound3,
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound4,
    compactNumericChildResultBoundedRowWithBoolSourceQpow_bound5,
    compactNumericChildResultBoundedRowWithBoolRawTerminal_rewriting]

/-- Substituting the six witnesses exposes the expected bound, entries, and
fixed-Boolean child-result core. -/
theorem
    compactNumericChildResultBoundedRowWithBoolTerminal_substitution_alignment
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool start finish gammaFinish gammaCount gammaBoundary
      gammaBoundarySize : Nat) :
    (compactNumericChildResultBoundedRowWithBoolTerminal
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool) ⇜
        ![shortBinaryNumeralTerm gammaBoundarySize,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm start] =
      (“!!(shortBinaryNumeralTerm expectedBool) ≤
          !!(shortBinaryNumeralTerm valueBound)” ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm valueBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm rowIndex)
            (shortBinaryNumeralTerm start) ⋏
          (compactFixedWidthEntryAtValuationFormula
              (shortBinaryNumeralTerm valueBoundary)
              (shortBinaryNumeralTerm tokenCount)
              (‘!!(shortBinaryNumeralTerm rowIndex) + 1’ : ValuationTerm)
              (shortBinaryNumeralTerm finish) ⋏
            compactNumericChildResultCoreClosedFormula
              tokenTable width tokenCount
              (compactNumericChildResultRowCoordinatesOf
                start finish gammaFinish gammaCount gammaBoundary
                  expectedBool)
              { gammaBoundarySize := gammaBoundarySize }))) := by
  unfold compactNumericChildResultBoundedRowWithBoolTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactNumericChildResultCoreClosedFormula
  unfold compactNumericChildResultRowCoordinatesOf
  simp [substitute_closedShift, ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

/-- Public fixed-row constructor used by finish-row certificates. -/
noncomputable def
    compactNumericChildResultBoundedRowWithBoolExplicitHybridCertificate
    (tokenTable width tokenCount valueBoundary valueBound rowIndex
      expectedBool : Nat)
    (hrow : CompactNumericChildResultBoundedRowWithBool
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool) :
    HybridCertificate zeroValuation
      (compactNumericChildResultBoundedRowWithBoolClosedFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool) := by
  let start := Classical.choose hrow
  have hstartData := Classical.choose_spec hrow
  have hstart := hstartData.1
  let finish := Classical.choose hstartData.2
  have hfinishData := Classical.choose_spec hstartData.2
  have hfinish := hfinishData.1
  let gammaFinish := Classical.choose hfinishData.2
  have hgammaFinishData := Classical.choose_spec hfinishData.2
  have hgammaFinish := hgammaFinishData.1
  let gammaCount := Classical.choose hgammaFinishData.2
  have hgammaCountData := Classical.choose_spec hgammaFinishData.2
  have hgammaCount := hgammaCountData.1
  let gammaBoundary := Classical.choose hgammaCountData.2
  have hgammaBoundaryData := Classical.choose_spec hgammaCountData.2
  have hgammaBoundary := hgammaBoundaryData.1
  let gammaBoundarySize := Classical.choose hgammaBoundaryData.2
  have hgammaBoundarySizeData :=
    Classical.choose_spec hgammaBoundaryData.2
  have hgammaBoundarySize := hgammaBoundarySizeData.1
  have hexpectedBool := hgammaBoundarySizeData.2.1
  have hstartEntry := hgammaBoundarySizeData.2.2.1
  have hfinishEntry := hgammaBoundarySizeData.2.2.2.1
  have hcore := hgammaBoundarySizeData.2.2.2.2
  let values : Fin 6 -> Nat :=
    ![gammaBoundarySize, gammaBoundary, gammaCount,
      gammaFinish, finish, start]
  have hvalueTerms :
      (fun coordinate : Fin 6 =>
        shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm gammaBoundarySize,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm start] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (valuationLeCertificate zeroValuation
        (shortBinaryNumeralTerm expectedBool)
        (shortBinaryNumeralTerm valueBound) (by
          simpa [termValue_shortBinaryNumeralTerm] using hexpectedBool))
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
            (‘!!(shortBinaryNumeralTerm rowIndex) + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm finish) (by
              simpa [zeroValuation, termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticOne]
                using hfinishEntry))
          (compactNumericChildResultCoreExplicitHybridCertificate
            hcore)))
  let terminal : HybridCertificate zeroValuation
      ((compactNumericChildResultBoundedRowWithBoolTerminal
          tokenTable width tokenCount valueBoundary valueBound rowIndex
            expectedBool) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactNumericChildResultBoundedRowWithBoolTerminal_substitution_alignment
          tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool start finish gammaFinish gammaCount gammaBoundary
          gammaBoundarySize).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate
    valueBound
    (compactNumericChildResultBoundedRowWithBoolTerminal
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact hgammaBoundarySize
      · exact hgammaBoundary
      · exact hgammaCount
      · exact hgammaFinish
      · exact hfinish
      · exact hstart) terminal
  let explicitInstalled : HybridCertificate zeroValuation
      (compactNumericChildResultBoundedRowWithBoolExplicitFormula
        tokenTable width tokenCount valueBoundary valueBound rowIndex
          expectedBool) := .cast
    (compactNumericChildResultBoundedRowWithBoolExplicitFormula_eq_boundedWitness
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool).symm installed
  exact .cast
    (compactNumericChildResultBoundedRowWithBoolClosedFormula_alignment
      tokenTable width tokenCount valueBoundary valueBound rowIndex
        expectedBool).symm explicitInstalled

#print axioms compactNumericChildResultListRowsClosedFormula_alignment
#print axioms compactNumericChildResultListRowsBody_free_alignment
#print axioms
  compactNumericChildResultListRowsBranchTerminal_substitution_alignment
#print axioms
  compactNumericChildResultListRowsExplicitHybridCertificateOfGraph
#print axioms
  compactNumericChildResultBoundedRowWithBoolClosedFormula_alignment
#print axioms
  compactNumericChildResultBoundedRowWithBoolTerminal_substitution_alignment
#print axioms
  compactNumericChildResultBoundedRowWithBoolExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierChildResultListRowsExplicitHybridCertificate
