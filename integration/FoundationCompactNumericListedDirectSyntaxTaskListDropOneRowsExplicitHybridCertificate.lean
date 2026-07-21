import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for dropping a fixed native-numeral row count

Some original callers write the consumed count with a native arithmetic
numeral.  This file preserves that exact formula syntax instead of replacing
it with an extensionally equal short-binary numeral.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler

private abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left : ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
      ArithmeticSemiformula targetVariables targetArity) = Rewriting.app right := by
  cases h
  rfl

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity -> ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜ (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables predicateArity)) ▹
            formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity)) ▹
            formula := by rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜ (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem rewriting_formulaOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (operator : Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity -> ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms = operator.operator (rewriting ∘ terms) := by
  unfold Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables targetArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1))
    (bound : ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms : rewriting.q ∘
      ![(#0 : ArithmeticSemiterm sourceVariables (sourceArity + 1)), Rew.bShift bound] =
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

private def closedShift : (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator (Semiterm.Operator.numeral ℒₒᵣ value) ![]

@[simp] private theorem fixedNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm Semiterm.Operator.operator
  simp

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

@[simp] private theorem free_closedShift_fixedNumeralTerm
    (k value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := k))
        (closedShift (k + 1) (fixedNumeralTerm value)) =
      closedShift k (fixedNumeralTerm value) := by
  let leftRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    (Rew.free (L := ℒₒᵣ) (n := k)).comp
      (closedShiftRewriting (k + 1))
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat k :=
    closedShiftRewriting k
  have h := Semiterm.rew_eq_of_funEqOn
    leftRewriting rightRewriting (fixedNumeralTerm value)
    (fun coordinate => Fin.elim0 coordinate)
    (fun coordinate hcoordinate => by
      have : coordinate ∈ (fixedNumeralTerm value).freeVariables := hcoordinate
      rw [fixedNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [leftRewriting, rightRewriting, Rew.comp_app] using h

@[simp] private theorem free_bShift5_fixedNumeralTerm
    (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (fixedNumeralTerm value)))))) =
      Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
        (fixedNumeralTerm value)))) := by
  simpa [closedShift] using free_closedShift_fixedNumeralTerm 4 value

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      consumed : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListDropRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount, shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount, fixedNumeralTerm consumed]

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        ‘!!(closedShift 5 (fixedNumeralTerm consumed)) + #4’,
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 5 (shortBinaryNumeralTerm tokenCount),
          ‘(!!(closedShift 5 (fixedNumeralTerm consumed)) + #4) + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
            closedShift 5 (shortBinaryNumeralTerm tokenCount), #4,
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
              closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’,
              (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
              closedShift 5 (shortBinaryNumeralTerm width),
              closedShift 5 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]))))

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (((((compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary consumed).bexsLTSucc
        (closedShift 4 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount)))

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      consumed : Nat) :
    ValuationFormula :=
  “!!(fixedNumeralTerm consumed) ≤ !!(shortBinaryNumeralTerm sourceCount)” ⋏
    (“!!(shortBinaryNumeralTerm sourceCount) =
        !!(fixedNumeralTerm consumed) + !!(shortBinaryNumeralTerm targetCount)” ⋏
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary consumed).ballLT (shortBinaryNumeralTerm targetCount))

theorem compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      consumed : Nat) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount consumed =
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount consumed := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitFormula
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal
  unfold compactAdditiveSyntaxTaskListDropRowsDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT, rewriting_ballLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
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
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      · congr 1
        apply arithmeticRewritingApp_congr
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
        · intro coordinate
          exact Empty.elim coordinate
      · congr 1
        · congr 1
          apply arithmeticRewritingApp_congr
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate
        · congr 1
          apply arithmeticRewritingApp_congr
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        ‘!!(closedShift 4 (fixedNumeralTerm consumed)) + &0’,
        (#3 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          ‘(!!(closedShift 4 (fixedNumeralTerm consumed)) + &0) + 1’,
          (#2 : ArithmeticSemiterm Nat 4)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
            closedShift 4 (shortBinaryNumeralTerm tokenCount), &0,
            (#1 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
              closedShift 4 (shortBinaryNumeralTerm tokenCount), ‘&0 + 1’,
              (#0 : ArithmeticSemiterm Nat 4)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount), #3, #2, #1, #0]))))

theorem compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    Rewriting.free (compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary consumed) =
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary consumed := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [closedShift, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private def localExplicitBoundedWitnessFormulaFour
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 4) : ValuationFormula :=
  ((((body.bexsLTSucc (closedShift 3 bound)).bexsLTSucc
      (closedShift 2 bound)).bexsLTSucc
    (closedShift 1 bound)).bexsLTSucc bound)

theorem compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    Rewriting.free (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary consumed) =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary consumed) := by
  calc
    Rewriting.free (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary consumed) =
      localExplicitBoundedWitnessFormulaFour (shortBinaryNumeralTerm tokenCount)
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary consumed) := by
      unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody
      unfold localExplicitBoundedWitnessFormulaFour
      simp [Rew.q_free, closedShift,
        compactAdditiveSyntaxTaskListDropFixedNumeralRowsTerminal_free_alignment]
    _ = explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary consumed) := by rfl

private theorem substitute_closedShift {k : Nat}
    (values : Fin k -> ValuationTerm) (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
    have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
      apply Rew.ext
      · intro coordinate
        exact Fin.elim0 coordinate
      · intro freeIndex
        rfl
    rw [hrew]
    exact Rew.id_app term
  | succ k ih =>
    have hrew : (Rew.subst values).comp Rew.bShift =
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
      _ = Rew.subst (fun index : Fin k => values index.succ) (closedShift k term) := by
        rw [hrew]
      _ = term := ih _

theorem compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary sourceLeft sourceRight
      targetLeft targetRight consumed : Nat) :
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary consumed) ⇜
        ![shortBinaryNumeralTerm targetRight, shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm sourceLeft] =
      (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘!!(fixedNumeralTerm consumed) + &0’ : ValuationTerm)
          (shortBinaryNumeralTerm sourceLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘(!!(fixedNumeralTerm consumed) + &0) + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm sourceRight) ⋏
          (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
              (shortBinaryNumeralTerm targetLeft) ⋏
            (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm targetBoundary)
                (shortBinaryNumeralTerm tokenCount) (‘&0 + 1’ : ValuationTerm)
                (shortBinaryNumeralTerm targetRight) ⋏
              ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
                ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
                  shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceLeft,
                  shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm targetLeft,
                  shortBinaryNumeralTerm targetRight]))))) := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 :=
  termValue_one valuation ![]

@[simp] private theorem termValue_fixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘ (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) =
        (![] : Fin 0 -> Nat) by
      funext index
      exact Fin.elim0 index]
  simp

noncomputable def closedFixedNumeralLeCertificate
    (consumed right : Nat) (hle : consumed ≤ right) :
    HybridCertificate zeroValuation
      “!!(fixedNumeralTerm consumed) ≤ !!(shortBinaryNumeralTerm right)” := by
  if heq : consumed = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![fixedNumeralTerm consumed, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (fixedNumeralTerm consumed) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_fixedNumeralTerm, termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionLeft equality)
  else
    have hlt : consumed < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![fixedNumeralTerm consumed, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (fixedNumeralTerm consumed) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_fixedNumeralTerm, termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm (.disjunctionRight strict)

noncomputable def closedFixedNumeralAddEqCertificate
    (total consumed right : Nat) (heq : total = consumed + right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm total) =
        !!(fixedNumeralTerm consumed) + !!(shortBinaryNumeralTerm right)” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm total,
      ‘!!(fixedNumeralTerm consumed) + !!(shortBinaryNumeralTerm right)’] (by
      change termValue zeroValuation (shortBinaryNumeralTerm total) =
        termValue zeroValuation
          ‘!!(fixedNumeralTerm consumed) + !!(shortBinaryNumeralTerm right)’
      simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
        termValue_fixedNumeralTerm] using heq)

noncomputable def compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed index : Nat)
    (data : CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary consumed)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalueTerms :
      (fun coordinate : Fin 4 => shortBinaryNumeralTerm (values coordinate)) =
        ![shortBinaryNumeralTerm data.targetRight, shortBinaryNumeralTerm data.targetLeft,
          shortBinaryNumeralTerm data.sourceRight, shortBinaryNumeralTerm data.sourceLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let sourceIndexTerm : ValuationTerm := ‘!!(fixedNumeralTerm consumed) + &0’
  let sourceNextTerm : ValuationTerm := ‘(!!(fixedNumeralTerm consumed) + &0) + 1’
  let targetIndexTerm : ValuationTerm := &0
  let targetNextTerm : ValuationTerm := ‘&0 + 1’
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) (shortBinaryNumeralTerm tokenCount)
      sourceIndexTerm (shortBinaryNumeralTerm data.sourceLeft) (by
        simpa [valuation, sourceIndexTerm, zeroValuation, termValue_arithmeticAdd,
          termValue_arithmeticOne, termValue_fixedNumeralTerm,
          termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
        (shortBinaryNumeralTerm sourceBoundary) (shortBinaryNumeralTerm tokenCount)
        sourceNextTerm (shortBinaryNumeralTerm data.sourceRight) (by
          simpa [valuation, sourceNextTerm, zeroValuation, termValue_arithmeticAdd,
            termValue_arithmeticOne, termValue_fixedNumeralTerm,
            termValue_shortBinaryNumeralTerm,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.sourceRight_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
          targetIndexTerm (shortBinaryNumeralTerm data.targetLeft) (by
            simpa [valuation, targetIndexTerm, zeroValuation,
              termValue_shortBinaryNumeralTerm,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using data.targetLeft_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
            (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
            targetNextTerm (shortBinaryNumeralTerm data.targetRight) (by
              simpa [valuation, targetNextTerm, zeroValuation, termValue_arithmeticAdd,
                termValue_arithmeticOne, termValue_shortBinaryNumeralTerm,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using data.targetRight_entry))
          (compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph valuation tokenTable
            width tokenCount data.sourceLeft data.sourceRight data.targetLeft data.targetRight
            data.row_eq))))
  let terminal : HybridCertificate valuation
      ((compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary consumed) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal_substitution_alignment
        tokenTable width tokenCount sourceBoundary targetBoundary data.sourceLeft
        data.sourceRight data.targetLeft data.targetRight consumed).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary consumed) values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le) terminal
  exact .cast (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody_free_alignment tokenTable width
    tokenCount sourceBoundary targetBoundary consumed).symm installed

noncomputable def
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsDirectHybridBranchesAtCount
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveSyntaxTaskListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary consumed) targetCount :=
  buildExplicitHybridUniversalBranches targetCount (fun index hindex =>
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchCertificate
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index
      (rows ⟨index, hindex⟩))

theorem
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsShortNumeralBound_eq_targetCount
    (targetCount : Nat) :
    termValue zeroValuation (shortBinaryNumeralTerm targetCount) =
      targetCount := by
  exact termValue_shortBinaryNumeralTerm zeroValuation targetCount

noncomputable def
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsDirectHybridBranches
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveSyntaxTaskListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary consumed)
      (termValue zeroValuation (shortBinaryNumeralTerm targetCount)) :=
  (compactAdditiveSyntaxTaskListDropFixedNumeralRowsShortNumeralBound_eq_targetCount
    targetCount).symm ▸
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsDirectHybridBranchesAtCount
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows

noncomputable def compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveSyntaxTaskListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    HybridCertificate zeroValuation
      ((compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary consumed).ballLT (shortBinaryNumeralTerm targetCount)) := by
  let body := compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width tokenCount
    sourceBoundary targetBoundary consumed
  let branches :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsDirectHybridBranches
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm targetCount) body branches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift (shortBinaryNumeralTerm targetCount))
      body) = body.ballLT (shortBinaryNumeralTerm targetCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def compactAdditiveSyntaxTaskListDropFixedNumeralRowDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed)
    (index : Fin targetCount) :
    CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
      sourceBoundary targetBoundary consumed index := by
  let sourceLeftExists := hgraph.2.2 index index.isLt
  let sourceLeft := Classical.choose sourceLeftExists
  have hsourceLeft := Classical.choose_spec sourceLeftExists
  let sourceRightExists := hsourceLeft.2
  let sourceRight := Classical.choose sourceRightExists
  have hsourceRight := Classical.choose_spec sourceRightExists
  let targetLeftExists := hsourceRight.2
  let targetLeft := Classical.choose targetLeftExists
  have htargetLeft := Classical.choose_spec targetLeftExists
  let targetRightExists := htargetLeft.2
  let targetRight := Classical.choose targetRightExists
  have htargetRight := Classical.choose_spec targetRightExists
  exact
    { sourceLeft := sourceLeft
      sourceRight := sourceRight
      targetLeft := targetLeft
      targetRight := targetRight
      sourceLeft_le := hsourceLeft.1
      sourceRight_le := hsourceRight.1
      targetLeft_le := htargetLeft.1
      targetRight_le := htargetRight.1
      sourceLeft_entry := htargetRight.2.1
      sourceRight_entry := htargetRight.2.2.1
      targetLeft_entry := htargetRight.2.2.2.1
      targetRight_entry := htargetRight.2.2.2.2.1
      row_eq := htargetRight.2.2.2.2.2 }

noncomputable def
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hbound : consumed ≤ sourceCount)
    (heq : sourceCount = consumed + targetCount)
    (rows : (index : Fin targetCount) -> CompactAdditiveSyntaxTaskListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount consumed) := by
  let countBound := closedFixedNumeralLeCertificate consumed sourceCount hbound
  let countEq := closedFixedNumeralAddEqCertificate sourceCount consumed targetCount heq
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction countBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction countEq
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalCertificate tokenTable width tokenCount
        sourceBoundary targetBoundary targetCount consumed rows))
  exact .cast
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula_alignment
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed).symm parts

noncomputable def compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount sourceBoundary
      sourceCount targetBoundary targetCount consumed) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount consumed) := by
  let rows : (index : Fin targetCount) -> CompactAdditiveSyntaxTaskListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowDataOfGraph tokenTable width
      tokenCount sourceBoundary sourceCount targetBoundary targetCount consumed
      hgraph
  exact
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataExplicitHybridCertificate
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed hgraph.1 hgraph.2.1 rows

#print axioms compactAdditiveSyntaxTaskListDropFixedNumeralRowsClosedFormula_alignment
#print axioms compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
