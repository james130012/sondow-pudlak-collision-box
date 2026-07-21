import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for syntax-task-list prefix dropping

Each target row installs the four bounded boundary entries used by the
original formula and proves the three atomic equalities of the syntax-task
row.  The universal index remains the actual valuation variable `&0`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

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
      Rewriting.app right := by
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

def compactAdditiveSyntaxTaskListDropRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactAdditiveSyntaxTaskListDropRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm consumed]

def compactAdditiveSyntaxTaskListDropRowsTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount),
        ‘!!(closedShift 5 (shortBinaryNumeralTerm consumed)) + #4’,
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 5 (shortBinaryNumeralTerm tokenCount),
          ‘(!!(closedShift 5 (shortBinaryNumeralTerm consumed)) + #4) + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
            closedShift 5 (shortBinaryNumeralTerm tokenCount),
            (#4 : ArithmeticSemiterm Nat 5),
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
              closedShift 5 (shortBinaryNumeralTerm tokenCount),
              ‘#4 + 1’, (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat)
              compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
              closedShift 5 (shortBinaryNumeralTerm width),
              closedShift 5 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 5),
              (#2 : ArithmeticSemiterm Nat 5),
              (#1 : ArithmeticSemiterm Nat 5),
              (#0 : ArithmeticSemiterm Nat 5)]))))

def compactAdditiveSyntaxTaskListDropRowsBody
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (((((compactAdditiveSyntaxTaskListDropRowsTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary consumed).bexsLTSucc
        (closedShift 4 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount)))

def compactAdditiveSyntaxTaskListDropRowsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm consumed) ≤
      !!(shortBinaryNumeralTerm sourceCount)” ⋏
    (“!!(shortBinaryNumeralTerm sourceCount) =
        !!(shortBinaryNumeralTerm consumed) +
          !!(shortBinaryNumeralTerm targetCount)” ⋏
      (compactAdditiveSyntaxTaskListDropRowsBody
        tokenTable width tokenCount sourceBoundary targetBoundary consumed).ballLT
          (shortBinaryNumeralTerm targetCount))

theorem compactAdditiveSyntaxTaskListDropRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat) :
    compactAdditiveSyntaxTaskListDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount consumed =
      compactAdditiveSyntaxTaskListDropRowsExplicitFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount consumed := by
  unfold compactAdditiveSyntaxTaskListDropRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListDropRowsExplicitFormula
  unfold compactAdditiveSyntaxTaskListDropRowsBody
  unfold compactAdditiveSyntaxTaskListDropRowsTerminal
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

structure CompactAdditiveSyntaxTaskListDropRowData
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed
      index : Nat) where
  sourceLeft : Nat
  sourceRight : Nat
  targetLeft : Nat
  targetRight : Nat
  sourceLeft_le : sourceLeft ≤ tokenCount
  sourceRight_le : sourceRight ≤ tokenCount
  targetLeft_le : targetLeft ≤ tokenCount
  targetRight_le : targetRight ≤ tokenCount
  sourceLeft_entry : CompactFixedWidthEntry sourceBoundary tokenCount
    (consumed + index) sourceLeft
  sourceRight_entry : CompactFixedWidthEntry sourceBoundary tokenCount
    (consumed + index + 1) sourceRight
  targetLeft_entry : CompactFixedWidthEntry targetBoundary tokenCount
    index targetLeft
  targetRight_entry : CompactFixedWidthEntry targetBoundary tokenCount
    (index + 1) targetRight
  row_eq : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
    sourceLeft sourceRight targetLeft targetRight

def compactAdditiveSyntaxTaskListDropRowsBranchTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        ‘!!(closedShift 4 (shortBinaryNumeralTerm consumed)) + &0’,
        (#3 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          ‘(!!(closedShift 4 (shortBinaryNumeralTerm consumed)) + &0) + 1’,
          (#2 : ArithmeticSemiterm Nat 4)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
            closedShift 4 (shortBinaryNumeralTerm tokenCount),
            (&0 : ArithmeticSemiterm Nat 4),
            (#1 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]) ⋏
          ((Rewriting.emb (ξ := Nat)
              compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 4),
              (#2 : ArithmeticSemiterm Nat 4),
              (#1 : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]))))

private theorem substitute_closedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew :
          (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
        apply Rew.ext
        · intro coordinate
          exact Fin.elim0 coordinate
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

@[simp] private theorem free_bvar_four_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#4 : ArithmeticSemiterm Nat 5) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 4)) (#(Fin.last 4)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_three_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#3 : ArithmeticSemiterm Nat 5) = #3 := by
  exact Rew.free_bvar_castSucc (3 : Fin 4)

@[simp] private theorem free_bvar_two_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#2 : ArithmeticSemiterm Nat 5) = #2 := by
  exact Rew.free_bvar_castSucc (2 : Fin 4)

@[simp] private theorem free_bvar_one_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#1 : ArithmeticSemiterm Nat 5) = #1 := by
  exact Rew.free_bvar_castSucc (1 : Fin 4)

@[simp] private theorem free_bvar_zero_fin5 :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (#0 : ArithmeticSemiterm Nat 5) = #0 := by
  exact Rew.free_bvar_castSucc (0 : Fin 4)

private theorem compactAdditiveSyntaxTaskListDropRowsTerminal_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    Rewriting.free
        (compactAdditiveSyntaxTaskListDropRowsTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary consumed) =
      compactAdditiveSyntaxTaskListDropRowsBranchTerminal
        tokenTable width tokenCount sourceBoundary targetBoundary consumed := by
  unfold compactAdditiveSyntaxTaskListDropRowsTerminal
  unfold compactAdditiveSyntaxTaskListDropRowsBranchTerminal
  simp [closedShift, ← TransitiveRewriting.comp_app]
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

private def localExplicitBoundedWitnessFormulaFour
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 4) :
    ValuationFormula :=
  ((((body.bexsLTSucc (closedShift 3 bound)).bexsLTSucc
      (closedShift 2 bound)).bexsLTSucc
    (closedShift 1 bound)).bexsLTSucc bound)

private theorem localExplicitBoundedWitnessFormulaFour_eq_explicit
    (bound : ValuationTerm) (body : ArithmeticSemiformula Nat 4) :
    localExplicitBoundedWitnessFormulaFour bound body =
      explicitBoundedWitnessFormula bound 4 body := by
  rfl

theorem compactAdditiveSyntaxTaskListDropRowsBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed : Nat) :
    Rewriting.free
        (compactAdditiveSyntaxTaskListDropRowsBody
          tokenTable width tokenCount sourceBoundary targetBoundary consumed) =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListDropRowsBranchTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            consumed) := by
  calc
    Rewriting.free
        (compactAdditiveSyntaxTaskListDropRowsBody
          tokenTable width tokenCount sourceBoundary targetBoundary consumed) =
      localExplicitBoundedWitnessFormulaFour
        (shortBinaryNumeralTerm tokenCount)
        (compactAdditiveSyntaxTaskListDropRowsBranchTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            consumed) := by
      unfold compactAdditiveSyntaxTaskListDropRowsBody
      unfold localExplicitBoundedWitnessFormulaFour
      simp [Rew.q_free, closedShift,
        compactAdditiveSyntaxTaskListDropRowsTerminal_free_alignment]
    _ = explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListDropRowsBranchTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            consumed) :=
      localExplicitBoundedWitnessFormulaFour_eq_explicit _ _

theorem compactAdditiveSyntaxTaskListDropRowsBranchTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed
      sourceLeft sourceRight targetLeft targetRight : Nat) :
    (compactAdditiveSyntaxTaskListDropRowsBranchTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary consumed) ⇜
        ![shortBinaryNumeralTerm targetRight,
          shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm sourceRight,
          shortBinaryNumeralTerm sourceLeft] =
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
          (shortBinaryNumeralTerm sourceLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘(!!(shortBinaryNumeralTerm consumed) + &0) + 1’ :
              ValuationTerm)
            (shortBinaryNumeralTerm sourceRight) ⋏
          (compactFixedWidthEntryAtValuationFormula
              (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
              (shortBinaryNumeralTerm targetLeft) ⋏
            (compactFixedWidthEntryAtValuationFormula
                (shortBinaryNumeralTerm targetBoundary)
                (shortBinaryNumeralTerm tokenCount)
                (‘&0 + 1’ : ValuationTerm)
                (shortBinaryNumeralTerm targetRight) ⋏
              ((Rewriting.emb (ξ := Nat)
                  compactAdditiveSyntaxTaskRowEqDef.val) ⇜
                ![shortBinaryNumeralTerm tokenTable,
                  shortBinaryNumeralTerm width,
                  shortBinaryNumeralTerm tokenCount,
                  shortBinaryNumeralTerm sourceLeft,
                  shortBinaryNumeralTerm sourceRight,
                  shortBinaryNumeralTerm targetLeft,
                  shortBinaryNumeralTerm targetRight]))))) := by
  unfold compactAdditiveSyntaxTaskListDropRowsBranchTerminal
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
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 :=
  termValue_one valuation ![]

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right] (by
            change termValue zeroValuation
                (shortBinaryNumeralTerm left) =
              termValue zeroValuation (shortBinaryNumeralTerm right)
            simpa [termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt
        ![shortBinaryNumeralTerm left,
          shortBinaryNumeralTerm right] (by
            change termValue zeroValuation
                (shortBinaryNumeralTerm left) <
              termValue zeroValuation (shortBinaryNumeralTerm right)
            simpa [termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def closedAddEqCertificate
    (total left right : Nat) (heq : total = left + right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm total) =
        !!(shortBinaryNumeralTerm left) +
          !!(shortBinaryNumeralTerm right)” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm total,
      ‘!!(shortBinaryNumeralTerm left) +
        !!(shortBinaryNumeralTerm right)’] (by
      change termValue zeroValuation (shortBinaryNumeralTerm total) =
        termValue zeroValuation
          ‘!!(shortBinaryNumeralTerm left) +
            !!(shortBinaryNumeralTerm right)’
      simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd]
        using heq)

private noncomputable def
    compactAdditiveSyntaxTaskListDropRowsBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed
      index : Nat)
    (data : CompactAdditiveSyntaxTaskListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed
        index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free
        (compactAdditiveSyntaxTaskListDropRowsBody
          tokenTable width tokenCount sourceBoundary targetBoundary
            consumed)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft,
      data.sourceRight, data.sourceLeft]
  have hvalueTerms :
      (fun coordinate : Fin 4 =>
        shortBinaryNumeralTerm (values coordinate)) =
      ![shortBinaryNumeralTerm data.targetRight,
        shortBinaryNumeralTerm data.targetLeft,
        shortBinaryNumeralTerm data.sourceRight,
        shortBinaryNumeralTerm data.sourceLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let sourceIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm consumed) + &0’
  let sourceNextTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm consumed) + &0) + 1’
  let targetIndexTerm : ValuationTerm := &0
  let targetNextTerm : ValuationTerm := ‘&0 + 1’
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount) sourceIndexTerm
        (shortBinaryNumeralTerm data.sourceLeft) (by
          simpa [valuation, sourceIndexTerm, zeroValuation,
            termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.sourceLeft_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) sourceNextTerm
          (shortBinaryNumeralTerm data.sourceRight) (by
            simpa [valuation, sourceNextTerm, zeroValuation,
              termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
              termValue_arithmeticOne,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using data.sourceRight_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            valuation (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount) targetIndexTerm
            (shortBinaryNumeralTerm data.targetLeft) (by
              simpa [valuation, targetIndexTerm, zeroValuation,
                termValue_shortBinaryNumeralTerm,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using data.targetLeft_entry))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactFixedWidthEntryAtValuationExplicitHybridCertificate
              valuation (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount) targetNextTerm
              (shortBinaryNumeralTerm data.targetRight) (by
                simpa [valuation, targetNextTerm, zeroValuation,
                  termValue_shortBinaryNumeralTerm,
                  termValue_arithmeticAdd, termValue_arithmeticOne,
                  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                  using data.targetRight_entry))
            (compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph
              valuation tokenTable width tokenCount data.sourceLeft
              data.sourceRight data.targetLeft data.targetRight
                data.row_eq))))
  let terminal : HybridCertificate valuation
      ((compactAdditiveSyntaxTaskListDropRowsBranchTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            consumed) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact
        (compactAdditiveSyntaxTaskListDropRowsBranchTerminal_substitution_alignment
          tokenTable width tokenCount sourceBoundary targetBoundary consumed
          data.sourceLeft data.sourceRight data.targetLeft data.targetRight).symm)
      terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveSyntaxTaskListDropRowsBranchTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary consumed)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact data.targetRight_le
      · exact data.targetLeft_le
      · exact data.sourceRight_le
      · exact data.sourceLeft_le)
    terminal
  exact .cast
    (compactAdditiveSyntaxTaskListDropRowsBody_free_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary consumed).symm
    installed

private noncomputable def
    compactAdditiveSyntaxTaskListDropRowsUniversalCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary consumed
      targetCount : Nat)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData
        tokenTable width tokenCount sourceBoundary targetBoundary consumed
          index) :
    HybridCertificate zeroValuation
      ((compactAdditiveSyntaxTaskListDropRowsBody
        tokenTable width tokenCount sourceBoundary targetBoundary consumed).ballLT
          (shortBinaryNumeralTerm targetCount)) := by
  let body := compactAdditiveSyntaxTaskListDropRowsBody
    tokenTable width tokenCount sourceBoundary targetBoundary consumed
  let branches := buildExplicitHybridUniversalBranches targetCount
    (fun index hindex =>
      compactAdditiveSyntaxTaskListDropRowsBranchCertificate
        tokenTable width tokenCount sourceBoundary targetBoundary consumed
          index (rows ⟨index, hindex⟩))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm targetCount) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount)) body) =
        body.ballLT (shortBinaryNumeralTerm targetCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def
    compactAdditiveSyntaxTaskListDropRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount consumed) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount consumed) := by
  rw [compactAdditiveSyntaxTaskListDropRowsClosedFormula_alignment]
  let countBound := closedLeCertificate consumed sourceCount hgraph.1
  let countEq := closedAddEqCertificate sourceCount consumed targetCount
    hgraph.2.1
  let rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData
        tokenTable width tokenCount sourceBoundary targetBoundary consumed
          index := fun index => by
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
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction countEq
      (compactAdditiveSyntaxTaskListDropRowsUniversalCertificate
        tokenTable width tokenCount sourceBoundary targetBoundary consumed
          targetCount rows))

noncomputable def
    compileCompactAdditiveSyntaxTaskListDropRowsExplicitHybridContext
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount consumed) :
    CertifiedPAContextProof
      (valuationContext
        (compactAdditiveSyntaxTaskListDropRowsClosedFormula
          tokenTable width tokenCount sourceBoundary sourceCount
            targetBoundary targetCount consumed).freeVariables
        zeroValuation)
      (compactAdditiveSyntaxTaskListDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount consumed) :=
  (compactAdditiveSyntaxTaskListDropRowsExplicitHybridCertificateOfGraph
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed hgraph).compile

noncomputable def
    compactAdditiveSyntaxTaskListDropRowsExplicitStructuralResource
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount consumed) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListDropRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed hgraph)

theorem
    compileCompactAdditiveSyntaxTaskListDropRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount consumed) :
    (compileCompactAdditiveSyntaxTaskListDropRowsExplicitHybridContext
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed hgraph).payloadLength ≤
      compactAdditiveSyntaxTaskListDropRowsExplicitStructuralResource
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount consumed hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListDropRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed hgraph)

#print axioms compactAdditiveSyntaxTaskListDropRowsClosedFormula_alignment
#print axioms
  compactAdditiveSyntaxTaskListDropRowsExplicitHybridCertificateOfGraph
#print axioms
  compileCompactAdditiveSyntaxTaskListDropRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
