import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRows
import integration.FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for equal syntax-task list row tables

Each public task row installs four fixed-width entries and proves the three
consecutive atomic row equalities that make up a syntax task.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
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
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

private abbrev HybridCertificate := CheckedHybridValuationBoundedFormulaCertificate

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
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
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

def compactAdditiveSyntaxTaskListSameRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskListSameRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount, shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount]

def compactAdditiveSyntaxTaskListSameRowsTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 5 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 5 (shortBinaryNumeralTerm tokenCount), (#4 : ArithmeticSemiterm Nat 5),
        (#3 : ArithmeticSemiterm Nat 5)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 5 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’,
          (#2 : ArithmeticSemiterm Nat 5)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
            closedShift 5 (shortBinaryNumeralTerm tokenCount), (#4 : ArithmeticSemiterm Nat 5),
            (#1 : ArithmeticSemiterm Nat 5)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm targetBoundary),
              closedShift 5 (shortBinaryNumeralTerm tokenCount), ‘#4 + 1’,
              (#0 : ArithmeticSemiterm Nat 5)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 5 (shortBinaryNumeralTerm tokenTable),
              closedShift 5 (shortBinaryNumeralTerm width),
              closedShift 5 (shortBinaryNumeralTerm tokenCount), (#3 : ArithmeticSemiterm Nat 5),
              (#2 : ArithmeticSemiterm Nat 5), (#1 : ArithmeticSemiterm Nat 5),
              (#0 : ArithmeticSemiterm Nat 5)]))))

def compactAdditiveSyntaxTaskListSameRowsBody
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (((((compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary).bexsLTSucc
        (closedShift 4 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount)))

def compactAdditiveSyntaxTaskListSameRowsExplicitFormula
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm targetCount) = !!(shortBinaryNumeralTerm sourceCount)” ⋏
    (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT (shortBinaryNumeralTerm sourceCount)

theorem compactAdditiveSyntaxTaskListSameRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat) :
    compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount =
      compactAdditiveSyntaxTaskListSameRowsExplicitFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount := by
  unfold compactAdditiveSyntaxTaskListSameRowsClosedFormula
  unfold compactAdditiveSyntaxTaskListSameRowsExplicitFormula
  unfold compactAdditiveSyntaxTaskListSameRowsBody
  unfold compactAdditiveSyntaxTaskListSameRowsTerminal
  unfold compactAdditiveSyntaxTaskListSameRowsDef
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

structure CompactAdditiveSyntaxTaskListSameRowData
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat) where
  sourceLeft : Nat
  sourceRight : Nat
  targetLeft : Nat
  targetRight : Nat
  sourceLeft_le : sourceLeft ≤ tokenCount
  sourceRight_le : sourceRight ≤ tokenCount
  targetLeft_le : targetLeft ≤ tokenCount
  targetRight_le : targetRight ≤ tokenCount
  sourceLeft_entry : CompactFixedWidthEntry sourceBoundary tokenCount index sourceLeft
  sourceRight_entry : CompactFixedWidthEntry sourceBoundary tokenCount (index + 1) sourceRight
  targetLeft_entry : CompactFixedWidthEntry targetBoundary tokenCount index targetLeft
  targetRight_entry : CompactFixedWidthEntry targetBoundary tokenCount (index + 1) targetRight
  row_eq : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount
    sourceLeft sourceRight targetLeft targetRight

def compactAdditiveSyntaxTaskListSameRowsBranchTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount), (&0 : ArithmeticSemiterm Nat 4),
        (#3 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount), (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
          (#2 : ArithmeticSemiterm Nat 4)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
            closedShift 4 (shortBinaryNumeralTerm tokenCount), (&0 : ArithmeticSemiterm Nat 4),
            (#1 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
              closedShift 4 (shortBinaryNumeralTerm tokenCount), (‘&0 + 1’ : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount), (#3 : ArithmeticSemiterm Nat 4),
              (#2 : ArithmeticSemiterm Nat 4), (#1 : ArithmeticSemiterm Nat 4),
              (#0 : ArithmeticSemiterm Nat 4)]))))

private theorem substitute_closedShift {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) : Rew.subst values (closedShift k term) = term := by
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
      _ = Rew.subst (fun index : Fin k => values index.succ) (closedShift k term) := by rw [hrew]
      _ = term := ih _

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
  simp

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  simp

@[simp] private theorem free_bShift3_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))) =
      Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value)) := by
  simp

@[simp] private theorem free_bShift4_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value))))) =
      Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value))) := by
  simp

@[simp] private theorem free_bShift5_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift
          (Rew.bShift (shortBinaryNumeralTerm value)))))) =
      Rew.bShift (Rew.bShift (Rew.bShift
        (Rew.bShift (shortBinaryNumeralTerm value)))) := by
  simpa [closedShift] using
    (free_closedShift_shortBinaryNumeralTerm 4 value)

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

private theorem compactAdditiveSyntaxTaskListSameRowsTerminal_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free (compactAdditiveSyntaxTaskListSameRowsTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) =
      compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary := by
  unfold compactAdditiveSyntaxTaskListSameRowsTerminal
  unfold compactAdditiveSyntaxTaskListSameRowsBranchTerminal
  simp [closedShift, ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
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

theorem compactAdditiveSyntaxTaskListSameRowsBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary) =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width tokenCount
          sourceBoundary targetBoundary) := by
  calc
    Rewriting.free (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary) =
      localExplicitBoundedWitnessFormulaFour
        (shortBinaryNumeralTerm tokenCount)
        (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary) := by
      unfold compactAdditiveSyntaxTaskListSameRowsBody
      unfold localExplicitBoundedWitnessFormulaFour
      simp [Rew.q_free, closedShift,
        compactAdditiveSyntaxTaskListSameRowsTerminal_free_alignment]
    _ = explicitBoundedWitnessFormula (shortBinaryNumeralTerm tokenCount) 4
        (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width
          tokenCount sourceBoundary targetBoundary) :=
      localExplicitBoundedWitnessFormulaFour_eq_explicit _ _

theorem compactAdditiveSyntaxTaskListSameRowsBranchTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary sourceLeft sourceRight
      targetLeft targetRight : Nat) :
    (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) ⇜
        ![shortBinaryNumeralTerm targetRight, shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm sourceLeft] =
      (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount) (&0 : ValuationTerm)
          (shortBinaryNumeralTerm sourceLeft) ⋏
        (compactFixedWidthEntryAtValuationFormula (shortBinaryNumeralTerm sourceBoundary)
            (shortBinaryNumeralTerm tokenCount) (‘&0 + 1’ : ValuationTerm)
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
  unfold compactAdditiveSyntaxTaskListSameRowsBranchTerminal
  unfold compactFixedWidthEntryAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar, substitute_closedShift]
    · intro coordinate
      exact Empty.elim coordinate

private theorem arithmeticAddTerm_eq_func {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq, Rew.func,
    Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd (valuation : Nat -> Nat)
    (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := termValue_one valuation ![]

private theorem termValue_arithmeticTwo (valuation : Nat -> Nat) :
    termValue valuation (‘2’ : ValuationTerm) = 2 := by
  simp [termValue, LO.FirstOrder.Semiterm.val_operator]

noncomputable def countEqualityCertificate (sourceCount targetCount : Nat)
    (hcount : targetCount = sourceCount) : HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm targetCount) = !!(shortBinaryNumeralTerm sourceCount)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic zeroValuation
    Language.Eq.eq ![shortBinaryNumeralTerm targetCount, shortBinaryNumeralTerm sourceCount] (by
      change termValue zeroValuation (shortBinaryNumeralTerm targetCount) =
        termValue zeroValuation (shortBinaryNumeralTerm sourceCount)
      simpa [termValue_shortBinaryNumeralTerm] using hcount)
  exact .cast (Semiformula.Operator.eq_def _ _).symm direct

theorem compactAdditiveSyntaxTaskRowEqClosedFormula_alignment
    (tokenTable width tokenCount sourceLeft sourceRight targetLeft
      targetRight : Nat) :
    ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceLeft,
          shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm targetRight]) =
      (compactAdditiveAtomicRowEqAtValuationFormula
          (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
          (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm sourceLeft)
          (‘!!(shortBinaryNumeralTerm sourceLeft) + 1’)
          (shortBinaryNumeralTerm targetLeft)
          (‘!!(shortBinaryNumeralTerm targetLeft) + 1’) ⋏
        (compactAdditiveAtomicRowEqAtValuationFormula
            (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (‘!!(shortBinaryNumeralTerm sourceLeft) + 1’)
            (‘!!(shortBinaryNumeralTerm sourceLeft) + 2’)
            (‘!!(shortBinaryNumeralTerm targetLeft) + 1’)
            (‘!!(shortBinaryNumeralTerm targetLeft) + 2’) ⋏
          compactAdditiveAtomicRowEqAtValuationFormula
            (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
            (shortBinaryNumeralTerm tokenCount)
            (‘!!(shortBinaryNumeralTerm sourceLeft) + 2’)
            (shortBinaryNumeralTerm sourceRight)
            (‘!!(shortBinaryNumeralTerm targetLeft) + 2’)
            (shortBinaryNumeralTerm targetRight))) := by
  unfold compactAdditiveSyntaxTaskRowEqDef
  unfold compactAdditiveAtomicRowEqAtValuationFormula
  simp [← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      apply arithmeticRewritingApp_congr
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate

noncomputable def compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph
    (valuation : Nat -> Nat) (tokenTable width tokenCount sourceLeft sourceRight
      targetLeft targetRight : Nat)
    (hrow : CompactAdditiveSyntaxTaskRowEq tokenTable width tokenCount sourceLeft sourceRight
      targetLeft targetRight) :
    HybridCertificate valuation
      ((Rewriting.emb (ξ := Nat) compactAdditiveSyntaxTaskRowEqDef.val) ⇜
        ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceLeft,
          shortBinaryNumeralTerm sourceRight, shortBinaryNumeralTerm targetLeft,
          shortBinaryNumeralTerm targetRight]) := by
  let tokenTableTerm := shortBinaryNumeralTerm tokenTable
  let widthTerm := shortBinaryNumeralTerm width
  let tokenCountTerm := shortBinaryNumeralTerm tokenCount
  let sourceLeftTerm := shortBinaryNumeralTerm sourceLeft
  let sourceRightTerm := shortBinaryNumeralTerm sourceRight
  let targetLeftTerm := shortBinaryNumeralTerm targetLeft
  let targetRightTerm := shortBinaryNumeralTerm targetRight
  let sourceSuccTerm : ValuationTerm := ‘!!sourceLeftTerm + 1’
  let sourceSuccSuccTerm : ValuationTerm := ‘!!sourceLeftTerm + 2’
  let targetSuccTerm : ValuationTerm := ‘!!targetLeftTerm + 1’
  let targetSuccSuccTerm : ValuationTerm := ‘!!targetLeftTerm + 2’
  have hfirst : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm) (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm) (termValue valuation sourceLeftTerm)
      (termValue valuation sourceSuccTerm) (termValue valuation targetLeftTerm)
      (termValue valuation targetSuccTerm) := by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      targetLeftTerm, sourceSuccTerm, targetSuccTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hrow.1
  have hsecond : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm) (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm) (termValue valuation sourceSuccTerm)
      (termValue valuation sourceSuccSuccTerm) (termValue valuation targetSuccTerm)
      (termValue valuation targetSuccSuccTerm) := by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      targetLeftTerm, sourceSuccTerm, sourceSuccSuccTerm, targetSuccTerm,
      targetSuccSuccTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne,
      termValue_arithmeticTwo] using hrow.2.1
  have hthird : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm) (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm) (termValue valuation sourceSuccSuccTerm)
      (termValue valuation sourceRightTerm) (termValue valuation targetSuccSuccTerm)
      (termValue valuation targetRightTerm) := by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      sourceRightTerm, targetLeftTerm, targetRightTerm, sourceSuccSuccTerm,
      targetSuccSuccTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne,
      termValue_arithmeticTwo] using hrow.2.2
  let first : HybridCertificate valuation
      (compactAdditiveAtomicRowEqAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm sourceLeftTerm sourceSuccTerm targetLeftTerm targetSuccTerm) :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      tokenTableTerm widthTerm tokenCountTerm sourceLeftTerm sourceSuccTerm
        targetLeftTerm targetSuccTerm hfirst
  let second : HybridCertificate valuation
      (compactAdditiveAtomicRowEqAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm sourceSuccTerm sourceSuccSuccTerm targetSuccTerm
          targetSuccSuccTerm) :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      tokenTableTerm widthTerm tokenCountTerm sourceSuccTerm sourceSuccSuccTerm
        targetSuccTerm targetSuccSuccTerm hsecond
  let third : HybridCertificate valuation
      (compactAdditiveAtomicRowEqAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm sourceSuccSuccTerm sourceRightTerm targetSuccSuccTerm
          targetRightTerm) :=
    compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate valuation
      tokenTableTerm widthTerm tokenCountTerm sourceSuccSuccTerm sourceRightTerm
        targetSuccSuccTerm targetRightTerm hthird
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    first (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      second third)
  exact .cast (by
    simpa [tokenTableTerm, widthTerm, tokenCountTerm, sourceLeftTerm,
      sourceRightTerm, targetLeftTerm, targetRightTerm, sourceSuccTerm,
      sourceSuccSuccTerm, targetSuccTerm, targetSuccSuccTerm] using
        (compactAdditiveSyntaxTaskRowEqClosedFormula_alignment tokenTable width tokenCount sourceLeft
          sourceRight targetLeft targetRight).symm) parts

noncomputable def compactAdditiveSyntaxTaskListSameRowsBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (data : CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index) :
    HybridCertificate (extendValuation index zeroValuation)
      (Rewriting.free (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)) := by
  let valuation := extendValuation index zeroValuation
  let values : Fin 4 -> Nat :=
    ![data.targetRight, data.targetLeft, data.sourceRight, data.sourceLeft]
  have hvalueTerms : (fun coordinate : Fin 4 => shortBinaryNumeralTerm (values coordinate)) =
      ![shortBinaryNumeralTerm data.targetRight, shortBinaryNumeralTerm data.targetLeft,
        shortBinaryNumeralTerm data.sourceRight, shortBinaryNumeralTerm data.sourceLeft] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  let sourceIndexTerm : ValuationTerm := &0
  let nextIndexTerm : ValuationTerm := ‘&0 + 1’
  let terminalParts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      (shortBinaryNumeralTerm sourceBoundary) (shortBinaryNumeralTerm tokenCount)
      sourceIndexTerm (shortBinaryNumeralTerm data.sourceLeft) (by
        simpa [valuation, sourceIndexTerm, zeroValuation, termValue_shortBinaryNumeralTerm,
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
          using data.sourceLeft_entry))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
        (shortBinaryNumeralTerm sourceBoundary) (shortBinaryNumeralTerm tokenCount)
        nextIndexTerm (shortBinaryNumeralTerm data.sourceRight) (by
          simpa [valuation, nextIndexTerm, zeroValuation, termValue_shortBinaryNumeralTerm,
            termValue_arithmeticAdd, termValue_arithmeticOne,
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
            using data.sourceRight_entry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
          (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
          sourceIndexTerm (shortBinaryNumeralTerm data.targetLeft) (by
            simpa [valuation, sourceIndexTerm, zeroValuation, termValue_shortBinaryNumeralTerm,
              FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
              using data.targetLeft_entry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
            (shortBinaryNumeralTerm targetBoundary) (shortBinaryNumeralTerm tokenCount)
            nextIndexTerm (shortBinaryNumeralTerm data.targetRight) (by
              simpa [valuation, nextIndexTerm, zeroValuation, termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticOne,
                FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation]
                using data.targetRight_entry))
          (compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph
            valuation tokenTable width tokenCount data.sourceLeft
            data.sourceRight data.targetLeft data.targetRight data.row_eq))))
  let terminal : HybridCertificate valuation
      ((compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width tokenCount
        sourceBoundary targetBoundary) ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate)) :=
    .cast (by
      rw [hvalueTerms]
      exact (compactAdditiveSyntaxTaskListSameRowsBranchTerminal_substitution_alignment
        tokenTable width tokenCount sourceBoundary targetBoundary data.sourceLeft data.sourceRight
        data.targetLeft data.targetRight).symm) terminalParts
  let installed := buildExplicitBoundedWitnessHybridCertificate tokenCount
    (compactAdditiveSyntaxTaskListSameRowsBranchTerminal tokenTable width tokenCount
      sourceBoundary targetBoundary) values (by
        intro coordinate
        fin_cases coordinate
        · exact data.targetRight_le
        · exact data.targetLeft_le
        · exact data.sourceRight_le
        · exact data.sourceLeft_le) terminal
  exact .cast (compactAdditiveSyntaxTaskListSameRowsBody_free_alignment tokenTable width tokenCount
    sourceBoundary targetBoundary).symm installed

noncomputable def compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary) sourceCount :=
  buildExplicitHybridUniversalBranches sourceCount (fun index hindex =>
    compactAdditiveSyntaxTaskListSameRowsBranchCertificate tokenTable width
      tokenCount sourceBoundary targetBoundary index (rows ⟨index, hindex⟩))

theorem compactAdditiveSyntaxTaskListSameRowsShortNumeralBound_eq_sourceCount
    (sourceCount : Nat) :
    termValue zeroValuation (shortBinaryNumeralTerm sourceCount) =
      sourceCount := by
  exact termValue_shortBinaryNumeralTerm zeroValuation sourceCount

noncomputable def compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    CheckedHybridValuationUniversalBranches zeroValuation
      (compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary)
      (termValue zeroValuation (shortBinaryNumeralTerm sourceCount)) :=
  (compactAdditiveSyntaxTaskListSameRowsShortNumeralBound_eq_sourceCount
    sourceCount).symm ▸
      compactAdditiveSyntaxTaskListSameRowsDirectHybridBranchesAtCount
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows

noncomputable def compactAdditiveSyntaxTaskListSameRowsUniversalCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary : Nat)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      ((compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount
        sourceBoundary targetBoundary).ballLT (shortBinaryNumeralTerm sourceCount)) := by
  let body := compactAdditiveSyntaxTaskListSameRowsBody tokenTable width tokenCount sourceBoundary targetBoundary
  let branches := compactAdditiveSyntaxTaskListSameRowsDirectHybridBranches
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm sourceCount) body branches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body) =
      body.ballLT (shortBinaryNumeralTerm sourceCount)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def compactAdditiveSyntaxTaskListSameRowsFromRowDataExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (hcount : targetCount = sourceCount)
    (rows : (index : Fin sourceCount) -> CompactAdditiveSyntaxTaskListSameRowData
      tokenTable width tokenCount sourceBoundary targetBoundary index) :
    HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (countEqualityCertificate sourceCount targetCount hcount)
    (compactAdditiveSyntaxTaskListSameRowsUniversalCertificate tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary rows)
  exact .cast (compactAdditiveSyntaxTaskListSameRowsClosedFormula_alignment tokenTable width tokenCount
    sourceBoundary sourceCount targetBoundary targetCount).symm parts

noncomputable def compactAdditiveSyntaxTaskListSameRowDataOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount)
    (index : Fin sourceCount) :
    CompactAdditiveSyntaxTaskListSameRowData tokenTable width tokenCount
      sourceBoundary targetBoundary index := by
  let sourceLeftExists := hgraph.2 index index.isLt
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

noncomputable def compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount) : HybridCertificate zeroValuation
      (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount) :=
  compactAdditiveSyntaxTaskListSameRowsFromRowDataExplicitHybridCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    targetCount hgraph.1
    (compactAdditiveSyntaxTaskListSameRowDataOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount hgraph)

noncomputable def compileCompactAdditiveSyntaxTaskListSameRowsExplicitHybridContext
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount) : CertifiedPAContextProof
      (valuationContext (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount).freeVariables zeroValuation)
      (compactAdditiveSyntaxTaskListSameRowsClosedFormula tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount) :=
  (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph tokenTable width tokenCount
    sourceBoundary sourceCount targetBoundary targetCount hgraph).compile

noncomputable def compactAdditiveSyntaxTaskListSameRowsExplicitStructuralResource
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount) : Nat :=
  hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount hgraph)

theorem compileCompactAdditiveSyntaxTaskListSameRowsExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary targetCount : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListSameRows tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount) :
    (compileCompactAdditiveSyntaxTaskListSameRowsExplicitHybridContext tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount hgraph).payloadLength ≤
      compactAdditiveSyntaxTaskListSameRowsExplicitStructuralResource tokenTable width tokenCount
        sourceBoundary sourceCount targetBoundary targetCount hgraph := by
  exact compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    (compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount hgraph)

#print axioms compactAdditiveSyntaxTaskListSameRowsClosedFormula_alignment
#print axioms compactAdditiveSyntaxTaskRowEqExplicitHybridCertificateOfGraph
#print axioms compactAdditiveSyntaxTaskListSameRowsExplicitHybridCertificateOfGraph
#print axioms compileCompactAdditiveSyntaxTaskListSameRowsExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectSyntaxTaskListSameRowsExplicitHybridCertificate
