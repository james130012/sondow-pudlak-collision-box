import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for verifier task-list rows

The source graph is retained verbatim as the public closed formula.  Its
bounded universal is enumerated explicitly, and every live row installs the
fourteen witnesses exposed by the semantic graph before closing the two
public boundary entries and the verifier-task core.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAEmbeddedPredicateFreeVariables

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

def taskListRowsBranchValuation (rowIndex : Nat) : Nat -> Nat :=
  extendValuation rowIndex zeroValuation

theorem arithmeticRewritingApp_congr
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

theorem rewriting_embeddedFormulaSubstitution
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

@[simp] theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT]

private abbrev closedShift :=
  FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate.closedShift

@[simp] private theorem closedShift_zero (term : ValuationTerm) :
    closedShift 0 term = term := by
  rfl

@[simp] private theorem closedShift_succ
    (k : Nat) (term : ValuationTerm) :
    closedShift (k + 1) term = Rew.bShift (closedShift k term) := by
  rfl

theorem substitute_closedShift
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

@[simp] theorem free_closedShift_shortBinaryNumeralTerm
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

@[simp] theorem shift_shortBinaryNumeralTerm (value : Nat) :
    Rew.shift (shortBinaryNumeralTerm value) =
      shortBinaryNumeralTerm value := by
  simpa [closedShift, free_bShift_term] using
    (free_closedShift_shortBinaryNumeralTerm 0 value)

@[simp] theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (closedShift 2 (shortBinaryNumeralTerm value)) =
      closedShift 1 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 1 value

@[simp] theorem free_bShift3_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 2))
        (closedShift 3 (shortBinaryNumeralTerm value)) =
      closedShift 2 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 2 value

@[simp] theorem free_bShift4_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 3))
        (closedShift 4 (shortBinaryNumeralTerm value)) =
      closedShift 3 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 3 value

@[simp] theorem free_bShift5_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 4))
        (closedShift 5 (shortBinaryNumeralTerm value)) =
      closedShift 4 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 4 value

@[simp] theorem free_bShift6_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 5))
        (closedShift 6 (shortBinaryNumeralTerm value)) =
      closedShift 5 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 5 value

@[simp] theorem free_bShift7_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 6))
        (closedShift 7 (shortBinaryNumeralTerm value)) =
      closedShift 6 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 6 value

@[simp] theorem free_bShift8_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 7))
        (closedShift 8 (shortBinaryNumeralTerm value)) =
      closedShift 7 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 7 value

@[simp] theorem free_bShift9_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 8))
        (closedShift 9 (shortBinaryNumeralTerm value)) =
      closedShift 8 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 8 value

@[simp] theorem free_bShift10_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 9))
        (closedShift 10 (shortBinaryNumeralTerm value)) =
      closedShift 9 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 9 value

@[simp] theorem free_bShift11_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 10))
        (closedShift 11 (shortBinaryNumeralTerm value)) =
      closedShift 10 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 10 value

@[simp] theorem free_bShift12_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 11))
        (closedShift 12 (shortBinaryNumeralTerm value)) =
      closedShift 11 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 11 value

@[simp] theorem free_bShift13_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 12))
        (closedShift 13 (shortBinaryNumeralTerm value)) =
      closedShift 12 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 12 value

@[simp] theorem free_bShift14_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 13))
        (closedShift 14 (shortBinaryNumeralTerm value)) =
      closedShift 13 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 13 value

@[simp] private theorem free_bShift15_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (closedShift 15 (shortBinaryNumeralTerm value)) =
      closedShift 14 (shortBinaryNumeralTerm value) := by
  exact free_closedShift_shortBinaryNumeralTerm 14 value

@[simp] private theorem free_bvar_fourteen_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#14 : ArithmeticSemiterm Nat 15) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 14))
      (#(Fin.last 14)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem free_bvar_thirteen_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#13 : ArithmeticSemiterm Nat 15) = #13 := by
  exact Rew.free_bvar_castSucc (13 : Fin 14)

@[simp] private theorem free_bvar_twelve_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#12 : ArithmeticSemiterm Nat 15) = #12 := by
  exact Rew.free_bvar_castSucc (12 : Fin 14)

@[simp] private theorem free_bvar_eleven_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#11 : ArithmeticSemiterm Nat 15) = #11 := by
  exact Rew.free_bvar_castSucc (11 : Fin 14)

@[simp] private theorem free_bvar_ten_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#10 : ArithmeticSemiterm Nat 15) = #10 := by
  exact Rew.free_bvar_castSucc (10 : Fin 14)

@[simp] private theorem free_bvar_nine_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#9 : ArithmeticSemiterm Nat 15) = #9 := by
  exact Rew.free_bvar_castSucc (9 : Fin 14)

@[simp] private theorem free_bvar_eight_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#8 : ArithmeticSemiterm Nat 15) = #8 := by
  exact Rew.free_bvar_castSucc (8 : Fin 14)

@[simp] private theorem free_bvar_seven_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#7 : ArithmeticSemiterm Nat 15) = #7 := by
  exact Rew.free_bvar_castSucc (7 : Fin 14)

@[simp] private theorem free_bvar_six_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#6 : ArithmeticSemiterm Nat 15) = #6 := by
  exact Rew.free_bvar_castSucc (6 : Fin 14)

@[simp] private theorem free_bvar_five_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#5 : ArithmeticSemiterm Nat 15) = #5 := by
  exact Rew.free_bvar_castSucc (5 : Fin 14)

@[simp] private theorem free_bvar_four_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#4 : ArithmeticSemiterm Nat 15) = #4 := by
  exact Rew.free_bvar_castSucc (4 : Fin 14)

@[simp] private theorem free_bvar_three_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#3 : ArithmeticSemiterm Nat 15) = #3 := by
  exact Rew.free_bvar_castSucc (3 : Fin 14)

@[simp] private theorem free_bvar_two_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#2 : ArithmeticSemiterm Nat 15) = #2 := by
  exact Rew.free_bvar_castSucc (2 : Fin 14)

@[simp] private theorem free_bvar_one_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#1 : ArithmeticSemiterm Nat 15) = #1 := by
  exact Rew.free_bvar_castSucc (1 : Fin 14)

@[simp] private theorem free_bvar_zero_fin15 :
    (Rew.free (L := ℒₒᵣ) (n := 14))
        (#0 : ArithmeticSemiterm Nat 15) = #0 := by
  exact Rew.free_bvar_castSucc (0 : Fin 14)

/-- The original seven-coordinate graph closed by short binary numerals. -/
def compactNumericVerifierTaskListRowsClosedFormula
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierTaskListRowsGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm taskBoundary,
      shortBinaryNumeralTerm taskCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

/-- The source exponential conjunct, closed by short binary numerals. -/
def compactNumericVerifierTaskListRowsExponentialClosedFormula
    (tableWidth valueBound : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm tableWidth]

/-- The row conjunction under the universal and all fourteen witnesses. -/
def compactNumericVerifierTaskListRowsTerminal
    (tokenTable width tokenCount taskBoundary : Nat) :
    ArithmeticSemiformula Nat 15 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 15 (shortBinaryNumeralTerm taskBoundary),
        closedShift 15 (shortBinaryNumeralTerm tokenCount),
        (#14 : ArithmeticSemiterm Nat 15),
        (#13 : ArithmeticSemiterm Nat 15)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 15 (shortBinaryNumeralTerm taskBoundary),
          closedShift 15 (shortBinaryNumeralTerm tokenCount),
          ‘#14 + 1’,
          (#12 : ArithmeticSemiterm Nat 15)]) ⋏
      ((Rewriting.emb (ξ := Nat)
          compactNumericVerifierTaskCoreGraphDef.val) ⇜
        ![closedShift 15 (shortBinaryNumeralTerm tokenTable),
          closedShift 15 (shortBinaryNumeralTerm width),
          closedShift 15 (shortBinaryNumeralTerm tokenCount),
          (#13 : ArithmeticSemiterm Nat 15), #12, #11, #10, #9, #8,
          #7, #6, #5, #4, #3, #2, #1, #0]))

private def compactNumericVerifierTaskListRowsRawTerminal :
    ArithmeticSemiformula Nat 20 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![(#17 : ArithmeticSemiterm Nat 20), #16, #19, #13]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![(#17 : ArithmeticSemiterm Nat 20), #16, ‘#19 + 1’, #12]) ⋏
      ((Rewriting.emb (ξ := Nat)
          compactNumericVerifierTaskCoreGraphDef.val) ⇜
        ![(#14 : ArithmeticSemiterm Nat 20), #15, #16, #13, #12,
          #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]))

private def compactNumericVerifierTaskListRowsRawBody :
    ArithmeticSemiformula Nat 6 :=
  ((((((((((((((compactNumericVerifierTaskListRowsRawTerminal.bexsLTSucc
      (#17 : ArithmeticSemiterm Nat 19)).bexsLTSucc
      (#16 : ArithmeticSemiterm Nat 18)).bexsLTSucc
      (#15 : ArithmeticSemiterm Nat 17)).bexsLTSucc
      (#14 : ArithmeticSemiterm Nat 16)).bexsLTSucc
      (#13 : ArithmeticSemiterm Nat 15)).bexsLTSucc
      (#12 : ArithmeticSemiterm Nat 14)).bexsLTSucc
      (#11 : ArithmeticSemiterm Nat 13)).bexsLTSucc
      (#10 : ArithmeticSemiterm Nat 12)).bexsLTSucc
      (#9 : ArithmeticSemiterm Nat 11)).bexsLTSucc
      (#8 : ArithmeticSemiterm Nat 10)).bexsLTSucc
      (#7 : ArithmeticSemiterm Nat 9)).bexsLTSucc
      (#6 : ArithmeticSemiterm Nat 8)).bexsLTSucc
      (#5 : ArithmeticSemiterm Nat 7)).bexsLTSucc
      (#4 : ArithmeticSemiterm Nat 6))

private theorem compactNumericVerifierTaskBoundedRowDef_emb_eq_rawBody :
    Rewriting.emb (ξ := Nat) compactNumericVerifierTaskBoundedRowDef.val =
      compactNumericVerifierTaskListRowsRawBody := by
  have hstart :
      (Rew.emb : Rew ℒₒᵣ Empty 20 Nat 20).comp
          (Rew.subst
            ![(#17 : ArithmeticSemiterm Empty 20), #16, #19, #13]) =
        (Rew.subst
          ![(#17 : ArithmeticSemiterm Nat 20), #16, #19, #13]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hfinish :
      (Rew.emb : Rew ℒₒᵣ Empty 20 Nat 20).comp
          (Rew.subst
            ![(#17 : ArithmeticSemiterm Empty 20), #16,
              ‘#19 + 1’, #12]) =
        (Rew.subst
          ![(#17 : ArithmeticSemiterm Nat 20), #16,
            ‘#19 + 1’, #12]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 4 Nat 4) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  have hcore :
      (Rew.emb : Rew ℒₒᵣ Empty 20 Nat 20).comp
          (Rew.subst
            ![(#14 : ArithmeticSemiterm Empty 20), #15, #16, #13, #12,
              #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
        (Rew.subst
          ![(#14 : ArithmeticSemiterm Nat 20), #15, #16, #13, #12,
            #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 17 Nat 17) := by
    apply emb_comp_subst_eq_subst_comp_emb
    intro coordinate
    fin_cases coordinate <;> simp
  unfold compactNumericVerifierTaskBoundedRowDef
  unfold compactNumericVerifierTaskListRowsRawBody
  unfold compactNumericVerifierTaskListRowsRawTerminal
  simp [rewriting_bexsLTSucc,
    rewriting_embeddedFormulaSubstitution,
    Rew.q_bvar_zero, Rew.q_bvar_succ,
    ← TransitiveRewriting.comp_app]
  rw [hstart, hfinish, hcore]

private def compactNumericVerifierTaskListRowsSourceTerms
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    Fin 6 -> ArithmeticSemiterm Nat 1 :=
  ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
    Rew.bShift (shortBinaryNumeralTerm width),
    Rew.bShift (shortBinaryNumeralTerm tokenCount),
    Rew.bShift (shortBinaryNumeralTerm taskBoundary),
    Rew.bShift (shortBinaryNumeralTerm valueBound),
    (#0 : ArithmeticSemiterm Nat 1)]

private def taskListRowsSourceSubstitutionQpow
    (terms : Fin 6 -> ArithmeticSemiterm Nat 1) :
    (depth : Nat) -> Rew ℒₒᵣ Nat (6 + depth) Nat (depth + 1)
  | 0 => Rew.subst terms
  | depth + 1 => (taskListRowsSourceSubstitutionQpow terms depth).q

private def liftFromOne :
    (depth : Nat) -> ArithmeticSemiterm Nat 1 ->
      ArithmeticSemiterm Nat (depth + 1)
  | 0, term => term
  | depth + 1, term => Rew.bShift (liftFromOne depth term)

private def taskListRowsNormalizedBVarResult
    (terms : Fin 6 -> ArithmeticSemiterm Nat 1) (depth : Nat)
    (index : Fin (6 + depth)) : ArithmeticSemiterm Nat (depth + 1) :=
  if hlocal : index.val < depth then
    (#(⟨index.val, by omega⟩ : Fin (depth + 1)) :
      ArithmeticSemiterm Nat (depth + 1))
  else
    liftFromOne depth (terms ⟨index.val - depth, by omega⟩)

private theorem taskListRowsNormalizedBVarResult_eq
    (terms : Fin 6 -> ArithmeticSemiterm Nat 1) :
    forall (depth : Nat) (index : Fin (6 + depth)),
      taskListRowsNormalizedBVarResult terms depth index =
        taskListRowsSourceSubstitutionQpow terms depth
          (#index : ArithmeticSemiterm Nat (6 + depth)) := by
  intro depth
  induction depth with
  | zero =>
      intro index
      simp [taskListRowsNormalizedBVarResult,
        taskListRowsSourceSubstitutionQpow, liftFromOne,
        Rew.subst_bvar]
  | succ depth inductionHypothesis =>
      intro index
      cases index using Fin.cases with
      | zero =>
          simp [taskListRowsNormalizedBVarResult,
            taskListRowsSourceSubstitutionQpow]
      | succ index =>
          rw [show
            taskListRowsSourceSubstitutionQpow terms (depth + 1)
                (#index.succ : ArithmeticSemiterm Nat (6 + (depth + 1))) =
              Rew.bShift
                (taskListRowsSourceSubstitutionQpow terms depth
                  (#index : ArithmeticSemiterm Nat (6 + depth))) by
            change (taskListRowsSourceSubstitutionQpow terms depth).q
                (#index.succ) = _
            rw [Rew.q_bvar_succ]]
          rw [← inductionHypothesis index]
          by_cases hlocal : index.val < depth
          · have hlocalSucc : index.val + 1 < depth + 1 := by omega
            simp [taskListRowsNormalizedBVarResult, hlocal, hlocalSucc]
          · have hlocalSucc : ¬index.val + 1 < depth + 1 := by omega
            simp [taskListRowsNormalizedBVarResult, hlocal, hlocalSucc,
              liftFromOne]

@[simp] private theorem taskListRowsSourceSubstitutionQpow_bvar
    (terms : Fin 6 -> ArithmeticSemiterm Nat 1)
    (depth : Nat) (index : Fin (6 + depth)) :
    taskListRowsSourceSubstitutionQpow terms depth
        (#index : ArithmeticSemiterm Nat (6 + depth)) =
      taskListRowsNormalizedBVarResult terms depth index :=
  (taskListRowsNormalizedBVarResult_eq terms depth index).symm

@[simp] private theorem taskListRowsSourceSubstitutionQpow_bexsLTSucc
    {depth : Nat}
    (terms : Fin 6 -> ArithmeticSemiterm Nat 1)
    (bound : ArithmeticSemiterm Nat (6 + depth))
    (body : ArithmeticSemiformula Nat (6 + (depth + 1))) :
    taskListRowsSourceSubstitutionQpow terms depth ▹
        body.bexsLTSucc bound =
      (taskListRowsSourceSubstitutionQpow terms (depth + 1) ▹ body).bexsLTSucc
        (taskListRowsSourceSubstitutionQpow terms depth bound) := by
  simpa [taskListRowsSourceSubstitutionQpow] using
    (rewriting_bexsLTSucc
      (taskListRowsSourceSubstitutionQpow terms depth) bound body)

private theorem liftFromOne_bShift
    (depth : Nat) (term : ValuationTerm) :
    liftFromOne depth (Rew.bShift term) = closedShift (depth + 1) term := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp [liftFromOne, closedShift, inductionHypothesis]

@[simp] private theorem taskListRowsSourceSubstitutionQpow_valueBound
    (tokenTable width tokenCount taskBoundary valueBound depth : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) depth
        (#(⟨depth + 4, by omega⟩ : Fin (6 + depth)) :
          ArithmeticSemiterm Nat (6 + depth)) =
      closedShift (depth + 1) (shortBinaryNumeralTerm valueBound) := by
  rw [← taskListRowsNormalizedBVarResult_eq]
  simp [taskListRowsNormalizedBVarResult,
    compactNumericVerifierTaskListRowsSourceTerms,
    liftFromOne_bShift]

private theorem taskListRowsSourceSubstitutionQpow_bound0
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 0
        (#4 : ArithmeticSemiterm Nat 6) =
      closedShift 1 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 0

private theorem taskListRowsSourceSubstitutionQpow_bound1
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 1
        (#5 : ArithmeticSemiterm Nat 7) =
      closedShift 2 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 1

private theorem taskListRowsSourceSubstitutionQpow_bound2
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 2
        (#6 : ArithmeticSemiterm Nat 8) =
      closedShift 3 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 2

private theorem taskListRowsSourceSubstitutionQpow_bound3
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 3
        (#7 : ArithmeticSemiterm Nat 9) =
      closedShift 4 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 3

private theorem taskListRowsSourceSubstitutionQpow_bound4
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 4
        (#8 : ArithmeticSemiterm Nat 10) =
      closedShift 5 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 4

private theorem taskListRowsSourceSubstitutionQpow_bound5
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 5
        (#9 : ArithmeticSemiterm Nat 11) =
      closedShift 6 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 5

private theorem taskListRowsSourceSubstitutionQpow_bound6
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 6
        (#10 : ArithmeticSemiterm Nat 12) =
      closedShift 7 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 6

private theorem taskListRowsSourceSubstitutionQpow_bound7
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 7
        (#11 : ArithmeticSemiterm Nat 13) =
      closedShift 8 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 7

private theorem taskListRowsSourceSubstitutionQpow_bound8
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 8
        (#12 : ArithmeticSemiterm Nat 14) =
      closedShift 9 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 8

private theorem taskListRowsSourceSubstitutionQpow_bound9
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 9
        (#13 : ArithmeticSemiterm Nat 15) =
      closedShift 10 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 9

private theorem taskListRowsSourceSubstitutionQpow_bound10
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 10
        (#14 : ArithmeticSemiterm Nat 16) =
      closedShift 11 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 10

private theorem taskListRowsSourceSubstitutionQpow_bound11
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 11
        (#15 : ArithmeticSemiterm Nat 17) =
      closedShift 12 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 11

private theorem taskListRowsSourceSubstitutionQpow_bound12
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 12
        (#16 : ArithmeticSemiterm Nat 18) =
      closedShift 13 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 12

private theorem taskListRowsSourceSubstitutionQpow_bound13
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 13
        (#17 : ArithmeticSemiterm Nat 19) =
      closedShift 14 (shortBinaryNumeralTerm valueBound) := by
  simpa using taskListRowsSourceSubstitutionQpow_valueBound
    tokenTable width tokenCount taskBoundary valueBound 13

private theorem compactNumericVerifierTaskListRowsRawTerminal_rewriting
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 14 ▹
      compactNumericVerifierTaskListRowsRawTerminal =
    compactNumericVerifierTaskListRowsTerminal
      tokenTable width tokenCount taskBoundary := by
  unfold compactNumericVerifierTaskListRowsRawTerminal
  unfold compactNumericVerifierTaskListRowsTerminal
  simp [rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [taskListRowsSourceSubstitutionQpow,
          Rew.q, Rew.q_bvar_zero, Rew.q_bvar_succ,
          Rew.comp_app, Rew.subst_bvar,
          compactNumericVerifierTaskListRowsSourceTerms,
          liftFromOne, closedShift]
    · intro coordinate
      exact Empty.elim coordinate

/-- The row body obtained directly by substituting the source row predicate. -/
def compactNumericVerifierTaskListRowsSourceUniversalBody
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierTaskBoundedRowDef.val) ⇜
    compactNumericVerifierTaskListRowsSourceTerms
      tokenTable width tokenCount taskBoundary valueBound

/-- One row of the source universal with all fourteen bounded binders. -/
def compactNumericVerifierTaskListRowsUniversalBody
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    ArithmeticSemiformula Nat 1 :=
  ((((((((((((((compactNumericVerifierTaskListRowsTerminal
      tokenTable width tokenCount taskBoundary).bexsLTSucc
        (closedShift 14 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 13 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 12 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 11 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 10 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 9 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 8 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 7 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 6 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 5 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 4 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
      (closedShift 1 (shortBinaryNumeralTerm valueBound))

/-- The exponential conjunct followed by the explicit task-count universal. -/
def compactNumericVerifierTaskListRowsExplicitFormula
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat) : ValuationFormula :=
  compactNumericVerifierTaskListRowsExponentialClosedFormula
      tableWidth valueBound ⋏
    (compactNumericVerifierTaskListRowsUniversalBody
      tokenTable width tokenCount taskBoundary valueBound).ballLT
        (shortBinaryNumeralTerm taskCount)

/-- The substituted source row is the hand-exposed fourteen-witness body. -/
theorem compactNumericVerifierTaskListRowsSourceUniversalBody_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    compactNumericVerifierTaskListRowsSourceUniversalBody
        tokenTable width tokenCount taskBoundary valueBound =
      compactNumericVerifierTaskListRowsUniversalBody
        tokenTable width tokenCount taskBoundary valueBound := by
  unfold compactNumericVerifierTaskListRowsSourceUniversalBody
  rw [compactNumericVerifierTaskBoundedRowDef_emb_eq_rawBody]
  change
    taskListRowsSourceSubstitutionQpow
        (compactNumericVerifierTaskListRowsSourceTerms
          tokenTable width tokenCount taskBoundary valueBound) 0 ▹
      compactNumericVerifierTaskListRowsRawBody = _
  unfold compactNumericVerifierTaskListRowsUniversalBody
  unfold compactNumericVerifierTaskListRowsRawBody
  simp only [taskListRowsSourceSubstitutionQpow_bexsLTSucc]
  rw [taskListRowsSourceSubstitutionQpow_bound0,
    taskListRowsSourceSubstitutionQpow_bound1,
    taskListRowsSourceSubstitutionQpow_bound2,
    taskListRowsSourceSubstitutionQpow_bound3,
    taskListRowsSourceSubstitutionQpow_bound4,
    taskListRowsSourceSubstitutionQpow_bound5,
    taskListRowsSourceSubstitutionQpow_bound6,
    taskListRowsSourceSubstitutionQpow_bound7,
    taskListRowsSourceSubstitutionQpow_bound8,
    taskListRowsSourceSubstitutionQpow_bound9,
    taskListRowsSourceSubstitutionQpow_bound10,
    taskListRowsSourceSubstitutionQpow_bound11,
    taskListRowsSourceSubstitutionQpow_bound12,
    taskListRowsSourceSubstitutionQpow_bound13,
    compactNumericVerifierTaskListRowsRawTerminal_rewriting]

private theorem compactNumericVerifierTaskListRowsClosedFormula_source_alignment
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat) :
    compactNumericVerifierTaskListRowsClosedFormula
        tokenTable width tokenCount taskBoundary taskCount
          tableWidth valueBound =
      (compactNumericVerifierTaskListRowsExponentialClosedFormula
          tableWidth valueBound ⋏
        (compactNumericVerifierTaskListRowsSourceUniversalBody
          tokenTable width tokenCount taskBoundary valueBound).ballLT
            (shortBinaryNumeralTerm taskCount)) := by
  unfold compactNumericVerifierTaskListRowsClosedFormula
  unfold compactNumericVerifierTaskListRowsExponentialClosedFormula
  unfold compactNumericVerifierTaskListRowsSourceUniversalBody
  unfold compactNumericVerifierTaskListRowsGraphDef
  simp [Semiformula.ballLT, LO.FirstOrder.ball,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app, Function.comp_def]
  have htokenTable :
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#1 : ArithmeticSemiterm Nat 8) =
        Rew.bShift (shortBinaryNumeralTerm tokenTable) := by
    change
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#((0 : Fin 7).succ)) = _
    rw [Rew.q_bvar_succ, Rew.subst_bvar]
    rfl
  have hwidth :
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#2 : ArithmeticSemiterm Nat 8) =
        Rew.bShift (shortBinaryNumeralTerm width) := by
    change
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#((1 : Fin 7).succ)) = _
    rw [Rew.q_bvar_succ, Rew.subst_bvar]
    rfl
  have htokenCount :
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#3 : ArithmeticSemiterm Nat 8) =
        Rew.bShift (shortBinaryNumeralTerm tokenCount) := by
    change
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#((2 : Fin 7).succ)) = _
    rw [Rew.q_bvar_succ, Rew.subst_bvar]
    rfl
  have htaskBoundary :
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#4 : ArithmeticSemiterm Nat 8) =
        Rew.bShift (shortBinaryNumeralTerm taskBoundary) := by
    change
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#((3 : Fin 7).succ)) = _
    rw [Rew.q_bvar_succ, Rew.subst_bvar]
    rfl
  have htaskCount :
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#5 : ArithmeticSemiterm Nat 8) =
        Rew.bShift (shortBinaryNumeralTerm taskCount) := by
    change
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#((4 : Fin 7).succ)) = _
    rw [Rew.q_bvar_succ, Rew.subst_bvar]
    rfl
  have hvalueBound :
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#7 : ArithmeticSemiterm Nat 8) =
        Rew.bShift (shortBinaryNumeralTerm valueBound) := by
    change
      (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm taskCount,
          shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm valueBound]).q
          (#((6 : Fin 7).succ)) = _
    rw [Rew.q_bvar_succ, Rew.subst_bvar]
    rfl
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
    · intro index
      exact Empty.elim index
  · constructor
    · exact htaskCount
    · apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, htokenTable, hwidth,
            htokenCount, htaskBoundary, hvalueBound,
            compactNumericVerifierTaskListRowsSourceTerms]
      · intro index
        exact Empty.elim index

/-- Exact closed alignment with the original task-list row graph. -/
theorem compactNumericVerifierTaskListRowsClosedFormula_alignment
    (tokenTable width tokenCount taskBoundary taskCount
      tableWidth valueBound : Nat) :
    compactNumericVerifierTaskListRowsClosedFormula
        tokenTable width tokenCount taskBoundary taskCount
          tableWidth valueBound =
      compactNumericVerifierTaskListRowsExplicitFormula
        tokenTable width tokenCount taskBoundary taskCount
          tableWidth valueBound := by
  rw [compactNumericVerifierTaskListRowsClosedFormula_source_alignment]
  unfold compactNumericVerifierTaskListRowsExplicitFormula
  rw [compactNumericVerifierTaskListRowsSourceUniversalBody_alignment]

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
