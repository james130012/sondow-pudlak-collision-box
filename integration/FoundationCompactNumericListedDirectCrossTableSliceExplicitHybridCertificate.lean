import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for cross-table slice equality

The two bounded universal layers are materialized branch by branch.  The
constructor below receives the count witness and every arithmetic and bit
fact explicitly; it does not recover certificate data from semantic truth.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate

open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactBinaryNumeralTerm
open FoundationCompactCertifiedContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAFastArithmeticLeafRecognizer
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPABitMembershipRuleCompiler
open FoundationCompactPABitMembershipValuationContextCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : LO.FirstOrder.ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
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
    (operator : LO.FirstOrder.Semiformula.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ operator.operator terms =
      operator.operator (rewriting ∘ terms) := by
  unfold LO.FirstOrder.Semiformula.Operator.operator
  exact rewriting_embeddedFormulaSubstitution
    rewriting operator.sentence terms

private theorem rewriting_ballLT
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (body : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      (sourceArity + 1))
    (bound : LO.FirstOrder.ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ body.ballLT bound =
      (rewriting.q ▹ body).ballLT (rewriting bound) := by
  have hguardTerms :
      rewriting.q ∘
          ![(#0 : LO.FirstOrder.ArithmeticSemiterm sourceVariables
              (sourceArity + 1)), Rew.bShift bound] =
        ![(#0 : LO.FirstOrder.ArithmeticSemiterm targetVariables
              (targetArity + 1)), Rew.bShift (rewriting bound)] := by
    funext coordinate
    cases coordinate using Fin.cases with
    | zero => exact Rew.q_bvar_zero rewriting
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Rew.q_comp_bShift_app rewriting bound
        | succ coordinate => exact Fin.elim0 coordinate
  unfold LO.FirstOrder.Semiformula.ballLT
  rw [Rewriting.smul_ball, rewriting_formulaOperator, hguardTerms]

private theorem membershipOperator_eq_binaryBitAtomAtTerms
    {boundArity : Nat}
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat boundArity) :
    LO.FirstOrder.Semiformula.Operator.Mem.mem.operator
        ![indexTerm, valueTerm] =
      binaryBitAtomAtTerms indexTerm valueTerm := by
  unfold binaryBitAtomAtTerms
  unfold LO.FirstOrder.Semiformula.Operator.operator
  rw [LO.FirstOrder.Arithmetic.operator_mem_def]

@[simp] private theorem q_bvar_one
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 1 targetVariables targetArity) :
    rewriting.q (#1 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 2) =
      Rew.bShift (rewriting #0) := by
  change rewriting.q (#((0 : Fin 1).succ)) = Rew.bShift (rewriting #0)
  exact Rew.q_bvar_succ rewriting 0

@[simp] private theorem q_bvar_one_fin3
    {sourceVariables targetVariables : Type*} {targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables 2 targetVariables targetArity) :
    rewriting.q (#1 : LO.FirstOrder.ArithmeticSemiterm sourceVariables 3) =
      Rew.bShift (rewriting #0) := by
  change rewriting.q (#((0 : Fin 2).succ)) = Rew.bShift (rewriting #0)
  exact Rew.q_bvar_succ rewriting 0

@[simp] private theorem subst_qq_bvar_one (term : ValuationTerm) :
    (Rew.subst ![term]).q.q
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 3) = #1 := by
  rw [q_bvar_one_fin3, Rew.q_bvar_zero]
  rfl

@[simp] private theorem free_bvar_one_fin2 :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (#1 : LO.FirstOrder.ArithmeticSemiterm Nat 2) = &0 := by
  change (Rew.free (L := ℒₒᵣ) (n := 1)) (#(Fin.last 1)) = &0
  exact Rew.free_bvar_last

@[simp] private theorem shift_shortBinaryNumeralTerm (value : Nat) :
    Rew.shift (shortBinaryNumeralTerm value) =
      shortBinaryNumeralTerm value := by
  have h := LO.FirstOrder.Semiterm.rew_eq_of_funEqOn
    (Rew.shift : Rew ℒₒᵣ Nat 0 Nat 0) Rew.id
    (shortBinaryNumeralTerm value)
    (fun index => Fin.elim0 index)
    (fun index hindex => by
      have : index ∈ (shortBinaryNumeralTerm value).freeVariables := hindex
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa using h

@[simp] private theorem free_bShift2_shortBinaryNumeralTerm (value : Nat) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift (shortBinaryNumeralTerm value))) =
      Rew.bShift (shortBinaryNumeralTerm value) := by
  let composite :=
    ((Rew.free (L := ℒₒᵣ) (n := 1)).comp Rew.bShift).comp Rew.bShift
  have h := LO.FirstOrder.Semiterm.rew_eq_of_funEqOn
    composite Rew.bShift (shortBinaryNumeralTerm value)
    (fun index => Fin.elim0 index)
    (fun index hindex => by
      have : index ∈ (shortBinaryNumeralTerm value).freeVariables := hindex
      rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at this
      simp at this)
  simpa [composite, Rew.comp_app] using h

/-- The ten-coordinate closed instance of the quoted cross-table predicate. -/
def compactFixedWidthCrossTableSlicesEqClosedFormula
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) compactFixedWidthCrossTableSlicesEqDef.val) ⇜
    ![shortBinaryNumeralTerm sourceTable,
      shortBinaryNumeralTerm sourceWidth,
      shortBinaryNumeralTerm sourceTokenCount,
      shortBinaryNumeralTerm sourceStart,
      shortBinaryNumeralTerm sourceFinish,
      shortBinaryNumeralTerm targetTable,
      shortBinaryNumeralTerm targetWidth,
      shortBinaryNumeralTerm targetTokenCount,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm targetFinish]

private def crossTableWitnessBody
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm sourceTokenCount)) + 1 ∧
    #0 ≤ !!(Rew.bShift (shortBinaryNumeralTerm targetTokenCount)) ∧
    !!(Rew.bShift (shortBinaryNumeralTerm sourceFinish)) =
      !!(Rew.bShift (shortBinaryNumeralTerm sourceStart)) + #0 ∧
    !!(Rew.bShift (shortBinaryNumeralTerm targetFinish)) =
      !!(Rew.bShift (shortBinaryNumeralTerm targetStart)) + #0 ∧
    !!(Rew.bShift (shortBinaryNumeralTerm sourceFinish)) ≤
      !!(Rew.bShift (shortBinaryNumeralTerm sourceTokenCount)) ∧
    !!(Rew.bShift (shortBinaryNumeralTerm targetFinish)) ≤
      !!(Rew.bShift (shortBinaryNumeralTerm targetTokenCount)) ∧
    ∀ offset < #0,
      ∀ bitIndex <
          !!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm sourceWidth))) +
          !!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm targetWidth))),
        ((bitIndex <
              !!(Rew.bShift (Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm sourceWidth)))) ∧
            !bitDef
              ((!!(Rew.bShift (Rew.bShift (Rew.bShift
                    (shortBinaryNumeralTerm sourceStart)))) + offset) *
                  !!(Rew.bShift (Rew.bShift (Rew.bShift
                    (shortBinaryNumeralTerm sourceWidth)))) + bitIndex)
              !!(Rew.bShift (Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm sourceTable))))) ↔
          (bitIndex <
              !!(Rew.bShift (Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm targetWidth)))) ∧
            !bitDef
              ((!!(Rew.bShift (Rew.bShift (Rew.bShift
                    (shortBinaryNumeralTerm targetStart)))) + offset) *
                  !!(Rew.bShift (Rew.bShift (Rew.bShift
                    (shortBinaryNumeralTerm targetWidth)))) + bitIndex)
              !!(Rew.bShift (Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm targetTable))))))”

private def crossTablePostWitnessFormula
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat) : ArithmeticProposition :=
  (Rew.subst ![shortBinaryNumeralTerm count]) ▹
    crossTableWitnessBody sourceTable sourceWidth sourceTokenCount sourceStart
      sourceFinish targetTable targetWidth targetTokenCount targetStart
      targetFinish

private theorem crossTableWitnessBody_subst
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat) :
    (crossTableWitnessBody sourceTable sourceWidth sourceTokenCount sourceStart
      sourceFinish targetTable targetWidth targetTokenCount targetStart
      targetFinish)/[shortBinaryNumeralTerm count] =
      crossTablePostWitnessFormula sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish count := by
  rfl

private def crossTableSourceTail :
    LO.FirstOrder.ArithmeticSemiformula Empty 11 :=
  “#0 ≤ #8 ∧
    #5 = #4 + #0 ∧
    #10 = #9 + #0 ∧
    #5 ≤ #3 ∧
    #10 ≤ #8 ∧
    ∀ offset < #0,
      ∀ bitIndex < #3 + #8,
        ((bitIndex < #4 ∧
            ((#6 + offset) * #4 + bitIndex) ∈ #3) ↔
          (bitIndex < #9 ∧
            ((#11 + offset) * #9 + bitIndex) ∈ #8))”

private def crossTableSourceBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 11 :=
  “#0 < #3 + 1” ⋏ crossTableSourceTail

private theorem bShift_crossTableSourceCountBound :
    Rew.bShift
        (‘#2 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 10) =
      (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 11) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem compactFixedWidthCrossTableSlicesEqDef_val_eq_exists :
    compactFixedWidthCrossTableSlicesEqDef.val =
      ∃⁰ crossTableSourceBody := by
  unfold compactFixedWidthCrossTableSlicesEqDef
  change crossTableSourceTail.bexsLTSucc
      (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 10) =
    ∃⁰ crossTableSourceBody
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
    LO.FirstOrder.Semiformula.bexsLT crossTableSourceBody
  rw [bShift_crossTableSourceCountBound]
  rfl

private def crossTableOuterTerms
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 10 -> ValuationTerm :=
  ![shortBinaryNumeralTerm sourceTable,
    shortBinaryNumeralTerm sourceWidth,
    shortBinaryNumeralTerm sourceTokenCount,
    shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceFinish,
    shortBinaryNumeralTerm targetTable,
    shortBinaryNumeralTerm targetWidth,
    shortBinaryNumeralTerm targetTokenCount,
    shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetFinish]

private def crossTableBodyTerms
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 11 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift (shortBinaryNumeralTerm sourceTable),
    Rew.bShift (shortBinaryNumeralTerm sourceWidth),
    Rew.bShift (shortBinaryNumeralTerm sourceTokenCount),
    Rew.bShift (shortBinaryNumeralTerm sourceStart),
    Rew.bShift (shortBinaryNumeralTerm sourceFinish),
    Rew.bShift (shortBinaryNumeralTerm targetTable),
    Rew.bShift (shortBinaryNumeralTerm targetWidth),
    Rew.bShift (shortBinaryNumeralTerm targetTokenCount),
    Rew.bShift (shortBinaryNumeralTerm targetStart),
    Rew.bShift (shortBinaryNumeralTerm targetFinish)]

private def crossTableOffsetTerms
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 12 -> LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2), #1,
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceTable)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceWidth)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceTokenCount)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceStart)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceFinish)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetTable)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetWidth)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetTokenCount)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetStart)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetFinish))]

private def crossTableBitTerms
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Fin 13 -> LO.FirstOrder.ArithmeticSemiterm Nat 3 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3), #1, #2,
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceTable))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceWidth))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceTokenCount))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceStart))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceFinish))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetTable))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetWidth))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetTokenCount))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetStart))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetFinish)))]

private theorem crossTableBodyRewriting_eq_embSubsts
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (Rew.subst (crossTableOuterTerms sourceTable sourceWidth sourceTokenCount
      sourceStart sourceFinish targetTable targetWidth targetTokenCount
      targetStart targetFinish)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 11 Nat 11) =
      Rew.embSubsts
        (crossTableBodyTerms sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.comp_app, Rew.q_bvar_zero, Rew.embSubsts_bvar,
          crossTableBodyTerms]
    | succ coordinate =>
        simp only [Rew.comp_app, Rew.emb_bvar, Rew.q_bvar_succ,
          Rew.embSubsts_bvar]
        rw [Rew.subst_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem crossTableBodyRewriting_q_eq_embSubsts
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (Rew.embSubsts
      (crossTableBodyTerms sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish)).q =
      Rew.embSubsts
        (crossTableOffsetTerms sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar,
          crossTableOffsetTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem crossTableBodyRewriting_qq_eq_embSubsts
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (Rew.embSubsts
      (crossTableBodyTerms sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish)).q.q =
      Rew.embSubsts
        (crossTableBitTerms sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish) := by
  rw [crossTableBodyRewriting_q_eq_embSubsts]
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar,
          crossTableBitTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem crossTableSourceBody_rewrite
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    Rew.embSubsts
        (crossTableBodyTerms sourceTable sourceWidth sourceTokenCount
          sourceStart sourceFinish targetTable targetWidth targetTokenCount
          targetStart targetFinish) ▹ crossTableSourceBody =
      crossTableWitnessBody sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish := by
  unfold crossTableSourceBody crossTableSourceTail crossTableWitnessBody
  simp only [LogicalConnective.HomClass.map_and, rewriting_ballLT]
  rw [crossTableBodyRewriting_qq_eq_embSubsts,
    crossTableBodyRewriting_q_eq_embSubsts]
  simp [crossTableBodyTerms, crossTableOffsetTerms, crossTableBitTerms,
    membershipOperator_eq_binaryBitAtomAtTerms, binaryBitAtomAtTerms]

private theorem compactFixedWidthCrossTableSlicesEqClosedFormula_alignment
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    compactFixedWidthCrossTableSlicesEqClosedFormula sourceTable sourceWidth
        sourceTokenCount sourceStart sourceFinish targetTable targetWidth
        targetTokenCount targetStart targetFinish =
      ∃⁰ crossTableWitnessBody sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish := by
  unfold compactFixedWidthCrossTableSlicesEqClosedFormula
  rw [compactFixedWidthCrossTableSlicesEqDef_val_eq_exists]
  change
    Rew.subst (crossTableOuterTerms sourceTable sourceWidth sourceTokenCount
      sourceStart sourceFinish targetTable targetWidth targetTokenCount
      targetStart targetFinish) ▹
        (Rewriting.emb (ξ := Nat) (∃⁰ crossTableSourceBody)) = _
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [← TransitiveRewriting.comp_app,
    crossTableBodyRewriting_eq_embSubsts,
    crossTableSourceBody_rewrite]

private def crossTableBitBoundTerm
    (sourceWidth targetWidth : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm sourceWidth) +
    !!(shortBinaryNumeralTerm targetWidth)’

private def crossTableOffsetBitBody
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  “((#0 <
          !!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm sourceWidth))) ∧
        !bitDef
          ((!!(Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm sourceStart))) + #1) *
              !!(Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm sourceWidth))) + #0)
          !!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm sourceTable)))) ↔
      (#0 <
          !!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm targetWidth))) ∧
        !bitDef
          ((!!(Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm targetStart))) + #1) *
              !!(Rew.bShift (Rew.bShift
                (shortBinaryNumeralTerm targetWidth))) + #0)
          !!(Rew.bShift (Rew.bShift
            (shortBinaryNumeralTerm targetTable)))))”

private def crossTableOffsetBody
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (crossTableOffsetBitBody sourceTable sourceWidth sourceStart targetTable
    targetWidth targetStart).ballLT
      (Rew.bShift (crossTableBitBoundTerm sourceWidth targetWidth))

private def crossTableBitBody
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “((#0 < !!(Rew.bShift (shortBinaryNumeralTerm sourceWidth)) ∧
        !bitDef
          ((!!(Rew.bShift (shortBinaryNumeralTerm sourceStart)) +
                !!(Rew.bShift (&0 : ValuationTerm))) *
              !!(Rew.bShift (shortBinaryNumeralTerm sourceWidth)) + #0)
          !!(Rew.bShift (shortBinaryNumeralTerm sourceTable))) ↔
      (#0 < !!(Rew.bShift (shortBinaryNumeralTerm targetWidth)) ∧
        !bitDef
          ((!!(Rew.bShift (shortBinaryNumeralTerm targetStart)) +
                !!(Rew.bShift (&0 : ValuationTerm))) *
              !!(Rew.bShift (shortBinaryNumeralTerm targetWidth)) + #0)
          !!(Rew.bShift (shortBinaryNumeralTerm targetTable))))”

private def crossTableBitUniversalFormula
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    ValuationFormula :=
  (crossTableBitBody sourceTable sourceWidth sourceStart targetTable targetWidth
    targetStart).ballLT (crossTableBitBoundTerm sourceWidth targetWidth)

private def crossTableOffsetUniversalFormula
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart
      count : Nat) : ArithmeticProposition :=
  (crossTableOffsetBody sourceTable sourceWidth sourceStart targetTable
    targetWidth targetStart).ballLT (shortBinaryNumeralTerm count)

private def crossTableBitIndexTerm
    (start width : Nat) : ValuationTerm :=
  ‘(!!(shortBinaryNumeralTerm start) + &1) *
      !!(shortBinaryNumeralTerm width) + &0’

private def crossTableWidthAtom (width : Nat) : ValuationFormula :=
  “&0 < !!(shortBinaryNumeralTerm width)”

private def crossTableBitAtom
    (table start width : Nat) : ValuationFormula :=
  binaryBitAtomAtTerms (crossTableBitIndexTerm start width)
    (shortBinaryNumeralTerm table)

private def crossTableBitCondition
    (table start width : Nat) : ValuationFormula :=
  crossTableWidthAtom width ⋏ crossTableBitAtom table start width

private def crossTableExplicitBitFormula
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    ValuationFormula :=
  crossTableBitCondition sourceTable sourceStart sourceWidth 🡘
    crossTableBitCondition targetTable targetStart targetWidth

private def crossTableDecomposedPostWitnessFormula
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat) : ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm count) <
      !!(shortBinaryNumeralTerm sourceTokenCount) + 1” ⋏
    (“!!(shortBinaryNumeralTerm count) ≤
        !!(shortBinaryNumeralTerm targetTokenCount)” ⋏
      (“!!(shortBinaryNumeralTerm sourceFinish) =
          !!(shortBinaryNumeralTerm sourceStart) +
            !!(shortBinaryNumeralTerm count)” ⋏
        (“!!(shortBinaryNumeralTerm targetFinish) =
            !!(shortBinaryNumeralTerm targetStart) +
              !!(shortBinaryNumeralTerm count)” ⋏
          (“!!(shortBinaryNumeralTerm sourceFinish) ≤
              !!(shortBinaryNumeralTerm sourceTokenCount)” ⋏
            (“!!(shortBinaryNumeralTerm targetFinish) ≤
                !!(shortBinaryNumeralTerm targetTokenCount)” ⋏
              crossTableOffsetUniversalFormula sourceTable sourceWidth
                sourceStart targetTable targetWidth targetStart count)))))

private theorem crossTablePostWitnessFormula_alignment
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat) :
    crossTablePostWitnessFormula sourceTable sourceWidth sourceTokenCount
        sourceStart sourceFinish targetTable targetWidth targetTokenCount
        targetStart targetFinish count =
      crossTableDecomposedPostWitnessFormula sourceTable sourceWidth
        sourceTokenCount sourceStart sourceFinish targetTable targetWidth
        targetTokenCount targetStart targetFinish count := by
  simp [crossTablePostWitnessFormula, crossTableWitnessBody,
    crossTableDecomposedPostWitnessFormula,
    crossTableOffsetUniversalFormula, crossTableOffsetBody,
    crossTableOffsetBitBody, crossTableBitBoundTerm,
    rewriting_ballLT, rewriting_embeddedFormulaSubstitution]

private theorem crossTableOffsetBody_free_alignment
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    Rewriting.free
        (crossTableOffsetBody sourceTable sourceWidth sourceStart targetTable
          targetWidth targetStart) =
      crossTableBitUniversalFormula sourceTable sourceWidth sourceStart
        targetTable targetWidth targetStart := by
  simp [crossTableOffsetBody, crossTableOffsetBitBody,
    crossTableBitUniversalFormula, crossTableBitBody,
    crossTableBitBoundTerm, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution,
    free_bShift2_shortBinaryNumeralTerm, free_bvar_one_fin2,
    shift_shortBinaryNumeralTerm]

private theorem crossTableBitBody_free_alignment
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart : Nat) :
    Rewriting.free
        (crossTableBitBody sourceTable sourceWidth sourceStart targetTable
          targetWidth targetStart) =
      crossTableExplicitBitFormula sourceTable sourceWidth sourceStart
        targetTable targetWidth targetStart := by
  simp [crossTableBitBody, crossTableExplicitBitFormula,
    crossTableBitCondition, crossTableWidthAtom, crossTableBitAtom,
    crossTableBitIndexTerm, rewriting_embeddedFormulaSubstitution,
    shift_shortBinaryNumeralTerm, binaryBitAtomAtTerms]

private abbrev CrossTableHybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left * !!right’ : ValuationTerm) =
      LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left + !!right’) =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (‘!!left * !!right’) =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def sourceCountGuardCertificate
    (sourceTokenCount count : Nat)
    (hbound : count <= sourceTokenCount) :
    CrossTableHybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm count) <
        !!(shortBinaryNumeralTerm sourceTokenCount) + 1” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm count,
        (‘!!(shortBinaryNumeralTerm sourceTokenCount) + 1’ :
          ValuationTerm)] (by
        change termValue zeroValuation (shortBinaryNumeralTerm count) <
          termValue zeroValuation
            (‘!!(shortBinaryNumeralTerm sourceTokenCount) + 1’ :
              ValuationTerm)
        simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using Nat.lt_succ_of_le hbound)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left <= right) :
    CrossTableHybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  let leftTerm : ValuationTerm := shortBinaryNumeralTerm left
  let rightTerm : ValuationTerm := shortBinaryNumeralTerm right
  if hequal : left = right then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![leftTerm, rightTerm] (by
          change termValue zeroValuation leftTerm =
            termValue zeroValuation rightTerm
          simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm]
            using hequal)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![leftTerm, rightTerm]) equality
    exact .cast
      (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct
  else
    have hstrict : left < right := Nat.lt_of_le_of_ne hle hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] (by
          change termValue zeroValuation leftTerm <
            termValue zeroValuation rightTerm
          simpa [leftTerm, rightTerm, termValue_shortBinaryNumeralTerm]
            using hstrict)
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![leftTerm, rightTerm]) strict
    exact .cast
      (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct

private noncomputable def closedEndpointCertificate
    (start finish count : Nat) (hendpoint : finish = start + count) :
    CrossTableHybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm finish) =
        !!(shortBinaryNumeralTerm start) +
          !!(shortBinaryNumeralTerm count)” := by
  let rightTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm start) +
      !!(shortBinaryNumeralTerm count)’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm finish, rightTerm] (by
        change termValue zeroValuation (shortBinaryNumeralTerm finish) =
          termValue zeroValuation rightTerm
        simpa [rightTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd] using hendpoint)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private theorem binaryBitHybridVariablesTrue
    (indexTerm valueTerm : ValuationTerm) :
    indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
      (binaryBitAtValuationFormula true
        indexTerm valueTerm).freeVariables := by
  simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms,
    FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
      bitInstance_argument_freeVariables_union_subset indexTerm valueTerm

private theorem binaryBitFalse_freeVariables_eq_true
    (indexTerm valueTerm : ValuationTerm) :
    (binaryBitAtValuationFormula false indexTerm valueTerm).freeVariables =
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simp [binaryBitAtValuationFormula, binaryBitLiteralAtTerms]

private noncomputable def widthTrueCertificate
    (valuation : Nat -> Nat) (width bitIndex : Nat)
    (hwidth : bitIndex < width)
    (hbitValue : termValue valuation (&0 : ValuationTerm) = bitIndex) :
    CrossTableHybridCertificate valuation (crossTableWidthAtom width) := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![(&0 : ValuationTerm), shortBinaryNumeralTerm width] (by
        change termValue valuation (&0 : ValuationTerm) <
          termValue valuation (shortBinaryNumeralTerm width)
        simpa [hbitValue, termValue_shortBinaryNumeralTerm] using hwidth)
  exact .cast (by
    unfold crossTableWidthAtom
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def widthFalseCertificate
    (valuation : Nat -> Nat) (width bitIndex : Nat)
    (hwidth : ¬bitIndex < width)
    (hbitValue : termValue valuation (&0 : ValuationTerm) = bitIndex) :
    CrossTableHybridCertificate valuation (∼crossTableWidthAtom width) := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
      valuation Language.ORing.Rel.lt
      ![(&0 : ValuationTerm), shortBinaryNumeralTerm width] (by
        change ¬termValue valuation (&0 : ValuationTerm) <
          termValue valuation (shortBinaryNumeralTerm width)
        simpa [hbitValue, termValue_shortBinaryNumeralTerm] using hwidth)
  exact .cast (by
    change
      (∼LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
        ![(&0 : ValuationTerm), shortBinaryNumeralTerm width]) =
        ∼crossTableWidthAtom width
    congr 1) direct

private noncomputable def bitConditionTrueCertificate
    (table start width offset bitIndex : Nat)
    (hcondition : bitIndex < width ∧
      table.testBit ((start + offset) * width + bitIndex) = true) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset zeroValuation))
      (crossTableBitCondition table start width) := by
  let valuation :=
    extendValuation bitIndex (extendValuation offset zeroValuation)
  let indexTerm := crossTableBitIndexTerm start width
  let valueTerm : ValuationTerm := shortBinaryNumeralTerm table
  let widthCertificate := widthTrueCertificate valuation width bitIndex
    hcondition.1 rfl
  have hvariables :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          indexTerm valueTerm).freeVariables :=
    binaryBitHybridVariablesTrue indexTerm valueTerm
  let bitCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
      valuation indexTerm valueTerm (by
        simpa [valuation, indexTerm, valueTerm, crossTableBitIndexTerm,
          termValue_arithmeticAdd, termValue_arithmeticMul,
          termValue_shortBinaryNumeralTerm] using hcondition.2) hvariables
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    widthCertificate bitCertificate

private noncomputable def bitConditionFalseCertificate
    (table start width offset bitIndex : Nat)
    (hcondition : ¬(bitIndex < width ∧
      table.testBit ((start + offset) * width + bitIndex) = true)) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset zeroValuation))
      (∼crossTableBitCondition table start width) := by
  let valuation :=
    extendValuation bitIndex (extendValuation offset zeroValuation)
  let indexTerm := crossTableBitIndexTerm start width
  let valueTerm : ValuationTerm := shortBinaryNumeralTerm table
  by_cases hwidth : bitIndex < width
  · have hbitFalse :
        table.testBit ((start + offset) * width + bitIndex) = false := by
      cases hbit : table.testBit ((start + offset) * width + bitIndex) with
      | false => rfl
      | true => exact False.elim (hcondition ⟨hwidth, hbit⟩)
    have hvariablesTrue :
        indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
          (binaryBitAtValuationFormula true
            indexTerm valueTerm).freeVariables :=
      binaryBitHybridVariablesTrue indexTerm valueTerm
    have hvariablesFalse :
        indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
          (binaryBitAtValuationFormula false
            indexTerm valueTerm).freeVariables := by
      rw [binaryBitFalse_freeVariables_eq_true]
      exact hvariablesTrue
    let bitFalse :=
      CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
        valuation indexTerm valueTerm (by
          simpa [valuation, indexTerm, valueTerm, crossTableBitIndexTerm,
            termValue_arithmeticAdd, termValue_arithmeticMul,
            termValue_shortBinaryNumeralTerm] using hbitFalse)
        hvariablesFalse
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := ∼crossTableWidthAtom width) bitFalse
    simpa [crossTableBitCondition, crossTableBitAtom,
      binaryBitAtValuationFormula, binaryBitLiteralAtTerms] using direct
  · let widthFalse := widthFalseCertificate valuation width bitIndex
      hwidth rfl
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := ∼crossTableBitAtom table start width) widthFalse
    simpa [crossTableBitCondition] using direct

private noncomputable def crossTableBitBranchCertificate
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart
      offset bitIndex : Nat)
    (hiff :
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset zeroValuation))
      (crossTableExplicitBitFormula sourceTable sourceWidth sourceStart
        targetTable targetWidth targetStart) := by
  let sourceCondition :=
    crossTableBitCondition sourceTable sourceStart sourceWidth
  let targetCondition :=
    crossTableBitCondition targetTable targetStart targetWidth
  by_cases hsource : bitIndex < sourceWidth ∧
      sourceTable.testBit
        ((sourceStart + offset) * sourceWidth + bitIndex) = true
  · have htarget := hiff.mp hsource
    let sourceTrue := bitConditionTrueCertificate sourceTable sourceStart
      sourceWidth offset bitIndex hsource
    let targetTrue := bitConditionTrueCertificate targetTable targetStart
      targetWidth offset bitIndex htarget
    let forward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := ∼sourceCondition) targetTrue
    let backward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := ∼targetCondition) sourceTrue
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        forward backward
    exact .cast (by
      change ((∼sourceCondition ⋎ targetCondition) ⋏
        (∼targetCondition ⋎ sourceCondition)) = _
      rw [← LO.FirstOrder.Semiformula.iff_eq]
      rfl) direct
  · have htarget : ¬(bitIndex < targetWidth ∧
        targetTable.testBit
          ((targetStart + offset) * targetWidth + bitIndex) = true) :=
      fun htarget => hsource (hiff.mpr htarget)
    let sourceFalse := bitConditionFalseCertificate sourceTable sourceStart
      sourceWidth offset bitIndex hsource
    let targetFalse := bitConditionFalseCertificate targetTable targetStart
      targetWidth offset bitIndex htarget
    let forward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := targetCondition) sourceFalse
    let backward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := sourceCondition) targetFalse
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        forward backward
    exact .cast (by
      change ((∼sourceCondition ⋎ targetCondition) ⋏
        (∼targetCondition ⋎ sourceCondition)) = _
      rw [← LO.FirstOrder.Semiformula.iff_eq]
      rfl) direct

private noncomputable def crossTableBitUniversalCertificate
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart
      offset : Nat)
    (hbits : ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    CrossTableHybridCertificate (extendValuation offset zeroValuation)
      (crossTableBitUniversalFormula sourceTable sourceWidth sourceStart
        targetTable targetWidth targetStart) := by
  let body := crossTableBitBody sourceTable sourceWidth sourceStart targetTable
    targetWidth targetStart
  let branches := buildExplicitHybridUniversalBranches
    (sourceWidth + targetWidth) (fun bitIndex hbitIndex =>
      CheckedHybridValuationBoundedFormulaCertificate.cast
        (crossTableBitBody_free_alignment sourceTable sourceWidth sourceStart
          targetTable targetWidth targetStart).symm
        (crossTableBitBranchCertificate sourceTable sourceWidth sourceStart
          targetTable targetWidth targetStart offset bitIndex
          (hbits bitIndex hbitIndex)))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (crossTableBitBoundTerm sourceWidth targetWidth) body (by
        simpa [crossTableBitBoundTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (crossTableBitBoundTerm sourceWidth targetWidth)) body) =
        crossTableBitUniversalFormula sourceTable sourceWidth sourceStart
          targetTable targetWidth targetStart
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

private noncomputable def crossTableOffsetBranchCertificate
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart
      offset : Nat)
    (hbits : ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    CrossTableHybridCertificate (extendValuation offset zeroValuation)
      (Rewriting.free
        (crossTableOffsetBody sourceTable sourceWidth sourceStart targetTable
          targetWidth targetStart)) := by
  exact .cast
    (crossTableOffsetBody_free_alignment sourceTable sourceWidth sourceStart
      targetTable targetWidth targetStart).symm
    (crossTableBitUniversalCertificate sourceTable sourceWidth sourceStart
      targetTable targetWidth targetStart offset hbits)

private noncomputable def crossTableOffsetUniversalCertificate
    (sourceTable sourceWidth sourceStart targetTable targetWidth targetStart
      count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    CrossTableHybridCertificate zeroValuation
      (crossTableOffsetUniversalFormula sourceTable sourceWidth sourceStart
        targetTable targetWidth targetStart count) := by
  let body := crossTableOffsetBody sourceTable sourceWidth sourceStart
    targetTable targetWidth targetStart
  let branches := buildExplicitHybridUniversalBranches count
    (fun offset hoffset => crossTableOffsetBranchCertificate sourceTable
      sourceWidth sourceStart targetTable targetWidth targetStart offset
      (hbits offset hoffset))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm count) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        crossTableOffsetUniversalFormula sourceTable sourceWidth sourceStart
          targetTable targetWidth targetStart count
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Fully explicit checked hybrid certificate for ten closed coordinates.
The caller supplies the count witness, all six arithmetic facts, and every
offset/bitIndex equivalence used by the two materialized universal layers. -/
noncomputable def compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat)
    (hsourceCountBound : count <= sourceTokenCount)
    (htargetCountBound : count <= targetTokenCount)
    (hsourceEndpoint : sourceFinish = sourceStart + count)
    (htargetEndpoint : targetFinish = targetStart + count)
    (hsourceFinishBound : sourceFinish <= sourceTokenCount)
    (htargetFinishBound : targetFinish <= targetTokenCount)
    (hbits : ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    CrossTableHybridCertificate zeroValuation
      (compactFixedWidthCrossTableSlicesEqClosedFormula sourceTable sourceWidth
        sourceTokenCount sourceStart sourceFinish targetTable targetWidth
        targetTokenCount targetStart targetFinish) := by
  rw [compactFixedWidthCrossTableSlicesEqClosedFormula_alignment]
  refine .existsWitness
    (crossTableWitnessBody sourceTable sourceWidth sourceTokenCount sourceStart
      sourceFinish targetTable targetWidth targetTokenCount targetStart
      targetFinish) count ?_
  let decomposed :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (sourceCountGuardCertificate sourceTokenCount count hsourceCountBound)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (closedLeCertificate count targetTokenCount htargetCountBound)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (closedEndpointCertificate sourceStart sourceFinish count
            hsourceEndpoint)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedEndpointCertificate targetStart targetFinish count
              htargetEndpoint)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (closedLeCertificate sourceFinish sourceTokenCount
                hsourceFinishBound)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (closedLeCertificate targetFinish targetTokenCount
                  htargetFinishBound)
                (crossTableOffsetUniversalCertificate sourceTable sourceWidth
                  sourceStart targetTable targetWidth targetStart count
                  hbits))))))
  exact .cast (by
    rw [crossTableWitnessBody_subst]
    exact (crossTablePostWitnessFormula_alignment sourceTable sourceWidth
      sourceTokenCount sourceStart sourceFinish targetTable targetWidth
      targetTokenCount targetStart targetFinish count).symm) decomposed

/-! ## Arbitrary valuation-term coordinates -/

/-- The quoted cross-table predicate at ten arbitrary valuation terms. -/
def compactFixedWidthCrossTableSlicesEqAtValuationFormula
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFixedWidthCrossTableSlicesEqDef.val) ⇜
    ![sourceTableTerm, sourceWidthTerm, sourceTokenCountTerm, sourceStartTerm,
      sourceFinishTerm, targetTableTerm, targetWidthTerm,
      targetTokenCountTerm, targetStartTerm, targetFinishTerm]

private def crossTableAtValuationWitnessBody
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift sourceTokenCountTerm) + 1 ∧
    #0 ≤ !!(Rew.bShift targetTokenCountTerm) ∧
    !!(Rew.bShift sourceFinishTerm) = !!(Rew.bShift sourceStartTerm) + #0 ∧
    !!(Rew.bShift targetFinishTerm) = !!(Rew.bShift targetStartTerm) + #0 ∧
    !!(Rew.bShift sourceFinishTerm) ≤ !!(Rew.bShift sourceTokenCountTerm) ∧
    !!(Rew.bShift targetFinishTerm) ≤ !!(Rew.bShift targetTokenCountTerm) ∧
    ∀ offset < #0,
      ∀ bitIndex <
          !!(Rew.bShift (Rew.bShift sourceWidthTerm)) +
          !!(Rew.bShift (Rew.bShift targetWidthTerm)),
        ((bitIndex <
              !!(Rew.bShift (Rew.bShift (Rew.bShift sourceWidthTerm))) ∧
            !bitDef
              ((!!(Rew.bShift (Rew.bShift (Rew.bShift sourceStartTerm))) +
                    offset) *
                  !!(Rew.bShift (Rew.bShift (Rew.bShift sourceWidthTerm))) +
                    bitIndex)
              !!(Rew.bShift (Rew.bShift (Rew.bShift sourceTableTerm)))) ↔
          (bitIndex <
              !!(Rew.bShift (Rew.bShift (Rew.bShift targetWidthTerm))) ∧
            !bitDef
              ((!!(Rew.bShift (Rew.bShift (Rew.bShift targetStartTerm))) +
                    offset) *
                  !!(Rew.bShift (Rew.bShift (Rew.bShift targetWidthTerm))) +
                    bitIndex)
              !!(Rew.bShift (Rew.bShift (Rew.bShift targetTableTerm)))))”

private def crossTableAtValuationOuterTerms
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 10 -> ValuationTerm :=
  ![sourceTableTerm, sourceWidthTerm, sourceTokenCountTerm, sourceStartTerm,
    sourceFinishTerm, targetTableTerm, targetWidthTerm, targetTokenCountTerm,
    targetStartTerm, targetFinishTerm]

private def crossTableAtValuationBodyTerms
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 11 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift sourceTableTerm, Rew.bShift sourceWidthTerm,
    Rew.bShift sourceTokenCountTerm, Rew.bShift sourceStartTerm,
    Rew.bShift sourceFinishTerm, Rew.bShift targetTableTerm,
    Rew.bShift targetWidthTerm, Rew.bShift targetTokenCountTerm,
    Rew.bShift targetStartTerm, Rew.bShift targetFinishTerm]

private def crossTableAtValuationOffsetTerms
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 12 -> LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2), #1,
    Rew.bShift (Rew.bShift sourceTableTerm),
    Rew.bShift (Rew.bShift sourceWidthTerm),
    Rew.bShift (Rew.bShift sourceTokenCountTerm),
    Rew.bShift (Rew.bShift sourceStartTerm),
    Rew.bShift (Rew.bShift sourceFinishTerm),
    Rew.bShift (Rew.bShift targetTableTerm),
    Rew.bShift (Rew.bShift targetWidthTerm),
    Rew.bShift (Rew.bShift targetTokenCountTerm),
    Rew.bShift (Rew.bShift targetStartTerm),
    Rew.bShift (Rew.bShift targetFinishTerm)]

private def crossTableAtValuationBitTerms
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 13 -> LO.FirstOrder.ArithmeticSemiterm Nat 3 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3), #1, #2,
    Rew.bShift (Rew.bShift (Rew.bShift sourceTableTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceWidthTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceTokenCountTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceStartTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceFinishTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetTableTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetWidthTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetTokenCountTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetStartTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetFinishTerm))]

private theorem crossTableAtValuationBodyRewriting_eq_embSubsts
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (Rew.subst (crossTableAtValuationOuterTerms sourceTableTerm sourceWidthTerm
      sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
      targetWidthTerm targetTokenCountTerm targetStartTerm targetFinishTerm)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 11 Nat 11) =
      Rew.embSubsts (crossTableAtValuationBodyTerms sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.comp_app, Rew.q_bvar_zero, Rew.embSubsts_bvar,
          crossTableAtValuationBodyTerms]
    | succ coordinate =>
        simp only [Rew.comp_app, Rew.emb_bvar, Rew.q_bvar_succ,
          Rew.embSubsts_bvar]
        rw [Rew.subst_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem crossTableAtValuationBodyRewriting_q_eq_embSubsts
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (Rew.embSubsts (crossTableAtValuationBodyTerms sourceTableTerm
      sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
      targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
      targetFinishTerm)).q =
      Rew.embSubsts (crossTableAtValuationOffsetTerms sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar,
          crossTableAtValuationOffsetTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem crossTableAtValuationBodyRewriting_qq_eq_embSubsts
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (Rew.embSubsts (crossTableAtValuationBodyTerms sourceTableTerm
      sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
      targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
      targetFinishTerm)).q.q =
      Rew.embSubsts (crossTableAtValuationBitTerms sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm) := by
  rw [crossTableAtValuationBodyRewriting_q_eq_embSubsts]
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar,
          crossTableAtValuationBitTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem crossTableSourceBody_rewrite_atValuation
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Rew.embSubsts (crossTableAtValuationBodyTerms sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm) ▹ crossTableSourceBody =
      crossTableAtValuationWitnessBody sourceTableTerm sourceWidthTerm
        sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
        targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm := by
  unfold crossTableSourceBody crossTableSourceTail
    crossTableAtValuationWitnessBody
  simp only [LogicalConnective.HomClass.map_and, rewriting_ballLT]
  rw [crossTableAtValuationBodyRewriting_qq_eq_embSubsts,
    crossTableAtValuationBodyRewriting_q_eq_embSubsts]
  simp [crossTableAtValuationBodyTerms,
    crossTableAtValuationOffsetTerms, crossTableAtValuationBitTerms,
    membershipOperator_eq_binaryBitAtomAtTerms, binaryBitAtomAtTerms]

private theorem compactFixedWidthCrossTableSlicesEqAtValuationFormula_alignment
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    compactFixedWidthCrossTableSlicesEqAtValuationFormula sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm =
      ∃⁰ crossTableAtValuationWitnessBody sourceTableTerm sourceWidthTerm
        sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
        targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm := by
  unfold compactFixedWidthCrossTableSlicesEqAtValuationFormula
  rw [compactFixedWidthCrossTableSlicesEqDef_val_eq_exists]
  change
    Rew.subst (crossTableAtValuationOuterTerms sourceTableTerm sourceWidthTerm
      sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
      targetWidthTerm targetTokenCountTerm targetStartTerm targetFinishTerm) ▹
        (Rewriting.emb (ξ := Nat) (∃⁰ crossTableSourceBody)) = _
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [← TransitiveRewriting.comp_app,
    crossTableAtValuationBodyRewriting_eq_embSubsts,
    crossTableSourceBody_rewrite_atValuation]

private def crossTableAtValuationPostWitnessFormula
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) : ValuationFormula :=
  (Rew.subst ![shortBinaryNumeralTerm count]) ▹
    crossTableAtValuationWitnessBody sourceTableTerm sourceWidthTerm
      sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
      targetWidthTerm targetTokenCountTerm targetStartTerm targetFinishTerm

private def crossTableAtValuationBitBoundTerm
    (sourceWidthTerm targetWidthTerm : ValuationTerm) : ValuationTerm :=
  ‘!!sourceWidthTerm + !!targetWidthTerm’

private def crossTableAtValuationOffsetBitBody
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  “((#0 < !!(Rew.bShift (Rew.bShift sourceWidthTerm)) ∧
        !bitDef
          ((!!(Rew.bShift (Rew.bShift sourceStartTerm)) + #1) *
              !!(Rew.bShift (Rew.bShift sourceWidthTerm)) + #0)
          !!(Rew.bShift (Rew.bShift sourceTableTerm))) ↔
      (#0 < !!(Rew.bShift (Rew.bShift targetWidthTerm)) ∧
        !bitDef
          ((!!(Rew.bShift (Rew.bShift targetStartTerm)) + #1) *
              !!(Rew.bShift (Rew.bShift targetWidthTerm)) + #0)
          !!(Rew.bShift (Rew.bShift targetTableTerm))))”

private def crossTableAtValuationOffsetBody
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (crossTableAtValuationOffsetBitBody sourceTableTerm sourceWidthTerm
    sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm).ballLT
      (Rew.bShift
        (crossTableAtValuationBitBoundTerm sourceWidthTerm targetWidthTerm))

private def crossTableAtValuationBitBody
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “((#0 < !!(Rew.bShift (Rew.shift sourceWidthTerm)) ∧
        !bitDef
          ((!!(Rew.bShift (Rew.shift sourceStartTerm)) +
                !!(Rew.bShift (&0 : ValuationTerm))) *
              !!(Rew.bShift (Rew.shift sourceWidthTerm)) + #0)
          !!(Rew.bShift (Rew.shift sourceTableTerm))) ↔
      (#0 < !!(Rew.bShift (Rew.shift targetWidthTerm)) ∧
        !bitDef
          ((!!(Rew.bShift (Rew.shift targetStartTerm)) +
                !!(Rew.bShift (&0 : ValuationTerm))) *
              !!(Rew.bShift (Rew.shift targetWidthTerm)) + #0)
          !!(Rew.bShift (Rew.shift targetTableTerm))))”

private def crossTableAtValuationBitUniversalFormula
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) : ValuationFormula :=
  (crossTableAtValuationBitBody sourceTableTerm sourceWidthTerm sourceStartTerm
    targetTableTerm targetWidthTerm targetStartTerm).ballLT
      (crossTableAtValuationBitBoundTerm (Rew.shift sourceWidthTerm)
        (Rew.shift targetWidthTerm))

private def crossTableAtValuationOffsetUniversalFormula
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm)
    (count : Nat) : ValuationFormula :=
  (crossTableAtValuationOffsetBody sourceTableTerm sourceWidthTerm
    sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm).ballLT
      (shortBinaryNumeralTerm count)

private def crossTableAtValuationBitIndexTerm
    (startTerm widthTerm : ValuationTerm) : ValuationTerm :=
  ‘(!!(Rew.shift (Rew.shift startTerm)) + &1) *
      !!(Rew.shift (Rew.shift widthTerm)) + &0’

private def crossTableAtValuationWidthAtom
    (widthTerm : ValuationTerm) : ValuationFormula :=
  “&0 < !!(Rew.shift (Rew.shift widthTerm))”

private def crossTableAtValuationBitAtom
    (tableTerm startTerm widthTerm : ValuationTerm) : ValuationFormula :=
  binaryBitAtomAtTerms
    (crossTableAtValuationBitIndexTerm startTerm widthTerm)
    (Rew.shift (Rew.shift tableTerm))

private def crossTableAtValuationBitCondition
    (tableTerm startTerm widthTerm : ValuationTerm) : ValuationFormula :=
  crossTableAtValuationWidthAtom widthTerm ⋏
    crossTableAtValuationBitAtom tableTerm startTerm widthTerm

private def crossTableAtValuationExplicitBitFormula
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) : ValuationFormula :=
  crossTableAtValuationBitCondition sourceTableTerm sourceStartTerm
      sourceWidthTerm 🡘
    crossTableAtValuationBitCondition targetTableTerm targetStartTerm
      targetWidthTerm

private def crossTableAtValuationDecomposedPostWitnessFormula
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm count) < !!sourceTokenCountTerm + 1” ⋏
    (“!!(shortBinaryNumeralTerm count) ≤ !!targetTokenCountTerm” ⋏
      (“!!sourceFinishTerm =
          !!sourceStartTerm + !!(shortBinaryNumeralTerm count)” ⋏
        (“!!targetFinishTerm =
            !!targetStartTerm + !!(shortBinaryNumeralTerm count)” ⋏
          (“!!sourceFinishTerm ≤ !!sourceTokenCountTerm” ⋏
            (“!!targetFinishTerm ≤ !!targetTokenCountTerm” ⋏
              crossTableAtValuationOffsetUniversalFormula sourceTableTerm
                sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
                targetStartTerm count)))))

private theorem free_bShift2_term (term : ValuationTerm) :
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift term)) =
      Rew.bShift (Rew.shift term) := by
  let leftRewriting :=
    ((Rew.free (L := ℒₒᵣ) (n := 1)).comp Rew.bShift).comp Rew.bShift
  let rightRewriting : Rew ℒₒᵣ Nat 0 Nat 1 :=
    (Rew.bShift : Rew ℒₒᵣ Nat 0 Nat 1).comp
      (Rew.shift : Rew ℒₒᵣ Nat 0 Nat 0)
  have hrewrite : leftRewriting = rightRewriting := by
    ext coordinate
    · exact Fin.elim0 coordinate
    · simp [leftRewriting, rightRewriting, Rew.comp_app]
  calc
    (Rew.free (L := ℒₒᵣ) (n := 1))
        (Rew.bShift (Rew.bShift term)) = leftRewriting term := by
      simp [leftRewriting, Rew.comp_app]
    _ = rightRewriting term := by rw [hrewrite]
    _ = Rew.bShift (Rew.shift term) := by
      simp [rightRewriting, Rew.comp_app]

private theorem crossTableAtValuationPostWitnessFormula_alignment
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) :
    crossTableAtValuationPostWitnessFormula sourceTableTerm sourceWidthTerm
        sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
        targetWidthTerm targetTokenCountTerm targetStartTerm targetFinishTerm
        count =
      crossTableAtValuationDecomposedPostWitnessFormula sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm count := by
  simp [crossTableAtValuationPostWitnessFormula,
    crossTableAtValuationWitnessBody,
    crossTableAtValuationDecomposedPostWitnessFormula,
    crossTableAtValuationOffsetUniversalFormula,
    crossTableAtValuationOffsetBody,
    crossTableAtValuationOffsetBitBody,
    crossTableAtValuationBitBoundTerm, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution]

private theorem crossTableAtValuationOffsetBody_free_alignment
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) :
    Rewriting.free (crossTableAtValuationOffsetBody sourceTableTerm
        sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
        targetStartTerm) =
      crossTableAtValuationBitUniversalFormula sourceTableTerm sourceWidthTerm
        sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm := by
  simp [crossTableAtValuationOffsetBody,
    crossTableAtValuationOffsetBitBody,
    crossTableAtValuationBitUniversalFormula,
    crossTableAtValuationBitBody,
    crossTableAtValuationBitBoundTerm, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution, free_bShift2_term,
    free_bvar_one_fin2]

private theorem crossTableAtValuationBitBody_free_alignment
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm) :
    Rewriting.free (crossTableAtValuationBitBody sourceTableTerm
        sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
        targetStartTerm) =
      crossTableAtValuationExplicitBitFormula sourceTableTerm sourceWidthTerm
        sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm := by
  simp [crossTableAtValuationBitBody,
    crossTableAtValuationExplicitBitFormula,
    crossTableAtValuationBitCondition,
    crossTableAtValuationWidthAtom, crossTableAtValuationBitAtom,
    crossTableAtValuationBitIndexTerm,
    rewriting_embeddedFormulaSubstitution,
    binaryBitAtomAtTerms]

private noncomputable def atValuationSourceCountGuardCertificate
    (valuation : Nat -> Nat) (sourceTokenCountTerm : ValuationTerm)
    (count : Nat)
    (hbound : count <= termValue valuation sourceTokenCountTerm) :
    CrossTableHybridCertificate valuation
      “!!(shortBinaryNumeralTerm count) < !!sourceTokenCountTerm + 1” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm count,
        (‘!!sourceTokenCountTerm + 1’ : ValuationTerm)] (by
        change termValue valuation (shortBinaryNumeralTerm count) <
          termValue valuation (‘!!sourceTokenCountTerm + 1’ : ValuationTerm)
        simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using Nat.lt_succ_of_le hbound)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def atValuationLeCertificate
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hle : termValue valuation leftTerm <= termValue valuation rightTerm) :
    CrossTableHybridCertificate valuation “!!leftTerm ≤ !!rightTerm” := by
  if hequal : termValue valuation leftTerm = termValue valuation rightTerm then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        valuation Language.Eq.eq ![leftTerm, rightTerm] hequal
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
          ![leftTerm, rightTerm]) equality
    exact .cast
      (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct
  else
    have hstrict : termValue valuation leftTerm <
        termValue valuation rightTerm := Nat.lt_of_le_of_ne hle hequal
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        valuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hstrict
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := LO.FirstOrder.Semiformula.rel Language.Eq.eq
          ![leftTerm, rightTerm]) strict
    exact .cast
      (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm direct

private noncomputable def atValuationEndpointCertificate
    (valuation : Nat -> Nat) (startTerm finishTerm : ValuationTerm)
    (count : Nat)
    (hendpoint : termValue valuation finishTerm =
      termValue valuation startTerm + count) :
    CrossTableHybridCertificate valuation
      “!!finishTerm = !!startTerm + !!(shortBinaryNumeralTerm count)” := by
  let rightTerm : ValuationTerm :=
    ‘!!startTerm + !!(shortBinaryNumeralTerm count)’
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.Eq.eq ![finishTerm, rightTerm] (by
        change termValue valuation finishTerm = termValue valuation rightTerm
        simpa [rightTerm, termValue_arithmeticAdd,
          termValue_shortBinaryNumeralTerm] using hendpoint)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private noncomputable def atValuationWidthTrueCertificate
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hwidth : bitIndex < termValue valuation widthTerm) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (crossTableAtValuationWidthAtom widthTerm) := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let shiftedWidth := Rew.shift (Rew.shift widthTerm)
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      branchValuation Language.ORing.Rel.lt
      ![(&0 : ValuationTerm), shiftedWidth] (by
        change termValue branchValuation (&0 : ValuationTerm) <
          termValue branchValuation shiftedWidth
        simpa [branchValuation, shiftedWidth, termValue_shift] using hwidth)
  exact .cast (by
    unfold crossTableAtValuationWidthAtom
    exact (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm) direct

private noncomputable def atValuationWidthFalseCertificate
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hwidth : ¬bitIndex < termValue valuation widthTerm) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (∼crossTableAtValuationWidthAtom widthTerm) := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let shiftedWidth := Rew.shift (Rew.shift widthTerm)
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
      branchValuation Language.ORing.Rel.lt
      ![(&0 : ValuationTerm), shiftedWidth] (by
        change ¬termValue branchValuation (&0 : ValuationTerm) <
          termValue branchValuation shiftedWidth
        simpa [branchValuation, shiftedWidth, termValue_shift] using hwidth)
  exact .cast (by
    change
      (∼LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt
        ![(&0 : ValuationTerm), shiftedWidth]) =
        ∼crossTableAtValuationWidthAtom widthTerm
    congr 1) direct

private noncomputable def atValuationBitConditionTrueCertificate
    (valuation : Nat -> Nat)
    (tableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hcondition : bitIndex < termValue valuation widthTerm ∧
      (termValue valuation tableTerm).testBit
        ((termValue valuation startTerm + offset) *
          termValue valuation widthTerm + bitIndex) = true) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (crossTableAtValuationBitCondition tableTerm startTerm widthTerm) := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let indexTerm := crossTableAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
  let widthCertificate := atValuationWidthTrueCertificate valuation widthTerm
    offset bitIndex hcondition.1
  have hvariables :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          indexTerm valueTerm).freeVariables :=
    binaryBitHybridVariablesTrue indexTerm valueTerm
  let bitCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
      branchValuation indexTerm valueTerm (by
        simpa [branchValuation, indexTerm, valueTerm,
          crossTableAtValuationBitIndexTerm, termValue_arithmeticAdd,
          termValue_arithmeticMul, termValue_shift] using hcondition.2)
      hvariables
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    widthCertificate bitCertificate

private noncomputable def atValuationBitConditionFalseCertificate
    (valuation : Nat -> Nat)
    (tableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hcondition : ¬(bitIndex < termValue valuation widthTerm ∧
      (termValue valuation tableTerm).testBit
        ((termValue valuation startTerm + offset) *
          termValue valuation widthTerm + bitIndex) = true)) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (∼crossTableAtValuationBitCondition tableTerm startTerm widthTerm) := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let indexTerm := crossTableAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
  by_cases hwidth : bitIndex < termValue valuation widthTerm
  · have hbitFalse :
        (termValue valuation tableTerm).testBit
            ((termValue valuation startTerm + offset) *
              termValue valuation widthTerm + bitIndex) = false := by
      cases hbit : (termValue valuation tableTerm).testBit
          ((termValue valuation startTerm + offset) *
            termValue valuation widthTerm + bitIndex) with
      | false => rfl
      | true => exact False.elim (hcondition ⟨hwidth, hbit⟩)
    have hvariablesTrue :
        indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
          (binaryBitAtValuationFormula true
            indexTerm valueTerm).freeVariables :=
      binaryBitHybridVariablesTrue indexTerm valueTerm
    have hvariablesFalse :
        indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
          (binaryBitAtValuationFormula false
            indexTerm valueTerm).freeVariables := by
      rw [binaryBitFalse_freeVariables_eq_true]
      exact hvariablesTrue
    let bitFalse :=
      CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
        branchValuation indexTerm valueTerm (by
          simpa [branchValuation, indexTerm, valueTerm,
            crossTableAtValuationBitIndexTerm, termValue_arithmeticAdd,
            termValue_arithmeticMul, termValue_shift] using hbitFalse)
        hvariablesFalse
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := ∼crossTableAtValuationWidthAtom widthTerm) bitFalse
    simpa [crossTableAtValuationBitCondition,
      crossTableAtValuationBitAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms] using direct
  · let widthFalse := atValuationWidthFalseCertificate valuation widthTerm
      offset bitIndex hwidth
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := ∼crossTableAtValuationBitAtom tableTerm startTerm widthTerm)
        widthFalse
    simpa [crossTableAtValuationBitCondition] using direct

private noncomputable def crossTableAtValuationBitBranchCertificate
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hiff :
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    CrossTableHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (crossTableAtValuationExplicitBitFormula sourceTableTerm sourceWidthTerm
        sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm) := by
  let sourceCondition := crossTableAtValuationBitCondition sourceTableTerm
    sourceStartTerm sourceWidthTerm
  let targetCondition := crossTableAtValuationBitCondition targetTableTerm
    targetStartTerm targetWidthTerm
  by_cases hsource : bitIndex < termValue valuation sourceWidthTerm ∧
      (termValue valuation sourceTableTerm).testBit
        ((termValue valuation sourceStartTerm + offset) *
          termValue valuation sourceWidthTerm + bitIndex) = true
  · have htarget := hiff.mp hsource
    let sourceTrue := atValuationBitConditionTrueCertificate valuation
      sourceTableTerm sourceStartTerm sourceWidthTerm offset bitIndex hsource
    let targetTrue := atValuationBitConditionTrueCertificate valuation
      targetTableTerm targetStartTerm targetWidthTerm offset bitIndex htarget
    let forward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := ∼sourceCondition) targetTrue
    let backward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := ∼targetCondition) sourceTrue
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        forward backward
    exact .cast (by
      change ((∼sourceCondition ⋎ targetCondition) ⋏
        (∼targetCondition ⋎ sourceCondition)) = _
      rw [← LO.FirstOrder.Semiformula.iff_eq]
      rfl) direct
  · have htarget : ¬(bitIndex < termValue valuation targetWidthTerm ∧
        (termValue valuation targetTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation targetWidthTerm + bitIndex) = true) :=
      fun htarget => hsource (hiff.mpr htarget)
    let sourceFalse := atValuationBitConditionFalseCertificate valuation
      sourceTableTerm sourceStartTerm sourceWidthTerm offset bitIndex hsource
    let targetFalse := atValuationBitConditionFalseCertificate valuation
      targetTableTerm targetStartTerm targetWidthTerm offset bitIndex htarget
    let forward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := targetCondition) sourceFalse
    let backward :=
      CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := sourceCondition) targetFalse
    let direct :=
      CheckedHybridValuationBoundedFormulaCertificate.conjunction
        forward backward
    exact .cast (by
      change ((∼sourceCondition ⋎ targetCondition) ⋏
        (∼targetCondition ⋎ sourceCondition)) = _
      rw [← LO.FirstOrder.Semiformula.iff_eq]
      rfl) direct

private noncomputable def crossTableAtValuationBitUniversalCertificate
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    CrossTableHybridCertificate (extendValuation offset valuation)
      (crossTableAtValuationBitUniversalFormula sourceTableTerm
        sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
        targetStartTerm) := by
  let body := crossTableAtValuationBitBody sourceTableTerm sourceWidthTerm
    sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm
  let bound := termValue valuation sourceWidthTerm +
    termValue valuation targetWidthTerm
  let branches := buildExplicitHybridUniversalBranches bound
    (fun bitIndex hbitIndex =>
      CheckedHybridValuationBoundedFormulaCertificate.cast
        (crossTableAtValuationBitBody_free_alignment sourceTableTerm
          sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
          targetStartTerm).symm
        (crossTableAtValuationBitBranchCertificate valuation sourceTableTerm
          sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
          targetStartTerm offset bitIndex (hbits bitIndex hbitIndex)))
  let boundTerm := crossTableAtValuationBitBoundTerm
    (Rew.shift sourceWidthTerm) (Rew.shift targetWidthTerm)
  let normalizedBranches :
      CheckedHybridValuationUniversalBranches
        (extendValuation offset valuation) body
        (termValue (extendValuation offset valuation) boundTerm) := by
    simpa [bound, boundTerm, crossTableAtValuationBitBoundTerm,
      termValue_arithmeticAdd, termValue_shift] using branches
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      boundTerm body normalizedBranches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift boundTerm) body) =
      crossTableAtValuationBitUniversalFormula sourceTableTerm
        sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
        targetStartTerm
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

private noncomputable def crossTableAtValuationOffsetBranchCertificate
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    CrossTableHybridCertificate (extendValuation offset valuation)
      (Rewriting.free (crossTableAtValuationOffsetBody sourceTableTerm
        sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
        targetStartTerm)) := by
  exact .cast
    (crossTableAtValuationOffsetBody_free_alignment sourceTableTerm
      sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
      targetStartTerm).symm
    (crossTableAtValuationBitUniversalCertificate valuation sourceTableTerm
      sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
      targetStartTerm offset hbits)

private noncomputable def crossTableAtValuationOffsetUniversalCertificate
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm : ValuationTerm)
    (count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    CrossTableHybridCertificate valuation
      (crossTableAtValuationOffsetUniversalFormula sourceTableTerm
        sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
        targetStartTerm count) := by
  let body := crossTableAtValuationOffsetBody sourceTableTerm sourceWidthTerm
    sourceStartTerm targetTableTerm targetWidthTerm targetStartTerm
  let branches := buildExplicitHybridUniversalBranches count
    (fun offset hoffset => crossTableAtValuationOffsetBranchCertificate
      valuation sourceTableTerm sourceWidthTerm sourceStartTerm targetTableTerm
      targetWidthTerm targetStartTerm offset (hbits offset hoffset))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm count) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        crossTableAtValuationOffsetUniversalFormula sourceTableTerm
          sourceWidthTerm sourceStartTerm targetTableTerm targetWidthTerm
          targetStartTerm count
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Explicit checked hybrid certificate at ten original valuation terms.
In particular, callers may pass terms such as `proofStart + 1` directly;
the target formula retains those terms syntactically. -/
noncomputable def
    compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hsourceCountBound : count <=
      termValue valuation sourceTokenCountTerm)
    (htargetCountBound : count <=
      termValue valuation targetTokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation sourceTokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation targetTokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    CrossTableHybridCertificate valuation
      (compactFixedWidthCrossTableSlicesEqAtValuationFormula sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm) := by
  rw [compactFixedWidthCrossTableSlicesEqAtValuationFormula_alignment]
  refine .existsWitness
    (crossTableAtValuationWitnessBody sourceTableTerm sourceWidthTerm
      sourceTokenCountTerm sourceStartTerm sourceFinishTerm targetTableTerm
      targetWidthTerm targetTokenCountTerm targetStartTerm targetFinishTerm)
    count ?_
  let decomposed :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (atValuationSourceCountGuardCertificate valuation sourceTokenCountTerm
        count hsourceCountBound)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (atValuationLeCertificate valuation (shortBinaryNumeralTerm count)
          targetTokenCountTerm (by
            simpa [termValue_shortBinaryNumeralTerm] using htargetCountBound))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (atValuationEndpointCertificate valuation sourceStartTerm
            sourceFinishTerm count hsourceEndpoint)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (atValuationEndpointCertificate valuation targetStartTerm
              targetFinishTerm count htargetEndpoint)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (atValuationLeCertificate valuation sourceFinishTerm
                sourceTokenCountTerm hsourceFinishBound)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (atValuationLeCertificate valuation targetFinishTerm
                  targetTokenCountTerm htargetFinishBound)
                (crossTableAtValuationOffsetUniversalCertificate valuation
                  sourceTableTerm sourceWidthTerm sourceStartTerm
                  targetTableTerm targetWidthTerm targetStartTerm count
                  hbits))))))
  exact .cast
    (crossTableAtValuationPostWitnessFormula_alignment sourceTableTerm
      sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
      targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
      targetFinishTerm count).symm decomposed

theorem compactFixedWidthCrossTableSlicesEqClosedFormula_freeVariables_eq_empty
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish : Nat) :
    (compactFixedWidthCrossTableSlicesEqClosedFormula sourceTable sourceWidth
      sourceTokenCount sourceStart sourceFinish targetTable targetWidth
      targetTokenCount targetStart targetFinish).freeVariables = ∅ := by
  unfold compactFixedWidthCrossTableSlicesEqClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

/-- Empty-context checked PA derivation compiled from the closed explicit
certificate. -/
noncomputable def compileCompactFixedWidthCrossTableSlicesEqExplicitHybridContext
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat)
    (hsourceCountBound : count <= sourceTokenCount)
    (htargetCountBound : count <= targetTokenCount)
    (hsourceEndpoint : sourceFinish = sourceStart + count)
    (htargetEndpoint : targetFinish = targetStart + count)
    (hsourceFinishBound : sourceFinish <= sourceTokenCount)
    (htargetFinishBound : targetFinish <= targetTokenCount)
    (hbits : ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    CertifiedPAContextProof ∅
      (compactFixedWidthCrossTableSlicesEqClosedFormula sourceTable sourceWidth
        sourceTokenCount sourceStart sourceFinish targetTable targetWidth
        targetTokenCount targetStart targetFinish) := by
  let formula := compactFixedWidthCrossTableSlicesEqClosedFormula sourceTable
    sourceWidth sourceTokenCount sourceStart sourceFinish targetTable
    targetWidth targetTokenCount targetStart targetFinish
  let raw :=
    (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate sourceTable
      sourceWidth sourceTokenCount sourceStart sourceFinish targetTable
      targetWidth targetTokenCount targetStart targetFinish count
      hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
      hsourceFinishBound htargetFinishBound hbits).compile
  have hcontext : valuationContext formula.freeVariables zeroValuation = ∅ := by
    rw [compactFixedWidthCrossTableSlicesEqClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Proof-free recursive structural resource for the complete closed hybrid
certificate. -/
noncomputable def compactFixedWidthCrossTableSlicesEqExplicitHybridStructuralResource
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat)
    (hsourceCountBound : count <= sourceTokenCount)
    (htargetCountBound : count <= targetTokenCount)
    (hsourceEndpoint : sourceFinish = sourceStart + count)
    (htargetEndpoint : targetFinish = targetStart + count)
    (hsourceFinishBound : sourceFinish <= sourceTokenCount)
    (htargetFinishBound : targetFinish <= targetTokenCount)
    (hbits : ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate sourceTable
      sourceWidth sourceTokenCount sourceStart sourceFinish targetTable
      targetWidth targetTokenCount targetStart targetFinish count
      hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
      hsourceFinishBound htargetFinishBound hbits)

theorem compileCompactFixedWidthCrossTableSlicesEqExplicitHybridContext_payloadLength_le
    (sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish
      count : Nat)
    (hsourceCountBound : count <= sourceTokenCount)
    (htargetCountBound : count <= targetTokenCount)
    (hsourceEndpoint : sourceFinish = sourceStart + count)
    (htargetEndpoint : targetFinish = targetStart + count)
    (hsourceFinishBound : sourceFinish <= sourceTokenCount)
    (htargetFinishBound : targetFinish <= targetTokenCount)
    (hbits : ∀ offset < count, ∀ bitIndex < sourceWidth + targetWidth,
      (bitIndex < sourceWidth ∧
          sourceTable.testBit
            ((sourceStart + offset) * sourceWidth + bitIndex) = true) ↔
        (bitIndex < targetWidth ∧
          targetTable.testBit
            ((targetStart + offset) * targetWidth + bitIndex) = true)) :
    (compileCompactFixedWidthCrossTableSlicesEqExplicitHybridContext
      sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
      targetTable targetWidth targetTokenCount targetStart targetFinish count
      hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
      hsourceFinishBound htargetFinishBound hbits).payloadLength <=
      compactFixedWidthCrossTableSlicesEqExplicitHybridStructuralResource
        sourceTable sourceWidth sourceTokenCount sourceStart sourceFinish
        targetTable targetWidth targetTokenCount targetStart targetFinish count
        hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
        hsourceFinishBound htargetFinishBound hbits := by
  unfold compileCompactFixedWidthCrossTableSlicesEqExplicitHybridContext
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate sourceTable
        sourceWidth sourceTokenCount sourceStart sourceFinish targetTable
        targetWidth targetTokenCount targetStart targetFinish count
        hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
        hsourceFinishBound htargetFinishBound hbits)

/-- Checked compilation in the exact context induced by the ten original
valuation terms. -/
noncomputable def
    compileCompactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridContext
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hsourceCountBound : count <=
      termValue valuation sourceTokenCountTerm)
    (htargetCountBound : count <=
      termValue valuation targetTokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation sourceTokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation targetTokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    CertifiedPAContextProof
      (valuationContext
        (compactFixedWidthCrossTableSlicesEqAtValuationFormula sourceTableTerm
          sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
          targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
          targetFinishTerm).freeVariables valuation)
      (compactFixedWidthCrossTableSlicesEqAtValuationFormula sourceTableTerm
        sourceWidthTerm sourceTokenCountTerm sourceStartTerm sourceFinishTerm
        targetTableTerm targetWidthTerm targetTokenCountTerm targetStartTerm
        targetFinishTerm) :=
  (compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
    valuation sourceTableTerm sourceWidthTerm sourceTokenCountTerm
    sourceStartTerm sourceFinishTerm targetTableTerm targetWidthTerm
    targetTokenCountTerm targetStartTerm targetFinishTerm count
    hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
    hsourceFinishBound htargetFinishBound hbits).compile

/-- Proof-free recursive structural resource for the AtValuation
certificate. -/
noncomputable def
    compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridStructuralResource
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hsourceCountBound : count <=
      termValue valuation sourceTokenCountTerm)
    (htargetCountBound : count <=
      termValue valuation targetTokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation sourceTokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation targetTokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
      valuation sourceTableTerm sourceWidthTerm sourceTokenCountTerm
      sourceStartTerm sourceFinishTerm targetTableTerm targetWidthTerm
      targetTokenCountTerm targetStartTerm targetFinishTerm count
      hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
      hsourceFinishBound htargetFinishBound hbits)

theorem
    compileCompactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridContext_payloadLength_le
    (valuation : Nat -> Nat)
    (sourceTableTerm sourceWidthTerm sourceTokenCountTerm sourceStartTerm
      sourceFinishTerm targetTableTerm targetWidthTerm targetTokenCountTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hsourceCountBound : count <=
      termValue valuation sourceTokenCountTerm)
    (htargetCountBound : count <=
      termValue valuation targetTokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation sourceTokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation targetTokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex <
        termValue valuation sourceWidthTerm +
          termValue valuation targetWidthTerm,
      (bitIndex < termValue valuation sourceWidthTerm ∧
          (termValue valuation sourceTableTerm).testBit
            ((termValue valuation sourceStartTerm + offset) *
              termValue valuation sourceWidthTerm + bitIndex) = true) ↔
        (bitIndex < termValue valuation targetWidthTerm ∧
          (termValue valuation targetTableTerm).testBit
            ((termValue valuation targetStartTerm + offset) *
              termValue valuation targetWidthTerm + bitIndex) = true)) :
    (compileCompactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridContext
      valuation sourceTableTerm sourceWidthTerm sourceTokenCountTerm
      sourceStartTerm sourceFinishTerm targetTableTerm targetWidthTerm
      targetTokenCountTerm targetStartTerm targetFinishTerm count
      hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
      hsourceFinishBound htargetFinishBound hbits).payloadLength <=
      compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridStructuralResource
        valuation sourceTableTerm sourceWidthTerm sourceTokenCountTerm
        sourceStartTerm sourceFinishTerm targetTableTerm targetWidthTerm
        targetTokenCountTerm targetStartTerm targetFinishTerm count
        hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
        hsourceFinishBound htargetFinishBound hbits := by
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
        valuation sourceTableTerm sourceWidthTerm sourceTokenCountTerm
        sourceStartTerm sourceFinishTerm targetTableTerm targetWidthTerm
        targetTokenCountTerm targetStartTerm targetFinishTerm count
        hsourceCountBound htargetCountBound hsourceEndpoint htargetEndpoint
        hsourceFinishBound htargetFinishBound hbits)

#print axioms compactFixedWidthCrossTableSlicesEqClosedFormula_freeVariables_eq_empty
#print axioms compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate
#print axioms compileCompactFixedWidthCrossTableSlicesEqExplicitHybridContext
#print axioms compileCompactFixedWidthCrossTableSlicesEqExplicitHybridContext_payloadLength_le
#print axioms compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
#print axioms compileCompactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridContext
#print axioms compileCompactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
