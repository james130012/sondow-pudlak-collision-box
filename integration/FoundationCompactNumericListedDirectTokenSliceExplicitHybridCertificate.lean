import integration.FoundationCompactNumericListedDirectTokenSliceEquality
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for token slice equality

The two bounded universal layers are materialized branch by branch. The
constructor below receives the count witness and every arithmetic and bit
fact explicitly; it does not recover certificate data from semantic truth.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate

open FoundationCompactNumericListedDirectTokenSliceEquality
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

/-- The seven-coordinate closed instance of the quoted token-slice predicate. -/
def compactFixedWidthTokenSlicesEqClosedFormula
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) compactFixedWidthTokenSlicesEqDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceStart,
      shortBinaryNumeralTerm sourceFinish, shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm targetFinish]

private def tokenSliceWitnessBody
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1 ∧
    !!(Rew.bShift (shortBinaryNumeralTerm sourceFinish)) =
      !!(Rew.bShift (shortBinaryNumeralTerm sourceStart)) + #0 ∧
    !!(Rew.bShift (shortBinaryNumeralTerm targetFinish)) =
      !!(Rew.bShift (shortBinaryNumeralTerm targetStart)) + #0 ∧
    !!(Rew.bShift (shortBinaryNumeralTerm sourceFinish)) ≤
      !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) ∧
    !!(Rew.bShift (shortBinaryNumeralTerm targetFinish)) ≤
      !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) ∧
    ∀ offset < #0,
      ∀ bitIndex <
          !!(Rew.bShift (Rew.bShift (shortBinaryNumeralTerm width))),
        (!bitDef
            ((!!(Rew.bShift (Rew.bShift (Rew.bShift
                  (shortBinaryNumeralTerm sourceStart)))) + offset) *
                !!(Rew.bShift (Rew.bShift (Rew.bShift
                  (shortBinaryNumeralTerm width)))) + bitIndex)
            !!(Rew.bShift (Rew.bShift (Rew.bShift
              (shortBinaryNumeralTerm tokenTable)))) ↔
          !bitDef
            ((!!(Rew.bShift (Rew.bShift (Rew.bShift
                  (shortBinaryNumeralTerm targetStart)))) + offset) *
                !!(Rew.bShift (Rew.bShift (Rew.bShift
                  (shortBinaryNumeralTerm width)))) + bitIndex)
            !!(Rew.bShift (Rew.bShift (Rew.bShift
              (shortBinaryNumeralTerm tokenTable)))))”

private def tokenSlicePostWitnessFormula
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish count : Nat) : ArithmeticProposition :=
  (Rew.subst ![shortBinaryNumeralTerm count]) ▹
    tokenSliceWitnessBody tokenTable width tokenCount sourceStart sourceFinish
      targetStart targetFinish

private theorem tokenSliceWitnessBody_subst
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish count : Nat) :
    (tokenSliceWitnessBody tokenTable width tokenCount sourceStart sourceFinish
      targetStart targetFinish)/[shortBinaryNumeralTerm count] =
      tokenSlicePostWitnessFormula tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish count := by
  rfl

private def tokenSliceSourceTail :
    LO.FirstOrder.ArithmeticSemiformula Empty 8 :=
  “#5 = #4 + #0 ∧
    #7 = #6 + #0 ∧
    #5 ≤ #3 ∧
    #7 ≤ #3 ∧
    ∀ offset < #0,
      ∀ bitIndex < #3,
        (((#6 + offset) * #4 + bitIndex) ∈ #3 ↔
          ((#8 + offset) * #4 + bitIndex) ∈ #3)”

private def tokenSliceSourceBody :
    LO.FirstOrder.ArithmeticSemiformula Empty 8 :=
  “#0 < #3 + 1” ⋏ tokenSliceSourceTail

private theorem bShift_tokenSliceSourceCountBound :
    Rew.bShift
        (‘#2 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
      (‘#3 + 1’ : LO.FirstOrder.ArithmeticSemiterm Empty 8) := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    LO.FirstOrder.Semiterm.Operator.One.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem compactFixedWidthTokenSlicesEqDef_val_eq_exists :
    compactFixedWidthTokenSlicesEqDef.val = ∃⁰ tokenSliceSourceBody := by
  unfold compactFixedWidthTokenSlicesEqDef
  change tokenSliceSourceTail.bexsLTSucc
      (#2 : LO.FirstOrder.ArithmeticSemiterm Empty 7) =
    ∃⁰ tokenSliceSourceBody
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
    LO.FirstOrder.Semiformula.bexsLT tokenSliceSourceBody
  rw [bShift_tokenSliceSourceCountBound]
  rfl

private def tokenSliceOuterTerms
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) : Fin 7 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable, shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount, shortBinaryNumeralTerm sourceStart,
    shortBinaryNumeralTerm sourceFinish, shortBinaryNumeralTerm targetStart,
    shortBinaryNumeralTerm targetFinish]

private def tokenSliceBodyTerms
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    Fin 8 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift (shortBinaryNumeralTerm tokenTable),
    Rew.bShift (shortBinaryNumeralTerm width),
    Rew.bShift (shortBinaryNumeralTerm tokenCount),
    Rew.bShift (shortBinaryNumeralTerm sourceStart),
    Rew.bShift (shortBinaryNumeralTerm sourceFinish),
    Rew.bShift (shortBinaryNumeralTerm targetStart),
    Rew.bShift (shortBinaryNumeralTerm targetFinish)]

private def tokenSliceOffsetTerms
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    Fin 9 -> LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2), #1,
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm tokenTable)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm width)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm tokenCount)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceStart)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm sourceFinish)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetStart)),
    Rew.bShift (Rew.bShift (shortBinaryNumeralTerm targetFinish))]

private def tokenSliceBitTerms
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    Fin 10 -> LO.FirstOrder.ArithmeticSemiterm Nat 3 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3), #1, #2,
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm tokenTable))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm width))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm tokenCount))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceStart))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm sourceFinish))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetStart))),
    Rew.bShift (Rew.bShift (Rew.bShift
      (shortBinaryNumeralTerm targetFinish)))]

private theorem tokenSliceBodyRewriting_eq_embSubsts
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    (Rew.subst (tokenSliceOuterTerms tokenTable width tokenCount sourceStart
      sourceFinish targetStart targetFinish)).q.comp
        (Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) =
      Rew.embSubsts (tokenSliceBodyTerms tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.comp_app, Rew.q_bvar_zero, Rew.embSubsts_bvar,
          tokenSliceBodyTerms]
    | succ coordinate =>
        simp only [Rew.comp_app, Rew.emb_bvar, Rew.q_bvar_succ,
          Rew.embSubsts_bvar]
        rw [Rew.subst_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem tokenSliceBodyRewriting_q_eq_embSubsts
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    (Rew.embSubsts (tokenSliceBodyTerms tokenTable width tokenCount sourceStart
      sourceFinish targetStart targetFinish)).q =
      Rew.embSubsts (tokenSliceOffsetTerms tokenTable width tokenCount
        sourceStart sourceFinish targetStart targetFinish) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar, tokenSliceOffsetTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem tokenSliceBodyRewriting_qq_eq_embSubsts
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    (Rew.embSubsts (tokenSliceBodyTerms tokenTable width tokenCount sourceStart
      sourceFinish targetStart targetFinish)).q.q =
      Rew.embSubsts (tokenSliceBitTerms tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish) := by
  rw [tokenSliceBodyRewriting_q_eq_embSubsts]
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar, tokenSliceBitTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem tokenSliceSourceBody_rewrite
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    Rew.embSubsts (tokenSliceBodyTerms tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish) ▹ tokenSliceSourceBody =
      tokenSliceWitnessBody tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish := by
  unfold tokenSliceSourceBody tokenSliceSourceTail tokenSliceWitnessBody
  simp only [LogicalConnective.HomClass.map_and, rewriting_ballLT]
  rw [tokenSliceBodyRewriting_qq_eq_embSubsts,
    tokenSliceBodyRewriting_q_eq_embSubsts]
  simp [tokenSliceBodyTerms, tokenSliceOffsetTerms, tokenSliceBitTerms,
    membershipOperator_eq_binaryBitAtomAtTerms, binaryBitAtomAtTerms]

theorem compactFixedWidthTokenSlicesEqClosedFormula_alignment
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish : Nat) :
    compactFixedWidthTokenSlicesEqClosedFormula tokenTable width tokenCount
        sourceStart sourceFinish targetStart targetFinish =
      ∃⁰ tokenSliceWitnessBody tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish := by
  unfold compactFixedWidthTokenSlicesEqClosedFormula
  rw [compactFixedWidthTokenSlicesEqDef_val_eq_exists]
  change
    Rew.subst (tokenSliceOuterTerms tokenTable width tokenCount sourceStart
      sourceFinish targetStart targetFinish) ▹
        (Rewriting.emb (ξ := Nat) (∃⁰ tokenSliceSourceBody)) = _
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [← TransitiveRewriting.comp_app,
    tokenSliceBodyRewriting_eq_embSubsts, tokenSliceSourceBody_rewrite]

private def tokenSliceOffsetBitBody
    (tokenTable width sourceStart targetStart : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  “(!bitDef
        ((!!(Rew.bShift (Rew.bShift
              (shortBinaryNumeralTerm sourceStart))) + #1) *
            !!(Rew.bShift (Rew.bShift
              (shortBinaryNumeralTerm width))) + #0)
        !!(Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm tokenTable))) ↔
      !bitDef
        ((!!(Rew.bShift (Rew.bShift
              (shortBinaryNumeralTerm targetStart))) + #1) *
            !!(Rew.bShift (Rew.bShift
              (shortBinaryNumeralTerm width))) + #0)
        !!(Rew.bShift (Rew.bShift
          (shortBinaryNumeralTerm tokenTable))))”

private def tokenSliceOffsetBody
    (tokenTable width sourceStart targetStart : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (tokenSliceOffsetBitBody tokenTable width sourceStart targetStart).ballLT
    (Rew.bShift (shortBinaryNumeralTerm width))

private def tokenSliceBitBody
    (tokenTable width sourceStart targetStart : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “(!bitDef
        ((!!(Rew.bShift (shortBinaryNumeralTerm sourceStart)) +
              !!(Rew.bShift (&0 : ValuationTerm))) *
            !!(Rew.bShift (shortBinaryNumeralTerm width)) + #0)
        !!(Rew.bShift (shortBinaryNumeralTerm tokenTable)) ↔
      !bitDef
        ((!!(Rew.bShift (shortBinaryNumeralTerm targetStart)) +
              !!(Rew.bShift (&0 : ValuationTerm))) *
            !!(Rew.bShift (shortBinaryNumeralTerm width)) + #0)
        !!(Rew.bShift (shortBinaryNumeralTerm tokenTable)))”

private def tokenSliceBitUniversalFormula
    (tokenTable width sourceStart targetStart : Nat) : ValuationFormula :=
  (tokenSliceBitBody tokenTable width sourceStart targetStart).ballLT
    (shortBinaryNumeralTerm width)

private def tokenSliceOffsetUniversalFormula
    (tokenTable width sourceStart targetStart count : Nat) :
    ArithmeticProposition :=
  (tokenSliceOffsetBody tokenTable width sourceStart targetStart).ballLT
    (shortBinaryNumeralTerm count)

private def tokenSliceBitIndexTerm
    (start width : Nat) : ValuationTerm :=
  ‘(!!(shortBinaryNumeralTerm start) + &1) *
      !!(shortBinaryNumeralTerm width) + &0’

private def tokenSliceBitAtom
    (table start width : Nat) : ValuationFormula :=
  binaryBitAtomAtTerms (tokenSliceBitIndexTerm start width)
    (shortBinaryNumeralTerm table)

private def tokenSliceExplicitBitFormula
    (tokenTable width sourceStart targetStart : Nat) : ValuationFormula :=
  tokenSliceBitAtom tokenTable sourceStart width 🡘
    tokenSliceBitAtom tokenTable targetStart width

private def tokenSliceDecomposedPostWitnessFormula
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish count : Nat) : ArithmeticProposition :=
  “!!(shortBinaryNumeralTerm count) <
      !!(shortBinaryNumeralTerm tokenCount) + 1” ⋏
    (“!!(shortBinaryNumeralTerm sourceFinish) =
        !!(shortBinaryNumeralTerm sourceStart) +
          !!(shortBinaryNumeralTerm count)” ⋏
      (“!!(shortBinaryNumeralTerm targetFinish) =
          !!(shortBinaryNumeralTerm targetStart) +
            !!(shortBinaryNumeralTerm count)” ⋏
        (“!!(shortBinaryNumeralTerm sourceFinish) ≤
            !!(shortBinaryNumeralTerm tokenCount)” ⋏
          (“!!(shortBinaryNumeralTerm targetFinish) ≤
              !!(shortBinaryNumeralTerm tokenCount)” ⋏
            tokenSliceOffsetUniversalFormula tokenTable width sourceStart
              targetStart count))))

private theorem tokenSlicePostWitnessFormula_alignment
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish count : Nat) :
    tokenSlicePostWitnessFormula tokenTable width tokenCount sourceStart
        sourceFinish targetStart targetFinish count =
      tokenSliceDecomposedPostWitnessFormula tokenTable width tokenCount
        sourceStart sourceFinish targetStart targetFinish count := by
  simp [tokenSlicePostWitnessFormula, tokenSliceWitnessBody,
    tokenSliceDecomposedPostWitnessFormula,
    tokenSliceOffsetUniversalFormula, tokenSliceOffsetBody,
    tokenSliceOffsetBitBody, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution]

private theorem tokenSliceOffsetBody_free_alignment
    (tokenTable width sourceStart targetStart : Nat) :
    Rewriting.free
        (tokenSliceOffsetBody tokenTable width sourceStart targetStart) =
      tokenSliceBitUniversalFormula tokenTable width sourceStart
        targetStart := by
  simp [tokenSliceOffsetBody, tokenSliceOffsetBitBody,
    tokenSliceBitUniversalFormula, tokenSliceBitBody, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution,
    free_bShift2_shortBinaryNumeralTerm, free_bvar_one_fin2,
    shift_shortBinaryNumeralTerm]

private theorem tokenSliceBitBody_free_alignment
    (tokenTable width sourceStart targetStart : Nat) :
    Rewriting.free
        (tokenSliceBitBody tokenTable width sourceStart targetStart) =
      tokenSliceExplicitBitFormula tokenTable width sourceStart
        targetStart := by
  simp [tokenSliceBitBody, tokenSliceExplicitBitFormula,
    tokenSliceBitAtom, tokenSliceBitIndexTerm,
    rewriting_embeddedFormulaSubstitution,
    shift_shortBinaryNumeralTerm, binaryBitAtomAtTerms]

abbrev TokenSliceHybridCertificate
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

private noncomputable def countGuardCertificate
    (tokenCount count : Nat) (hbound : count <= tokenCount) :
    TokenSliceHybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm count) <
        !!(shortBinaryNumeralTerm tokenCount) + 1” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm count,
        (‘!!(shortBinaryNumeralTerm tokenCount) + 1’ : ValuationTerm)] (by
        change termValue zeroValuation (shortBinaryNumeralTerm count) <
          termValue zeroValuation
            (‘!!(shortBinaryNumeralTerm tokenCount) + 1’ : ValuationTerm)
        simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using Nat.lt_succ_of_le hbound)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left <= right) :
    TokenSliceHybridCertificate zeroValuation
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
    TokenSliceHybridCertificate zeroValuation
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

private noncomputable def bitAtomTrueCertificate
    (table start width offset bitIndex : Nat)
    (hbit : table.testBit
      ((start + offset) * width + bitIndex) = true) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset zeroValuation))
      (tokenSliceBitAtom table start width) := by
  let valuation :=
    extendValuation bitIndex (extendValuation offset zeroValuation)
  let indexTerm := tokenSliceBitIndexTerm start width
  let valueTerm : ValuationTerm := shortBinaryNumeralTerm table
  have hvariables :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          indexTerm valueTerm).freeVariables :=
    binaryBitHybridVariablesTrue indexTerm valueTerm
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
      valuation indexTerm valueTerm (by
        simpa [valuation, indexTerm, valueTerm, tokenSliceBitIndexTerm,
          termValue_arithmeticAdd, termValue_arithmeticMul,
          termValue_shortBinaryNumeralTerm] using hbit) hvariables
  simpa [tokenSliceBitAtom, binaryBitAtValuationFormula,
    binaryBitLiteralAtTerms] using direct

private noncomputable def bitAtomFalseCertificate
    (table start width offset bitIndex : Nat)
    (hbit : table.testBit
      ((start + offset) * width + bitIndex) = false) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset zeroValuation))
      (∼tokenSliceBitAtom table start width) := by
  let valuation :=
    extendValuation bitIndex (extendValuation offset zeroValuation)
  let indexTerm := tokenSliceBitIndexTerm start width
  let valueTerm : ValuationTerm := shortBinaryNumeralTerm table
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
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
      valuation indexTerm valueTerm (by
        simpa [valuation, indexTerm, valueTerm, tokenSliceBitIndexTerm,
          termValue_arithmeticAdd, termValue_arithmeticMul,
          termValue_shortBinaryNumeralTerm] using hbit) hvariablesFalse
  simpa [tokenSliceBitAtom, binaryBitAtValuationFormula,
    binaryBitLiteralAtTerms] using direct

private noncomputable def tokenSliceBitBranchCertificate
    (tokenTable width sourceStart targetStart offset bitIndex : Nat)
    (hbit : tokenTable.testBit
        ((sourceStart + offset) * width + bitIndex) =
      tokenTable.testBit
        ((targetStart + offset) * width + bitIndex)) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset zeroValuation))
      (tokenSliceExplicitBitFormula tokenTable width sourceStart
        targetStart) := by
  let sourceAtom := tokenSliceBitAtom tokenTable sourceStart width
  let targetAtom := tokenSliceBitAtom tokenTable targetStart width
  cases hsource : tokenTable.testBit
      ((sourceStart + offset) * width + bitIndex) with
  | false =>
      have htarget : tokenTable.testBit
          ((targetStart + offset) * width + bitIndex) = false := by
        rw [hsource] at hbit
        simpa using hbit.symm
      let sourceFalse := bitAtomFalseCertificate tokenTable sourceStart width
        offset bitIndex hsource
      let targetFalse := bitAtomFalseCertificate tokenTable targetStart width
        offset bitIndex htarget
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := targetAtom) sourceFalse
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := sourceAtom) targetFalse
      let direct :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼sourceAtom ⋎ targetAtom) ⋏
          (∼targetAtom ⋎ sourceAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        rfl) direct
  | true =>
      have htarget : tokenTable.testBit
          ((targetStart + offset) * width + bitIndex) = true := by
        rw [hsource] at hbit
        simpa using hbit.symm
      let sourceTrue := bitAtomTrueCertificate tokenTable sourceStart width
        offset bitIndex hsource
      let targetTrue := bitAtomTrueCertificate tokenTable targetStart width
        offset bitIndex htarget
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼sourceAtom) targetTrue
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼targetAtom) sourceTrue
      let direct :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼sourceAtom ⋎ targetAtom) ⋏
          (∼targetAtom ⋎ sourceAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        rfl) direct

private noncomputable def tokenSliceBitUniversalCertificate
    (tokenTable width sourceStart targetStart offset : Nat)
    (hbits : ∀ bitIndex < width,
      tokenTable.testBit
          ((sourceStart + offset) * width + bitIndex) =
        tokenTable.testBit
          ((targetStart + offset) * width + bitIndex)) :
    TokenSliceHybridCertificate (extendValuation offset zeroValuation)
      (tokenSliceBitUniversalFormula tokenTable width sourceStart
        targetStart) := by
  let body := tokenSliceBitBody tokenTable width sourceStart targetStart
  let branches := buildExplicitHybridUniversalBranches width
    (fun bitIndex hbitIndex =>
      CheckedHybridValuationBoundedFormulaCertificate.cast
        (tokenSliceBitBody_free_alignment tokenTable width sourceStart
          targetStart).symm
        (tokenSliceBitBranchCertificate tokenTable width sourceStart
          targetStart offset bitIndex (hbits bitIndex hbitIndex)))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm width) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm width)) body) =
        tokenSliceBitUniversalFormula tokenTable width sourceStart targetStart
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

private noncomputable def tokenSliceOffsetBranchCertificate
    (tokenTable width sourceStart targetStart offset : Nat)
    (hbits : ∀ bitIndex < width,
      tokenTable.testBit
          ((sourceStart + offset) * width + bitIndex) =
        tokenTable.testBit
          ((targetStart + offset) * width + bitIndex)) :
    TokenSliceHybridCertificate (extendValuation offset zeroValuation)
      (Rewriting.free
        (tokenSliceOffsetBody tokenTable width sourceStart targetStart)) := by
  exact .cast
    (tokenSliceOffsetBody_free_alignment tokenTable width sourceStart
      targetStart).symm
    (tokenSliceBitUniversalCertificate tokenTable width sourceStart
      targetStart offset hbits)

private noncomputable def tokenSliceOffsetUniversalCertificate
    (tokenTable width sourceStart targetStart count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < width,
      tokenTable.testBit
          ((sourceStart + offset) * width + bitIndex) =
        tokenTable.testBit
          ((targetStart + offset) * width + bitIndex)) :
    TokenSliceHybridCertificate zeroValuation
      (tokenSliceOffsetUniversalFormula tokenTable width sourceStart
        targetStart count) := by
  let body := tokenSliceOffsetBody tokenTable width sourceStart targetStart
  let branches := buildExplicitHybridUniversalBranches count
    (fun offset hoffset => tokenSliceOffsetBranchCertificate tokenTable width
      sourceStart targetStart offset (hbits offset hoffset))
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm count) body (by
        simpa [termValue_shortBinaryNumeralTerm] using branches)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        tokenSliceOffsetUniversalFormula tokenTable width sourceStart
          targetStart count
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

/-- Fully explicit checked hybrid certificate for seven closed coordinates.
The caller supplies the count witness, all endpoint and bound facts, and every
bit equality used by the two materialized universal layers. -/
noncomputable def compactFixedWidthTokenSlicesEqExplicitHybridCertificate
    (tokenTable width tokenCount sourceStart sourceFinish targetStart
      targetFinish count : Nat)
    (hcountBound : count <= tokenCount)
    (hsourceEndpoint : sourceFinish = sourceStart + count)
    (htargetEndpoint : targetFinish = targetStart + count)
    (hsourceFinishBound : sourceFinish <= tokenCount)
    (htargetFinishBound : targetFinish <= tokenCount)
    (hbits : ∀ offset < count, ∀ bitIndex < width,
      tokenTable.testBit
          ((sourceStart + offset) * width + bitIndex) =
        tokenTable.testBit
          ((targetStart + offset) * width + bitIndex)) :
    CheckedHybridValuationBoundedFormulaCertificate zeroValuation
      (compactFixedWidthTokenSlicesEqClosedFormula tokenTable width tokenCount
        sourceStart sourceFinish targetStart targetFinish) := by
  rw [compactFixedWidthTokenSlicesEqClosedFormula_alignment]
  refine .existsWitness
    (tokenSliceWitnessBody tokenTable width tokenCount sourceStart
      sourceFinish targetStart targetFinish) count ?_
  let decomposed :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (countGuardCertificate tokenCount count hcountBound)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (closedEndpointCertificate sourceStart sourceFinish count
          hsourceEndpoint)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (closedEndpointCertificate targetStart targetFinish count
            htargetEndpoint)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedLeCertificate sourceFinish tokenCount hsourceFinishBound)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (closedLeCertificate targetFinish tokenCount htargetFinishBound)
              (tokenSliceOffsetUniversalCertificate tokenTable width
                sourceStart targetStart count hbits)))))
  exact .cast (by
    rw [tokenSliceWitnessBody_subst]
    exact (tokenSlicePostWitnessFormula_alignment tokenTable width tokenCount
      sourceStart sourceFinish targetStart targetFinish count).symm) decomposed

/-! ## Arbitrary valuation-term coordinates -/

/-- The quoted token-slice predicate at seven arbitrary valuation terms. -/
def compactFixedWidthTokenSlicesEqAtValuationFormula
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactFixedWidthTokenSlicesEqDef.val) ⇜
    ![tokenTableTerm, widthTerm, tokenCountTerm, sourceStartTerm,
      sourceFinishTerm, targetStartTerm, targetFinishTerm]

def tokenSliceAtValuationWitnessBody
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift tokenCountTerm) + 1 ∧
    !!(Rew.bShift sourceFinishTerm) = !!(Rew.bShift sourceStartTerm) + #0 ∧
    !!(Rew.bShift targetFinishTerm) = !!(Rew.bShift targetStartTerm) + #0 ∧
    !!(Rew.bShift sourceFinishTerm) ≤ !!(Rew.bShift tokenCountTerm) ∧
    !!(Rew.bShift targetFinishTerm) ≤ !!(Rew.bShift tokenCountTerm) ∧
    ∀ offset < #0,
      ∀ bitIndex < !!(Rew.bShift (Rew.bShift widthTerm)),
        (!bitDef
            ((!!(Rew.bShift (Rew.bShift (Rew.bShift sourceStartTerm))) +
                  offset) *
                !!(Rew.bShift (Rew.bShift (Rew.bShift widthTerm))) +
                  bitIndex)
            !!(Rew.bShift (Rew.bShift (Rew.bShift tokenTableTerm))) ↔
          !bitDef
            ((!!(Rew.bShift (Rew.bShift (Rew.bShift targetStartTerm))) +
                  offset) *
                !!(Rew.bShift (Rew.bShift (Rew.bShift widthTerm))) +
                  bitIndex)
            !!(Rew.bShift (Rew.bShift (Rew.bShift tokenTableTerm))))”

private def tokenSliceAtValuationOuterTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 7 -> ValuationTerm :=
  ![tokenTableTerm, widthTerm, tokenCountTerm, sourceStartTerm,
    sourceFinishTerm, targetStartTerm, targetFinishTerm]

private def tokenSliceAtValuationBodyTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 8 -> LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1),
    Rew.bShift tokenTableTerm, Rew.bShift widthTerm,
    Rew.bShift tokenCountTerm, Rew.bShift sourceStartTerm,
    Rew.bShift sourceFinishTerm, Rew.bShift targetStartTerm,
    Rew.bShift targetFinishTerm]

private def tokenSliceAtValuationOffsetTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 9 -> LO.FirstOrder.ArithmeticSemiterm Nat 2 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 2), #1,
    Rew.bShift (Rew.bShift tokenTableTerm),
    Rew.bShift (Rew.bShift widthTerm),
    Rew.bShift (Rew.bShift tokenCountTerm),
    Rew.bShift (Rew.bShift sourceStartTerm),
    Rew.bShift (Rew.bShift sourceFinishTerm),
    Rew.bShift (Rew.bShift targetStartTerm),
    Rew.bShift (Rew.bShift targetFinishTerm)]

private def tokenSliceAtValuationBitTerms
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Fin 10 -> LO.FirstOrder.ArithmeticSemiterm Nat 3 :=
  ![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 3), #1, #2,
    Rew.bShift (Rew.bShift (Rew.bShift tokenTableTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift widthTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift tokenCountTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceStartTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift sourceFinishTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetStartTerm)),
    Rew.bShift (Rew.bShift (Rew.bShift targetFinishTerm))]

private theorem tokenSliceAtValuationBodyRewriting_eq_embSubsts
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (Rew.subst (tokenSliceAtValuationOuterTerms tokenTableTerm widthTerm
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm)).q.comp (Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) =
      Rew.embSubsts (tokenSliceAtValuationBodyTerms tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.comp_app, Rew.q_bvar_zero, Rew.embSubsts_bvar,
          tokenSliceAtValuationBodyTerms]
    | succ coordinate =>
        simp only [Rew.comp_app, Rew.emb_bvar, Rew.q_bvar_succ,
          Rew.embSubsts_bvar]
        rw [Rew.subst_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem tokenSliceAtValuationBodyRewriting_q_eq_embSubsts
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (Rew.embSubsts (tokenSliceAtValuationBodyTerms tokenTableTerm widthTerm
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm)).q =
      Rew.embSubsts (tokenSliceAtValuationOffsetTerms tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm) := by
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar,
          tokenSliceAtValuationOffsetTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem tokenSliceAtValuationBodyRewriting_qq_eq_embSubsts
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    (Rew.embSubsts (tokenSliceAtValuationBodyTerms tokenTableTerm widthTerm
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm)).q.q =
      Rew.embSubsts (tokenSliceAtValuationBitTerms tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm) := by
  rw [tokenSliceAtValuationBodyRewriting_q_eq_embSubsts]
  ext coordinate
  · cases coordinate using Fin.cases with
    | zero =>
        simp [Rew.q_bvar_zero, Rew.embSubsts_bvar,
          tokenSliceAtValuationBitTerms]
    | succ coordinate =>
        simp only [Rew.q_bvar_succ, Rew.embSubsts_bvar]
        fin_cases coordinate <;> rfl
  · exact Empty.elim coordinate

private theorem tokenSliceSourceBody_rewrite_atValuation
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    Rew.embSubsts (tokenSliceAtValuationBodyTerms tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm) ▹ tokenSliceSourceBody =
      tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
        sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm := by
  unfold tokenSliceSourceBody tokenSliceSourceTail
    tokenSliceAtValuationWitnessBody
  simp only [LogicalConnective.HomClass.map_and, rewriting_ballLT]
  rw [tokenSliceAtValuationBodyRewriting_qq_eq_embSubsts,
    tokenSliceAtValuationBodyRewriting_q_eq_embSubsts]
  simp [tokenSliceAtValuationBodyTerms,
    tokenSliceAtValuationOffsetTerms, tokenSliceAtValuationBitTerms,
    membershipOperator_eq_binaryBitAtomAtTerms, binaryBitAtomAtTerms]

theorem compactFixedWidthTokenSlicesEqAtValuationFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm) :
    compactFixedWidthTokenSlicesEqAtValuationFormula tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm =
      ∃⁰ tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm := by
  unfold compactFixedWidthTokenSlicesEqAtValuationFormula
  rw [compactFixedWidthTokenSlicesEqDef_val_eq_exists]
  change
    Rew.subst (tokenSliceAtValuationOuterTerms tokenTableTerm widthTerm
      tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm) ▹
        (Rewriting.emb (ξ := Nat) (∃⁰ tokenSliceSourceBody)) = _
  simp only [Rewriting.app_exs, Rew.q_emb]
  rw [← TransitiveRewriting.comp_app,
    tokenSliceAtValuationBodyRewriting_eq_embSubsts,
    tokenSliceSourceBody_rewrite_atValuation]

def tokenSliceAtValuationPostWitnessFormula
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) : ValuationFormula :=
  (Rew.subst ![shortBinaryNumeralTerm count]) ▹
    tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm

def tokenSliceAtValuationOffsetBitBody
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) : LO.FirstOrder.ArithmeticSemiformula Nat 2 :=
  “(!bitDef
        ((!!(Rew.bShift (Rew.bShift sourceStartTerm)) + #1) *
            !!(Rew.bShift (Rew.bShift widthTerm)) + #0)
        !!(Rew.bShift (Rew.bShift tokenTableTerm)) ↔
      !bitDef
        ((!!(Rew.bShift (Rew.bShift targetStartTerm)) + #1) *
            !!(Rew.bShift (Rew.bShift widthTerm)) + #0)
        !!(Rew.bShift (Rew.bShift tokenTableTerm)))”

def tokenSliceAtValuationOffsetBody
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (tokenSliceAtValuationOffsetBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm).ballLT (Rew.bShift widthTerm)

def tokenSliceAtValuationBitBody
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) : LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  “(!bitDef
        ((!!(Rew.bShift (Rew.shift sourceStartTerm)) +
              !!(Rew.bShift (&0 : ValuationTerm))) *
            !!(Rew.bShift (Rew.shift widthTerm)) + #0)
        !!(Rew.bShift (Rew.shift tokenTableTerm)) ↔
      !bitDef
        ((!!(Rew.bShift (Rew.shift targetStartTerm)) +
              !!(Rew.bShift (&0 : ValuationTerm))) *
            !!(Rew.bShift (Rew.shift widthTerm)) + #0)
        !!(Rew.bShift (Rew.shift tokenTableTerm)))”

def tokenSliceAtValuationBitUniversalFormula
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) : ValuationFormula :=
  (tokenSliceAtValuationBitBody tokenTableTerm widthTerm sourceStartTerm
    targetStartTerm).ballLT (Rew.shift widthTerm)

def tokenSliceAtValuationOffsetUniversalFormula
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) (count : Nat) : ValuationFormula :=
  (tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm sourceStartTerm
    targetStartTerm).ballLT (shortBinaryNumeralTerm count)

def tokenSliceAtValuationBitIndexTerm
    (startTerm widthTerm : ValuationTerm) : ValuationTerm :=
  ‘(!!(Rew.shift (Rew.shift startTerm)) + &1) *
      !!(Rew.shift (Rew.shift widthTerm)) + &0’

def tokenSliceAtValuationBitAtom
    (tableTerm startTerm widthTerm : ValuationTerm) : ValuationFormula :=
  binaryBitAtomAtTerms
    (tokenSliceAtValuationBitIndexTerm startTerm widthTerm)
    (Rew.shift (Rew.shift tableTerm))

def tokenSliceAtValuationExplicitBitFormula
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) : ValuationFormula :=
  tokenSliceAtValuationBitAtom tokenTableTerm sourceStartTerm widthTerm 🡘
    tokenSliceAtValuationBitAtom tokenTableTerm targetStartTerm widthTerm

def tokenSliceAtValuationDecomposedPostWitnessFormula
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm count) < !!tokenCountTerm + 1” ⋏
    (“!!sourceFinishTerm =
        !!sourceStartTerm + !!(shortBinaryNumeralTerm count)” ⋏
      (“!!targetFinishTerm =
          !!targetStartTerm + !!(shortBinaryNumeralTerm count)” ⋏
        (“!!sourceFinishTerm ≤ !!tokenCountTerm” ⋏
          (“!!targetFinishTerm ≤ !!tokenCountTerm” ⋏
            tokenSliceAtValuationOffsetUniversalFormula tokenTableTerm
              widthTerm sourceStartTerm targetStartTerm count))))

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

theorem tokenSliceAtValuationPostWitnessFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat) :
    tokenSliceAtValuationPostWitnessFormula tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm count =
      tokenSliceAtValuationDecomposedPostWitnessFormula tokenTableTerm
        widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
        targetStartTerm targetFinishTerm count := by
  simp [tokenSliceAtValuationPostWitnessFormula,
    tokenSliceAtValuationWitnessBody,
    tokenSliceAtValuationDecomposedPostWitnessFormula,
    tokenSliceAtValuationOffsetUniversalFormula,
    tokenSliceAtValuationOffsetBody,
    tokenSliceAtValuationOffsetBitBody, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution]

theorem tokenSliceAtValuationOffsetBody_free_alignment
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) :
    Rewriting.free (tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm) =
      tokenSliceAtValuationBitUniversalFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm := by
  simp [tokenSliceAtValuationOffsetBody,
    tokenSliceAtValuationOffsetBitBody,
    tokenSliceAtValuationBitUniversalFormula,
    tokenSliceAtValuationBitBody, rewriting_ballLT,
    rewriting_embeddedFormulaSubstitution, free_bShift2_term,
    free_bvar_one_fin2]

theorem tokenSliceAtValuationBitBody_free_alignment
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm) :
    Rewriting.free (tokenSliceAtValuationBitBody tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm) =
      tokenSliceAtValuationExplicitBitFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm := by
  simp [tokenSliceAtValuationBitBody,
    tokenSliceAtValuationExplicitBitFormula,
    tokenSliceAtValuationBitAtom, tokenSliceAtValuationBitIndexTerm,
    rewriting_embeddedFormulaSubstitution, binaryBitAtomAtTerms]

noncomputable def tokenSliceAtValuationCountGuardCertificate
    (valuation : Nat -> Nat) (tokenCountTerm : ValuationTerm)
    (count : Nat)
    (hbound : count <= termValue valuation tokenCountTerm) :
    TokenSliceHybridCertificate valuation
      “!!(shortBinaryNumeralTerm count) < !!tokenCountTerm + 1” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm count,
        (‘!!tokenCountTerm + 1’ : ValuationTerm)] (by
        change termValue valuation (shortBinaryNumeralTerm count) <
          termValue valuation (‘!!tokenCountTerm + 1’ : ValuationTerm)
        simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
          termValue_arithmeticOne] using Nat.lt_succ_of_le hbound)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def tokenSliceAtValuationLeCertificate
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hle : termValue valuation leftTerm <= termValue valuation rightTerm) :
    TokenSliceHybridCertificate valuation “!!leftTerm ≤ !!rightTerm” := by
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

noncomputable def tokenSliceAtValuationEndpointCertificate
    (valuation : Nat -> Nat) (startTerm finishTerm : ValuationTerm)
    (count : Nat)
    (hendpoint : termValue valuation finishTerm =
      termValue valuation startTerm + count) :
    TokenSliceHybridCertificate valuation
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

noncomputable def tokenSliceAtValuationBitAtomTrueCertificate
    (valuation : Nat -> Nat)
    (tableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tableTerm).testBit
      ((termValue valuation startTerm + offset) *
        termValue valuation widthTerm + bitIndex) = true) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (tokenSliceAtValuationBitAtom tableTerm startTerm widthTerm) := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
  have hvariables :
      indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
        (binaryBitAtValuationFormula true
          indexTerm valueTerm).freeVariables :=
    binaryBitHybridVariablesTrue indexTerm valueTerm
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
      branchValuation indexTerm valueTerm (by
        simpa [branchValuation, indexTerm, valueTerm,
          tokenSliceAtValuationBitIndexTerm, termValue_arithmeticAdd,
          termValue_arithmeticMul, termValue_shift] using hbit) hvariables
  exact .cast (by
    dsimp only [indexTerm, valueTerm]
    simp [tokenSliceAtValuationBitAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms]) direct

noncomputable def tokenSliceAtValuationBitAtomFalseCertificate
    (valuation : Nat -> Nat)
    (tableTerm startTerm widthTerm : ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tableTerm).testBit
      ((termValue valuation startTerm + offset) *
        termValue valuation widthTerm + bitIndex) = false) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (∼tokenSliceAtValuationBitAtom tableTerm startTerm widthTerm) := by
  let branchValuation :=
    extendValuation bitIndex (extendValuation offset valuation)
  let indexTerm := tokenSliceAtValuationBitIndexTerm startTerm widthTerm
  let valueTerm := Rew.shift (Rew.shift tableTerm)
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
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
      branchValuation indexTerm valueTerm (by
        simpa [branchValuation, indexTerm, valueTerm,
          tokenSliceAtValuationBitIndexTerm, termValue_arithmeticAdd,
          termValue_arithmeticMul, termValue_shift] using hbit) hvariablesFalse
  exact .cast (by
    dsimp only [indexTerm, valueTerm]
    simp [tokenSliceAtValuationBitAtom, binaryBitAtValuationFormula,
      binaryBitLiteralAtTerms]) direct

inductive TokenSliceAtValuationBitBranchData
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat) : Type where
  | isFalse
      (hsource : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation sourceStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) = false)
      (htarget : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation targetStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) = false)
  | isTrue
      (hsource : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation sourceStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) = true)
      (htarget : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation targetStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) = true)

def tokenSliceAtValuationBitBranchDataOfEquality
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation sourceStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) =
      (termValue valuation tokenTableTerm).testBit
        ((termValue valuation targetStartTerm + offset) *
          termValue valuation widthTerm + bitIndex)) :
    TokenSliceAtValuationBitBranchData valuation tokenTableTerm widthTerm
      sourceStartTerm targetStartTerm offset bitIndex := by
  cases hsource : (termValue valuation tokenTableTerm).testBit
      ((termValue valuation sourceStartTerm + offset) *
        termValue valuation widthTerm + bitIndex) with
  | false =>
      have htarget : (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) = false := by
        rw [hsource] at hbit
        simpa using hbit.symm
      exact .isFalse hsource htarget
  | true =>
      have htarget : (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) = true := by
        rw [hsource] at hbit
        simpa using hbit.symm
      exact .isTrue hsource htarget

noncomputable def tokenSliceAtValuationBitBranchCertificateFromData
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat)
    (data : TokenSliceAtValuationBitBranchData valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset bitIndex) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (tokenSliceAtValuationExplicitBitFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm) := by
  let sourceAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    sourceStartTerm widthTerm
  let targetAtom := tokenSliceAtValuationBitAtom tokenTableTerm
    targetStartTerm widthTerm
  cases data with
  | isFalse hsource htarget =>
      let sourceFalse := tokenSliceAtValuationBitAtomFalseCertificate
        valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
        hsource
      let targetFalse := tokenSliceAtValuationBitAtomFalseCertificate
        valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
        htarget
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := targetAtom) sourceFalse
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := sourceAtom) targetFalse
      let direct :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼sourceAtom ⋎ targetAtom) ⋏
          (∼targetAtom ⋎ sourceAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        rfl) direct
  | isTrue hsource htarget =>
      let sourceTrue := tokenSliceAtValuationBitAtomTrueCertificate
        valuation tokenTableTerm sourceStartTerm widthTerm offset bitIndex
        hsource
      let targetTrue := tokenSliceAtValuationBitAtomTrueCertificate
        valuation tokenTableTerm targetStartTerm widthTerm offset bitIndex
        htarget
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼sourceAtom) targetTrue
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼targetAtom) sourceTrue
      let direct :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼sourceAtom ⋎ targetAtom) ⋏
          (∼targetAtom ⋎ sourceAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        rfl) direct

noncomputable def tokenSliceAtValuationBitBranchCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset bitIndex : Nat)
    (hbit : (termValue valuation tokenTableTerm).testBit
        ((termValue valuation sourceStartTerm + offset) *
          termValue valuation widthTerm + bitIndex) =
      (termValue valuation tokenTableTerm).testBit
        ((termValue valuation targetStartTerm + offset) *
          termValue valuation widthTerm + bitIndex)) :
    TokenSliceHybridCertificate
      (extendValuation bitIndex (extendValuation offset valuation))
      (tokenSliceAtValuationExplicitBitFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm) :=
  tokenSliceAtValuationBitBranchCertificateFromData valuation tokenTableTerm
    widthTerm sourceStartTerm targetStartTerm offset bitIndex
    (tokenSliceAtValuationBitBranchDataOfEquality valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset bitIndex hbit)

theorem tokenSliceAtValuationBitBound_eq
    (valuation : Nat -> Nat) (widthTerm : ValuationTerm) (offset : Nat) :
    termValue valuation widthTerm =
      termValue (extendValuation offset valuation) (Rew.shift widthTerm) := by
  simp only [termValue_shift]

noncomputable def tokenSliceAtValuationBitUniversalBranches
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    CheckedHybridValuationUniversalBranches
      (extendValuation offset valuation)
      (tokenSliceAtValuationBitBody tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm)
      (termValue (extendValuation offset valuation) (Rew.shift widthTerm)) :=
  (tokenSliceAtValuationBitBound_eq valuation widthTerm offset) ▸
    buildExplicitHybridUniversalBranches (termValue valuation widthTerm)
      (fun bitIndex hbitIndex =>
      CheckedHybridValuationBoundedFormulaCertificate.cast
        (tokenSliceAtValuationBitBody_free_alignment tokenTableTerm widthTerm
          sourceStartTerm targetStartTerm).symm
        (tokenSliceAtValuationBitBranchCertificate valuation tokenTableTerm
          widthTerm sourceStartTerm targetStartTerm offset bitIndex
          (hbits bitIndex hbitIndex)))

noncomputable def tokenSliceAtValuationBitUniversalCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    TokenSliceHybridCertificate (extendValuation offset valuation)
      (tokenSliceAtValuationBitUniversalFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm) := by
  let body := tokenSliceAtValuationBitBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let boundTerm := Rew.shift widthTerm
  let branches := tokenSliceAtValuationBitUniversalBranches valuation
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm offset hbits
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      boundTerm body branches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift boundTerm) body) =
      tokenSliceAtValuationBitUniversalFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def tokenSliceAtValuationOffsetBranchCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (offset : Nat)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    TokenSliceHybridCertificate (extendValuation offset valuation)
      (Rewriting.free (tokenSliceAtValuationOffsetBody tokenTableTerm
        widthTerm sourceStartTerm targetStartTerm)) := by
  exact .cast
    (tokenSliceAtValuationOffsetBody_free_alignment tokenTableTerm widthTerm
      sourceStartTerm targetStartTerm).symm
    (tokenSliceAtValuationBitUniversalCertificate valuation tokenTableTerm
      widthTerm sourceStartTerm targetStartTerm offset hbits)

theorem tokenSliceAtValuationOffsetBound_eq
    (valuation : Nat -> Nat) (count : Nat) :
    count = termValue valuation (shortBinaryNumeralTerm count) := by
  simp only [termValue_shortBinaryNumeralTerm]

noncomputable def tokenSliceAtValuationOffsetUniversalBranches
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    CheckedHybridValuationUniversalBranches valuation
      (tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm sourceStartTerm
        targetStartTerm)
      (termValue valuation (shortBinaryNumeralTerm count)) :=
  (tokenSliceAtValuationOffsetBound_eq valuation count) ▸
    buildExplicitHybridUniversalBranches count
      (fun offset hoffset => tokenSliceAtValuationOffsetBranchCertificate
      valuation tokenTableTerm widthTerm sourceStartTerm targetStartTerm
      offset (hbits offset hoffset))

noncomputable def tokenSliceAtValuationOffsetUniversalCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm sourceStartTerm targetStartTerm :
      ValuationTerm)
    (count : Nat)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    TokenSliceHybridCertificate valuation
      (tokenSliceAtValuationOffsetUniversalFormula tokenTableTerm widthTerm
        sourceStartTerm targetStartTerm count) := by
  let body := tokenSliceAtValuationOffsetBody tokenTableTerm widthTerm
    sourceStartTerm targetStartTerm
  let branches := tokenSliceAtValuationOffsetUniversalBranches valuation
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm count hbits
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm count) body branches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm count)) body) =
        tokenSliceAtValuationOffsetUniversalFormula tokenTableTerm widthTerm
          sourceStartTerm targetStartTerm count
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def tokenSliceAtValuationPostWitnessCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hcountBound : count <= termValue valuation tokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation tokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation tokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    TokenSliceHybridCertificate valuation
      (tokenSliceAtValuationPostWitnessFormula tokenTableTerm widthTerm
        tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
        targetFinishTerm count) := by
  let decomposed :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (tokenSliceAtValuationCountGuardCertificate valuation tokenCountTerm
        count hcountBound)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (tokenSliceAtValuationEndpointCertificate valuation sourceStartTerm
          sourceFinishTerm count hsourceEndpoint)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (tokenSliceAtValuationEndpointCertificate valuation targetStartTerm
            targetFinishTerm count htargetEndpoint)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (tokenSliceAtValuationLeCertificate valuation sourceFinishTerm
              tokenCountTerm hsourceFinishBound)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (tokenSliceAtValuationLeCertificate valuation targetFinishTerm
                tokenCountTerm htargetFinishBound)
              (tokenSliceAtValuationOffsetUniversalCertificate valuation
                tokenTableTerm widthTerm sourceStartTerm targetStartTerm
                count hbits)))))
  exact .cast
    (tokenSliceAtValuationPostWitnessFormula_alignment tokenTableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm count).symm decomposed

/-- Explicit checked hybrid certificate at seven original valuation terms.
Callers may retain arithmetic starts such as `leftStart + 1` syntactically. -/
noncomputable def
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count : Nat)
    (hcountBound : count <= termValue valuation tokenCountTerm)
    (hsourceEndpoint : termValue valuation sourceFinishTerm =
      termValue valuation sourceStartTerm + count)
    (htargetEndpoint : termValue valuation targetFinishTerm =
      termValue valuation targetStartTerm + count)
    (hsourceFinishBound : termValue valuation sourceFinishTerm <=
      termValue valuation tokenCountTerm)
    (htargetFinishBound : termValue valuation targetFinishTerm <=
      termValue valuation tokenCountTerm)
    (hbits : ∀ offset < count, ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          ((termValue valuation sourceStartTerm + offset) *
            termValue valuation widthTerm + bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          ((termValue valuation targetStartTerm + offset) *
            termValue valuation widthTerm + bitIndex)) :
    TokenSliceHybridCertificate valuation
      (compactFixedWidthTokenSlicesEqAtValuationFormula tokenTableTerm
        widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
        targetStartTerm targetFinishTerm) := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.existsWitness
    (tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
    count
    (tokenSliceAtValuationPostWitnessCertificate valuation tokenTableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm count hcountBound hsourceEndpoint htargetEndpoint
      hsourceFinishBound htargetFinishBound hbits)
  exact .cast
    (compactFixedWidthTokenSlicesEqAtValuationFormula_alignment tokenTableTerm
      widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm).symm direct

#print axioms compactFixedWidthTokenSlicesEqClosedFormula_alignment
#print axioms compactFixedWidthTokenSlicesEqExplicitHybridCertificate
#print axioms compactFixedWidthTokenSlicesEqAtValuationFormula_alignment
#print axioms compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate

end FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
