import integration.FoundationCompactNumericListedDirectChildResultListPushDropRows
import integration.FoundationCompactNumericListedDirectChildResultBoundedHeadEqExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectChildResultBoundedRowsEqExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for child-result-list push/drop rows

The three count facts and the prescribed target head are certified directly.
Every source-count branch either installs the checked fourteen-witness row
equality or explicitly certifies that its implication guard is false.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectChildResultListPushDropRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectChildResultBoundedRowsEquality
open FoundationCompactNumericListedDirectChildResultBoundedHeadEqExplicitHybridCertificate
open FoundationCompactNumericListedDirectChildResultBoundedRowsEqExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

private noncomputable def closedLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def closedOneLeCertificate
    (right : Nat) (hle : 1 ≤ right) :
    HybridCertificate “1 ≤ !!(shortBinaryNumeralTerm right)” := by
  if heq : 1 = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![(‘1’ : ValuationTerm), shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (‘1’ : ValuationTerm) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_arithmeticOne,
          termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : 1 < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![(‘1’ : ValuationTerm), shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (‘1’ : ValuationTerm) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_arithmeticOne,
          termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def closedCountEquationCertificate
    (sourceCount consumed targetCount : Nat)
    (heq : sourceCount + 1 = consumed + targetCount) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm sourceCount) + 1 =
        !!(shortBinaryNumeralTerm consumed) +
          !!(shortBinaryNumeralTerm targetCount)” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![(‘!!(shortBinaryNumeralTerm sourceCount) + 1’ : ValuationTerm),
      (‘!!(shortBinaryNumeralTerm consumed) +
        !!(shortBinaryNumeralTerm targetCount)’ : ValuationTerm)] (by
      change termValue zeroValuation
          (‘!!(shortBinaryNumeralTerm sourceCount) + 1’ : ValuationTerm) =
        termValue zeroValuation
          (‘!!(shortBinaryNumeralTerm consumed) +
            !!(shortBinaryNumeralTerm targetCount)’ : ValuationTerm)
      simpa [termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
        termValue_arithmeticOne] using heq)

private def compactNumericChildResultListPushDropRowsGuardBody
    (sourceCount consumed : Nat) : ArithmeticSemiformula Nat 1 :=
  “!!(Rew.bShift (shortBinaryNumeralTerm consumed)) + #0 <
    !!(Rew.bShift (shortBinaryNumeralTerm sourceCount))”

private def compactNumericChildResultListPushDropRowsRowBody
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound consumed : Nat) : ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowsEqDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm sourceBoundary),
      Rew.bShift (shortBinaryNumeralTerm targetBoundary),
      Rew.bShift (shortBinaryNumeralTerm valueBound),
      ‘!!(Rew.bShift (shortBinaryNumeralTerm consumed)) + #0’,
      ‘#0 + 1’]

/-- The implication body enumerated by the source-count universal. -/
def compactNumericChildResultListPushDropRowsUniversalBody
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      valueBound consumed : Nat) : ArithmeticSemiformula Nat 1 :=
  LO.Arrow.arrow
    (compactNumericChildResultListPushDropRowsGuardBody sourceCount consumed)
    (compactNumericChildResultListPushDropRowsRowBody
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound consumed)

private def compactNumericChildResultListPushDropRowsGuardFormula
    (sourceCount consumed : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm consumed) + &0 <
    !!(shortBinaryNumeralTerm sourceCount)”

private theorem compactNumericChildResultListPushDropRowsRowBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound consumed : Nat) :
    Rewriting.free
        (compactNumericChildResultListPushDropRowsRowBody
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound consumed) =
      compactNumericChildResultBoundedRowsEqAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
          (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm) := by
  unfold compactNumericChildResultListPushDropRowsRowBody
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactNumericChildResultBoundedRowsEqAtValuationFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp

private theorem
    compactNumericChildResultListPushDropRowsUniversalBody_free_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      valueBound consumed : Nat) :
    Rewriting.free
        (compactNumericChildResultListPushDropRowsUniversalBody
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
            valueBound consumed) =
      (∼compactNumericChildResultListPushDropRowsGuardFormula
          sourceCount consumed ⋎
        compactNumericChildResultBoundedRowsEqAtValuationFormula
          tokenTable width tokenCount sourceBoundary targetBoundary valueBound
            (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
            (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm)) := by
  simp [compactNumericChildResultListPushDropRowsUniversalBody,
    compactNumericChildResultListPushDropRowsGuardBody,
    compactNumericChildResultListPushDropRowsGuardFormula,
    LO.FirstOrder.Semiformula.imp_eq,
    compactNumericChildResultListPushDropRowsRowBody_free_alignment]

private noncomputable def
    compactNumericChildResultListPushDropRowsGuardFalseCertificate
    (sourceCount consumed index : Nat)
    (hguard : ¬consumed + index < sourceCount) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index zeroValuation)
      (∼compactNumericChildResultListPushDropRowsGuardFormula
        sourceCount consumed) := by
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm consumed) + &0’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.negativeAtomic
    (extendValuation index zeroValuation) Language.ORing.Rel.lt
    ![leftTerm, shortBinaryNumeralTerm sourceCount] (by
      change ¬termValue (extendValuation index zeroValuation) leftTerm <
        termValue (extendValuation index zeroValuation)
          (shortBinaryNumeralTerm sourceCount)
      simpa [leftTerm, termValue_arithmeticAdd,
        termValue_shortBinaryNumeralTerm] using hguard)
  exact .cast (by
    unfold compactNumericChildResultListPushDropRowsGuardFormula leftTerm
    rfl) direct

private noncomputable def
    compactNumericChildResultListPushDropRowsBranchCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      valueBound consumed index : Nat)
    (hrow : consumed + index < sourceCount ->
      CompactNumericChildResultBoundedRowsEq
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (consumed + index) (index + 1)) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index zeroValuation)
      (Rewriting.free
        (compactNumericChildResultListPushDropRowsUniversalBody
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
            valueBound consumed)) := by
  rw [compactNumericChildResultListPushDropRowsUniversalBody_free_alignment]
  if hguard : consumed + index < sourceCount then
    exact .disjunctionRight
      (left := ∼compactNumericChildResultListPushDropRowsGuardFormula
        sourceCount consumed)
      (compactNumericChildResultBoundedRowsEqAtValuationExplicitHybridCertificate
        (extendValuation index zeroValuation)
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
        (consumed + index) (index + 1)
        (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
        (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm) (by
          rw [termValue_arithmeticAdd]
          simp [termValue_shortBinaryNumeralTerm]) (by
          rw [termValue_arithmeticAdd, termValue_arithmeticOne]
          simp) (hrow hguard))
  else
    exact .disjunctionLeft
      (right := compactNumericChildResultBoundedRowsEqAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
          (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm))
      (compactNumericChildResultListPushDropRowsGuardFalseCertificate
        sourceCount consumed index hguard)

/-- Close all thirteen public inputs of the push/drop predicate. -/
def compactNumericChildResultListPushDropRowsClosedFormula
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      expectedGammaBoundary expectedGammaCount tableWidth valueBound
      consumed expectedBool : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultListPushDropRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm expectedGammaBoundary,
      shortBinaryNumeralTerm expectedGammaCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm consumed,
      shortBinaryNumeralTerm expectedBool]

theorem compactNumericChildResultListPushDropRowsClosedFormula_alignment
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      expectedGammaBoundary expectedGammaCount tableWidth valueBound
      consumed expectedBool : Nat) :
    compactNumericChildResultListPushDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount expectedGammaBoundary expectedGammaCount
        tableWidth valueBound consumed expectedBool =
      (“!!(shortBinaryNumeralTerm consumed) ≤
          !!(shortBinaryNumeralTerm sourceCount)” ⋏
        (“!!(shortBinaryNumeralTerm sourceCount) + 1 =
            !!(shortBinaryNumeralTerm consumed) +
              !!(shortBinaryNumeralTerm targetCount)” ⋏
          (“1 ≤ !!(shortBinaryNumeralTerm targetCount)” ⋏
            (compactNumericChildResultBoundedHeadEqClosedFormula
              tokenTable width tokenCount targetBoundary
                expectedGammaBoundary expectedGammaCount valueBound 0
                expectedBool ⋏
              (compactNumericChildResultListPushDropRowsUniversalBody
                tokenTable width tokenCount sourceBoundary sourceCount
                  targetBoundary valueBound consumed).ballLT
                (shortBinaryNumeralTerm sourceCount))))) := by
  unfold compactNumericChildResultListPushDropRowsClosedFormula
  unfold compactNumericChildResultListPushDropRowsDef
  simp [compactNumericChildResultListPushDropRowsUniversalBody,
    compactNumericChildResultListPushDropRowsGuardBody,
    compactNumericChildResultListPushDropRowsRowBody,
    compactNumericChildResultBoundedHeadEqClosedFormula,
    rewriting_ballLT, LO.FirstOrder.Semiformula.imp_eq,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, arithmeticZeroTerm,
          Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
          Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    have hq (parameter : Fin 13) :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount,
            shortBinaryNumeralTerm expectedGammaBoundary,
            shortBinaryNumeralTerm expectedGammaCount,
            shortBinaryNumeralTerm tableWidth,
            shortBinaryNumeralTerm valueBound,
            shortBinaryNumeralTerm consumed,
            shortBinaryNumeralTerm expectedBool]).q
            (#parameter.succ : ArithmeticSemiterm Nat 14) =
          Rew.bShift
            (![shortBinaryNumeralTerm tokenTable,
              shortBinaryNumeralTerm width,
              shortBinaryNumeralTerm tokenCount,
              shortBinaryNumeralTerm sourceBoundary,
              shortBinaryNumeralTerm sourceCount,
              shortBinaryNumeralTerm targetBoundary,
              shortBinaryNumeralTerm targetCount,
              shortBinaryNumeralTerm expectedGammaBoundary,
              shortBinaryNumeralTerm expectedGammaCount,
              shortBinaryNumeralTerm tableWidth,
              shortBinaryNumeralTerm valueBound,
              shortBinaryNumeralTerm consumed,
              shortBinaryNumeralTerm expectedBool] parameter) := by
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
    have hrowRewriting :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount,
            shortBinaryNumeralTerm expectedGammaBoundary,
            shortBinaryNumeralTerm expectedGammaCount,
            shortBinaryNumeralTerm tableWidth,
            shortBinaryNumeralTerm valueBound,
            shortBinaryNumeralTerm consumed,
            shortBinaryNumeralTerm expectedBool]).q.comp
            ((Rew.emb : Rew ℒₒᵣ Empty 14 Nat 14).comp
              (Rew.subst
                ![(#1 : ArithmeticSemiterm Empty 14), #2, #3, #4,
                  #6, #11, ‘#12 + #0’, ‘#0 + 1’])) =
          (Rew.subst
            ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
              Rew.bShift (shortBinaryNumeralTerm width),
              Rew.bShift (shortBinaryNumeralTerm tokenCount),
              Rew.bShift (shortBinaryNumeralTerm sourceBoundary),
              Rew.bShift (shortBinaryNumeralTerm targetBoundary),
              Rew.bShift (shortBinaryNumeralTerm valueBound),
              ‘!!(Rew.bShift (shortBinaryNumeralTerm consumed)) + #0’,
              ‘#0 + 1’]).comp
            (Rew.emb : Rew ℒₒᵣ Empty 8 Nat 8) := by
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp only [Rew.comp_app, Rew.emb_bvar, Rew.subst_bvar]
        · simpa using hq (0 : Fin 13)
        · simpa using hq (1 : Fin 13)
        · simpa using hq (2 : Fin 13)
        · simpa using hq (3 : Fin 13)
        · simpa using hq (5 : Fin 13)
        · simpa using hq (10 : Fin 13)
        · simpa [Rew.comp_app, Rew.subst_bvar] using
            congrArg
              (fun term : ArithmeticSemiterm Nat 1 =>
                (‘!!term + #0’ : ArithmeticSemiterm Nat 1))
              (hq (11 : Fin 13))
        · simp [Rew.emb_bvar, Rew.q_bvar_zero]
      · intro coordinate
        exact Empty.elim coordinate
    have hconsumed :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount,
            shortBinaryNumeralTerm expectedGammaBoundary,
            shortBinaryNumeralTerm expectedGammaCount,
            shortBinaryNumeralTerm tableWidth,
            shortBinaryNumeralTerm valueBound,
            shortBinaryNumeralTerm consumed,
            shortBinaryNumeralTerm expectedBool]).q
            (#12 : ArithmeticSemiterm Nat 14) =
          Rew.bShift (shortBinaryNumeralTerm consumed) := by
      simpa using hq (11 : Fin 13)
    have hsourceCount :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount,
            shortBinaryNumeralTerm expectedGammaBoundary,
            shortBinaryNumeralTerm expectedGammaCount,
            shortBinaryNumeralTerm tableWidth,
            shortBinaryNumeralTerm valueBound,
            shortBinaryNumeralTerm consumed,
            shortBinaryNumeralTerm expectedBool]).q
            (#5 : ArithmeticSemiterm Nat 14) =
          Rew.bShift (shortBinaryNumeralTerm sourceCount) := by
      simpa using hq (4 : Fin 13)
    rw [hconsumed, hsourceCount, hrowRewriting]

/-- Assemble the complete push/drop certificate from the semantic graph. -/
noncomputable def compactNumericChildResultListPushDropRowsExplicitHybridCertificate
    (tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount
      expectedGammaBoundary expectedGammaCount tableWidth valueBound
      consumed expectedBool : Nat)
    (hgraph : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount expectedGammaBoundary expectedGammaCount
      tableWidth valueBound consumed expectedBool) :
    HybridCertificate
      (compactNumericChildResultListPushDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount expectedGammaBoundary expectedGammaCount
        tableWidth valueBound consumed expectedBool) := by
  rw [compactNumericChildResultListPushDropRowsClosedFormula_alignment]
  let consumedBound := closedLeCertificate consumed sourceCount hgraph.1
  let countEquation := closedCountEquationCertificate
    sourceCount consumed targetCount hgraph.2.1
  let targetNonempty := closedOneLeCertificate targetCount hgraph.2.2.1
  let head := compactNumericChildResultBoundedHeadEqExplicitHybridCertificate
    tokenTable width tokenCount targetBoundary expectedGammaBoundary
      expectedGammaCount valueBound 0 expectedBool hgraph.2.2.2.1
  let body := compactNumericChildResultListPushDropRowsUniversalBody
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      valueBound consumed
  let branches := buildExplicitHybridUniversalBranches sourceCount
    (fun index hindex =>
      compactNumericChildResultListPushDropRowsBranchCertificate
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          valueBound consumed index (hgraph.2.2.2.2 index hindex))
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm sourceCount) body (by
      simpa [termValue_shortBinaryNumeralTerm] using branches)
  let universal : HybridCertificate
      (body.ballLT (shortBinaryNumeralTerm sourceCount)) := .cast (by
        change (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body) =
            body.ballLT (shortBinaryNumeralTerm sourceCount)
        rw [termBoundedUniversal_eq_ball]
        rfl) direct
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    consumedBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction countEquation
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        targetNonempty
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          head universal)))

#print axioms compactNumericChildResultListPushDropRowsClosedFormula
#print axioms compactNumericChildResultListPushDropRowsClosedFormula_alignment
#print axioms compactNumericChildResultListPushDropRowsExplicitHybridCertificate

end FoundationCompactNumericListedDirectChildResultListPushDropRowsExplicitHybridCertificate
