import integration.FoundationCompactNumericListedDirectVerifierTaskBoundedRowsEqExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for equal natural-list-list row tables

The outer count equality is an explicit arithmetic atom.  Each bounded
universal branch is exactly the verified task-row equality predicate with
`valueBound = tokenCount` and both row indices set to the branch index.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectNatListListSameRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListListSameRows
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectVerifierTaskBoundedRowsEqExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAExplicitHybridUniversalBranches
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

private noncomputable def closedEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm left) =
        !!(shortBinaryNumeralTerm right)” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using heq)

/-- Close the seven inputs of the same-rows predicate by binary numerals. -/
def compactAdditiveNatListListSameRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListListSameRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount]

private def compactAdditiveNatListListSameRowsNamedDef :
    𝚺₀.Semisentence 7 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount.
    targetCount = sourceCount ∧
    ∀ index < sourceCount,
      !(compactNumericVerifierTaskBoundedRowsEqDef)
        tokenTable width tokenCount sourceBoundary targetBoundary
          tokenCount index index”

private theorem compactAdditiveNatListListSameRowsDef_eq_namedDef :
    compactAdditiveNatListListSameRowsDef.val =
      compactAdditiveNatListListSameRowsNamedDef.val := by
  unfold compactAdditiveNatListListSameRowsDef
  unfold compactAdditiveNatListListSameRowsNamedDef
  unfold compactNumericVerifierTaskBoundedRowsEqDef
  simp [Semiformula.bexsLTSucc, Semiformula.bexsLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    · apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      · apply Rewriting.smul_ext'
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
        · intro coordinate
          exact Empty.elim coordinate
      · congr 1
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate

/-- The same matrix after the universal index becomes valuation variable zero. -/
private def compactAdditiveNatListListSameRowsRowAtValuationFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ValuationFormula :=
  compactNumericVerifierTaskBoundedRowsEqAtValuationFormula
    tokenTable width tokenCount sourceBoundary targetBoundary tokenCount
      (&0 : ValuationTerm) (&0 : ValuationTerm)

/-- The exact row-equality matrix under the outer universal index. -/
private def compactAdditiveNatListListSameRowsUniversalBody
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskBoundedRowsEqDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm sourceBoundary),
      Rew.bShift (shortBinaryNumeralTerm targetBoundary),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      (#0 : ArithmeticSemiterm Nat 1), #0]

/-- Releasing the outer binder yields the specialized four-witness predicate. -/
private theorem compactAdditiveNatListListSameRowsUniversalBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary : Nat) :
    Rewriting.free
        (compactAdditiveNatListListSameRowsUniversalBody
          tokenTable width tokenCount sourceBoundary targetBoundary) =
      compactAdditiveNatListListSameRowsRowAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary := by
  unfold compactAdditiveNatListListSameRowsUniversalBody
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactAdditiveNatListListSameRowsRowAtValuationFormula
  unfold compactNumericVerifierTaskBoundedRowsEqAtValuationFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp

/-- The closed same-rows formula is exactly count equality plus its universal. -/
theorem compactAdditiveNatListListSameRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat) :
    compactAdditiveNatListListSameRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount =
      (“!!(shortBinaryNumeralTerm targetCount) =
          !!(shortBinaryNumeralTerm sourceCount)” ⋏
        (compactAdditiveNatListListSameRowsUniversalBody
          tokenTable width tokenCount sourceBoundary targetBoundary).ballLT
          (shortBinaryNumeralTerm sourceCount)) := by
  unfold compactAdditiveNatListListSameRowsClosedFormula
  rw [compactAdditiveNatListListSameRowsDef_eq_namedDef]
  unfold compactAdditiveNatListListSameRowsNamedDef
  unfold compactAdditiveNatListListSameRowsUniversalBody
  simp [rewriting_ballLT, ← TransitiveRewriting.comp_app]
  congr 1
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    have hq (parameter : Fin 7) :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount]).q
            (#parameter.succ : ArithmeticSemiterm Nat 8) =
          Rew.bShift
            (![shortBinaryNumeralTerm tokenTable,
              shortBinaryNumeralTerm width,
              shortBinaryNumeralTerm tokenCount,
              shortBinaryNumeralTerm sourceBoundary,
              shortBinaryNumeralTerm sourceCount,
              shortBinaryNumeralTerm targetBoundary,
              shortBinaryNumeralTerm targetCount] parameter) := by
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
    fin_cases coordinate <;>
      simp only [Rew.comp_app, Rew.subst_bvar]
    · simpa using hq (0 : Fin 7)
    · simpa using hq (1 : Fin 7)
    · simpa using hq (2 : Fin 7)
    · simpa using hq (3 : Fin 7)
    · simpa using hq (5 : Fin 7)
    · simpa using hq (2 : Fin 7)
    · simp [Rew.subst_bvar]
    · simp [Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

private noncomputable def compactAdditiveNatListListSameRowsRowCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary index : Nat)
    (hrow : CompactNumericVerifierTaskBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        tokenCount index index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index zeroValuation)
      (Rewriting.free
        (compactAdditiveNatListListSameRowsUniversalBody
          tokenTable width tokenCount sourceBoundary targetBoundary)) := by
  rw [compactAdditiveNatListListSameRowsUniversalBody_free_alignment]
  exact compactNumericVerifierTaskBoundedRowsEqAtValuationExplicitHybridCertificate
    (extendValuation index zeroValuation)
    tokenTable width tokenCount sourceBoundary targetBoundary
      tokenCount index index
      (&0 : ValuationTerm) (&0 : ValuationTerm) (by
        simp) (by
        simp) hrow

/-- Construct the fully explicit certificate from the semantic same-rows graph. -/
noncomputable def compactAdditiveNatListListSameRowsExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat)
    (hsame : CompactAdditiveNatListListSameRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount) :
    HybridCertificate
      (compactAdditiveNatListListSameRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount) := by
  let countEq := closedEqCertificate targetCount sourceCount hsame.1
  let body := compactAdditiveNatListListSameRowsUniversalBody
    tokenTable width tokenCount sourceBoundary targetBoundary
  let branches := buildExplicitHybridUniversalBranches sourceCount
    (fun index hindex =>
      compactAdditiveNatListListSameRowsRowCertificate
        tokenTable width tokenCount sourceBoundary targetBoundary index
        (hsame.2 index hindex))
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
  exact .cast
    (compactAdditiveNatListListSameRowsClosedFormula_alignment
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount).symm
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction countEq
      universal)

#print axioms compactAdditiveNatListListSameRowsClosedFormula
#print axioms compactAdditiveNatListListSameRowsClosedFormula_alignment
#print axioms compactAdditiveNatListListSameRowsExplicitHybridCertificate

end FoundationCompactNumericListedDirectNatListListSameRowsExplicitHybridCertificate
