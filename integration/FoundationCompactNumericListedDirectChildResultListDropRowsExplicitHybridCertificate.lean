import integration.FoundationCompactNumericListedDirectChildResultListDropRows
import integration.FoundationCompactNumericListedDirectChildResultBoundedRowsEqExplicitHybridCertificate
import integration.FoundationCompactPAExplicitHybridUniversalBranches

/-!
# Explicit hybrid certificate for child-result-list prefix dropping

The two count facts are certified as arithmetic atoms.  Every branch of the
bounded universal reuses the checked row-equality constructor at the extended
valuation, so the branch index is represented by the actual valuation term
`&0`; it is never replaced by a false syntactic equality with a closed term.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectChildResultListDropRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectChildResultListDropRows
open FoundationCompactNumericListedDirectChildResultBoundedRowsEquality
open FoundationCompactNumericListedDirectChildResultBoundedRowsEqExplicitHybridCertificate
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

private noncomputable def closedAddEqCertificate
    (total left right : Nat) (heq : total = left + right) :
    HybridCertificate
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

private def compactNumericChildResultListDropRowsBody
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
      (#0 : ArithmeticSemiterm Nat 1)]

private def compactNumericChildResultListDropRowsRowAtValuationFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound consumed : Nat) : ValuationFormula :=
  compactNumericChildResultBoundedRowsEqAtValuationFormula
    tokenTable width tokenCount sourceBoundary targetBoundary valueBound
      (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
      (&0 : ValuationTerm)

private theorem compactNumericChildResultListDropRowsBody_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound consumed : Nat) :
    Rewriting.free
        (compactNumericChildResultListDropRowsBody
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound consumed) =
      compactNumericChildResultListDropRowsRowAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound consumed := by
  unfold compactNumericChildResultListDropRowsBody
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactNumericChildResultListDropRowsRowAtValuationFormula
  unfold compactNumericChildResultBoundedRowsEqAtValuationFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;>
    simp

private noncomputable def compactNumericChildResultListDropRowsBranchCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound consumed index : Nat)
    (hrow : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound (consumed + index) index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index zeroValuation)
      (Rewriting.free
        (compactNumericChildResultListDropRowsBody
          tokenTable width tokenCount sourceBoundary targetBoundary
            valueBound consumed)) := by
  rw [compactNumericChildResultListDropRowsBody_free_alignment]
  exact
    compactNumericChildResultBoundedRowsEqAtValuationExplicitHybridCertificate
      (extendValuation index zeroValuation)
      tokenTable width tokenCount sourceBoundary targetBoundary valueBound
      (consumed + index) index
      (‘!!(shortBinaryNumeralTerm consumed) + &0’ : ValuationTerm)
      (&0 : ValuationTerm) (by
        rw [termValue_arithmeticAdd]
        simp [termValue_shortBinaryNumeralTerm]) (by
        simp) hrow

/-- Close all ten coordinates of the prefix-drop predicate. -/
def compactNumericChildResultListDropRowsClosedFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound consumed : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultListDropRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm consumed]

theorem compactNumericChildResultListDropRowsClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound consumed : Nat) :
    compactNumericChildResultListDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount tableWidth valueBound consumed =
      (“!!(shortBinaryNumeralTerm consumed) ≤
          !!(shortBinaryNumeralTerm sourceCount)” ⋏
        (“!!(shortBinaryNumeralTerm sourceCount) =
            !!(shortBinaryNumeralTerm consumed) +
              !!(shortBinaryNumeralTerm targetCount)” ⋏
          (compactNumericChildResultListDropRowsBody
            tokenTable width tokenCount sourceBoundary targetBoundary
              valueBound consumed).ballLT
            (shortBinaryNumeralTerm targetCount))) := by
  unfold compactNumericChildResultListDropRowsClosedFormula
  unfold compactNumericChildResultListDropRowsDef
  simp [compactNumericChildResultListDropRowsBody,
    rewriting_ballLT,
    ← TransitiveRewriting.comp_app]
  congr 1
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    have hq (parameter : Fin 10) :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount,
            shortBinaryNumeralTerm tableWidth,
            shortBinaryNumeralTerm valueBound,
            shortBinaryNumeralTerm consumed]).q
            (#parameter.succ : ArithmeticSemiterm Nat 11) =
          Rew.bShift
            (![shortBinaryNumeralTerm tokenTable,
              shortBinaryNumeralTerm width,
              shortBinaryNumeralTerm tokenCount,
              shortBinaryNumeralTerm sourceBoundary,
              shortBinaryNumeralTerm sourceCount,
              shortBinaryNumeralTerm targetBoundary,
              shortBinaryNumeralTerm targetCount,
              shortBinaryNumeralTerm tableWidth,
              shortBinaryNumeralTerm valueBound,
              shortBinaryNumeralTerm consumed] parameter) := by
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
    fin_cases coordinate <;>
      simp only [Rew.comp_app, Rew.subst_bvar]
    · simpa using hq (0 : Fin 10)
    · simpa using hq (1 : Fin 10)
    · simpa using hq (2 : Fin 10)
    · simpa using hq (3 : Fin 10)
    · simpa using hq (5 : Fin 10)
    · simpa using hq (8 : Fin 10)
    · simpa [Rew.comp_app, Rew.subst_bvar] using
        congrArg
          (fun term : ArithmeticSemiterm Nat 1 =>
            (‘!!term + #0’ : ArithmeticSemiterm Nat 1))
          (hq (9 : Fin 10))
    · simp [Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

/-- Assemble the complete prefix-drop certificate from the semantic graph. -/
noncomputable def compactNumericChildResultListDropRowsExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound consumed : Nat)
    (hgraph : CompactNumericChildResultListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount tableWidth valueBound consumed) :
    HybridCertificate
      (compactNumericChildResultListDropRowsClosedFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount tableWidth valueBound consumed) := by
  rw [compactNumericChildResultListDropRowsClosedFormula_alignment]
  let countBound := closedLeCertificate consumed sourceCount hgraph.1
  let countEq := closedAddEqCertificate sourceCount consumed targetCount
    hgraph.2.1
  let body := compactNumericChildResultListDropRowsBody
    tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound consumed
  let branches := buildExplicitHybridUniversalBranches targetCount
    (fun index hindex =>
      compactNumericChildResultListDropRowsBranchCertificate
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound consumed index (hgraph.2.2 index hindex))
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm targetCount) body (by
      simpa [termValue_shortBinaryNumeralTerm] using branches)
  let universal : HybridCertificate
      (body.ballLT (shortBinaryNumeralTerm targetCount)) := .cast (by
        change (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm targetCount)) body) =
            body.ballLT (shortBinaryNumeralTerm targetCount)
        rw [termBoundedUniversal_eq_ball]
        rfl) direct
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction countBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction countEq
      universal)

private noncomputable def closedTermLeCertificate
    (leftTerm : ValuationTerm) (left right : Nat)
    (hleft : termValue zeroValuation leftTerm = left)
    (hle : left ≤ right) :
    HybridCertificate
      “!!leftTerm ≤ !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![leftTerm, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation leftTerm =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [hleft, termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![leftTerm, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation leftTerm <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [hleft, termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

private noncomputable def closedTermAddEqCertificate
    (total left right : Nat) (leftTerm : ValuationTerm)
    (hleft : termValue zeroValuation leftTerm = left)
    (heq : total = left + right) :
    HybridCertificate
      “!!(shortBinaryNumeralTerm total) =
        !!leftTerm + !!(shortBinaryNumeralTerm right)” := by
  exact .positiveAtomic zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm total,
      ‘!!leftTerm + !!(shortBinaryNumeralTerm right)’] (by
      change termValue zeroValuation (shortBinaryNumeralTerm total) =
        termValue zeroValuation
          ‘!!leftTerm + !!(shortBinaryNumeralTerm right)’
      simpa [hleft, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd] using heq)

private def compactNumericChildResultListDropRowsBodyAtValuationTerm
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (consumedTerm : ValuationTerm) : ArithmeticSemiformula Nat 1 :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultBoundedRowsEqDef.val) ⇜
    ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
      Rew.bShift (shortBinaryNumeralTerm width),
      Rew.bShift (shortBinaryNumeralTerm tokenCount),
      Rew.bShift (shortBinaryNumeralTerm sourceBoundary),
      Rew.bShift (shortBinaryNumeralTerm targetBoundary),
      Rew.bShift (shortBinaryNumeralTerm valueBound),
      ‘!!(Rew.bShift consumedTerm) + #0’,
      (#0 : ArithmeticSemiterm Nat 1)]

private def compactNumericChildResultListDropRowsRowAtValuationTermFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (consumedTerm : ValuationTerm) : ValuationFormula :=
  compactNumericChildResultBoundedRowsEqAtValuationFormula
    tokenTable width tokenCount sourceBoundary targetBoundary valueBound
      (‘!!(Rew.shift consumedTerm) + &0’ : ValuationTerm)
      (&0 : ValuationTerm)

private theorem
    compactNumericChildResultListDropRowsBodyAtValuationTerm_free_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound : Nat)
    (consumedTerm : ValuationTerm) :
    Rewriting.free
        (compactNumericChildResultListDropRowsBodyAtValuationTerm
          tokenTable width tokenCount sourceBoundary targetBoundary valueBound
            consumedTerm) =
      compactNumericChildResultListDropRowsRowAtValuationTermFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          consumedTerm := by
  unfold compactNumericChildResultListDropRowsBodyAtValuationTerm
  rw [rewriting_embeddedFormulaSubstitution]
  unfold compactNumericChildResultListDropRowsRowAtValuationTermFormula
  unfold compactNumericChildResultBoundedRowsEqAtValuationFormula
  congr 1
  funext coordinate
  fin_cases coordinate <;> simp

private noncomputable def
    compactNumericChildResultListDropRowsBranchAtValuationTermCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary valueBound
      consumed index : Nat)
    (consumedTerm : ValuationTerm)
    (hterm : termValue zeroValuation consumedTerm = consumed)
    (hrow : CompactNumericChildResultBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary valueBound
        (consumed + index) index) :
    CheckedHybridValuationBoundedFormulaCertificate
      (extendValuation index zeroValuation)
      (Rewriting.free
        (compactNumericChildResultListDropRowsBodyAtValuationTerm
          tokenTable width tokenCount sourceBoundary targetBoundary valueBound
            consumedTerm)) := by
  rw [compactNumericChildResultListDropRowsBodyAtValuationTerm_free_alignment]
  exact
    compactNumericChildResultBoundedRowsEqAtValuationExplicitHybridCertificate
      (extendValuation index zeroValuation)
      tokenTable width tokenCount sourceBoundary targetBoundary valueBound
      (consumed + index) index
      (‘!!(Rew.shift consumedTerm) + &0’ : ValuationTerm)
      (&0 : ValuationTerm) (by
        rw [termValue_arithmeticAdd, termValue_shift]
        change termValue zeroValuation consumedTerm + index = consumed + index
        rw [hterm]) (by simp) hrow

/-- Close the drop predicate with an arbitrary term representing `consumed`.
This preserves the exact syntax used by callers such as the leaf transition. -/
def compactNumericChildResultListDropRowsAtValuationFormula
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound : Nat)
    (consumedTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericChildResultListDropRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm sourceCount,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm targetCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound,
      consumedTerm]

theorem compactNumericChildResultListDropRowsAtValuationFormula_alignment
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound : Nat)
    (consumedTerm : ValuationTerm) :
    compactNumericChildResultListDropRowsAtValuationFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount tableWidth valueBound consumedTerm =
      (“!!consumedTerm ≤ !!(shortBinaryNumeralTerm sourceCount)” ⋏
        (“!!(shortBinaryNumeralTerm sourceCount) =
            !!consumedTerm + !!(shortBinaryNumeralTerm targetCount)” ⋏
          (compactNumericChildResultListDropRowsBodyAtValuationTerm
            tokenTable width tokenCount sourceBoundary targetBoundary
              valueBound consumedTerm).ballLT
            (shortBinaryNumeralTerm targetCount))) := by
  unfold compactNumericChildResultListDropRowsAtValuationFormula
  unfold compactNumericChildResultListDropRowsDef
  simp [compactNumericChildResultListDropRowsBodyAtValuationTerm,
    rewriting_ballLT, ← TransitiveRewriting.comp_app]
  congr 1
  apply Rewriting.smul_ext'
  apply Rew.ext
  · intro coordinate
    have hq (parameter : Fin 10) :
        (Rew.subst
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm sourceBoundary,
            shortBinaryNumeralTerm sourceCount,
            shortBinaryNumeralTerm targetBoundary,
            shortBinaryNumeralTerm targetCount,
            shortBinaryNumeralTerm tableWidth,
            shortBinaryNumeralTerm valueBound,
            consumedTerm]).q
            (#parameter.succ : ArithmeticSemiterm Nat 11) =
          Rew.bShift
            (![shortBinaryNumeralTerm tokenTable,
              shortBinaryNumeralTerm width,
              shortBinaryNumeralTerm tokenCount,
              shortBinaryNumeralTerm sourceBoundary,
              shortBinaryNumeralTerm sourceCount,
              shortBinaryNumeralTerm targetBoundary,
              shortBinaryNumeralTerm targetCount,
              shortBinaryNumeralTerm tableWidth,
              shortBinaryNumeralTerm valueBound,
              consumedTerm] parameter) := by
      rw [Rew.q_bvar_succ, Rew.subst_bvar]
    fin_cases coordinate <;>
      simp only [Rew.comp_app, Rew.subst_bvar]
    · simpa using hq (0 : Fin 10)
    · simpa using hq (1 : Fin 10)
    · simpa using hq (2 : Fin 10)
    · simpa using hq (3 : Fin 10)
    · simpa using hq (5 : Fin 10)
    · simpa using hq (8 : Fin 10)
    · simpa [Rew.comp_app, Rew.subst_bvar] using
        congrArg
          (fun term : ArithmeticSemiterm Nat 1 =>
            (‘!!term + #0’ : ArithmeticSemiterm Nat 1))
          (hq (9 : Fin 10))
    · simp [Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

/-- Explicit certificate for the arbitrary-term drop formula. -/
noncomputable def
    compactNumericChildResultListDropRowsAtValuationExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount tableWidth valueBound consumed : Nat)
    (consumedTerm : ValuationTerm)
    (hzero : termValue zeroValuation consumedTerm = consumed)
    (hgraph : CompactNumericChildResultListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount tableWidth valueBound consumed) :
    HybridCertificate
      (compactNumericChildResultListDropRowsAtValuationFormula
        tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount tableWidth valueBound consumedTerm) := by
  rw [compactNumericChildResultListDropRowsAtValuationFormula_alignment]
  let countBound := closedTermLeCertificate consumedTerm consumed sourceCount
    hzero hgraph.1
  let countEq := closedTermAddEqCertificate sourceCount consumed targetCount
    consumedTerm hzero hgraph.2.1
  let body := compactNumericChildResultListDropRowsBodyAtValuationTerm
    tokenTable width tokenCount sourceBoundary targetBoundary valueBound
      consumedTerm
  let branches := buildExplicitHybridUniversalBranches targetCount
    (fun index hindex =>
      compactNumericChildResultListDropRowsBranchAtValuationTermCertificate
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          consumed index consumedTerm hzero
          (hgraph.2.2 index hindex))
  let direct := CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
    (shortBinaryNumeralTerm targetCount) body (by
      simpa [termValue_shortBinaryNumeralTerm] using branches)
  let universal : HybridCertificate
      (body.ballLT (shortBinaryNumeralTerm targetCount)) := .cast (by
        change (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm targetCount)) body) =
            body.ballLT (shortBinaryNumeralTerm targetCount)
        rw [termBoundedUniversal_eq_ball]
        rfl) direct
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction countBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction countEq
      universal)

#print axioms compactNumericChildResultListDropRowsClosedFormula
#print axioms compactNumericChildResultListDropRowsClosedFormula_alignment
#print axioms compactNumericChildResultListDropRowsExplicitHybridCertificate
#print axioms compactNumericChildResultListDropRowsAtValuationFormula
#print axioms compactNumericChildResultListDropRowsAtValuationFormula_alignment
#print axioms compactNumericChildResultListDropRowsAtValuationExplicitHybridCertificate

end FoundationCompactNumericListedDirectChildResultListDropRowsExplicitHybridCertificate
