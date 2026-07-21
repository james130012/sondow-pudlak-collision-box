import integration.FoundationCompactNumericListedDirectAtomicRowEquality
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables
import integration.FoundationCompactPAExplicitHybridUniversalBranches
import integration.FoundationCompactPAFastArithmeticLeafRecognizer
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds

/-!
# Explicit hybrid certificate for direct atomic-row equality

This is the open-term form of `compactAdditiveAtomicRowEqDef`.  In
particular, the bit index remains a bound variable below the universal, so
the certificate is usable after an enclosing universal extends its valuation.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate

open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
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

abbrev AtomicRowEqHybridCertificate
    (valuation : Nat -> Nat) (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate valuation formula

/-- `compactAdditiveAtomicRowEqDef` instantiated by arbitrary valuation
terms. -/
def compactAdditiveAtomicRowEqAtValuationFormula
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveAtomicRowEqDef.val) ⇜
    ![tokenTableTerm, widthTerm, tokenCountTerm, leftTerm, rightTerm,
      otherLeftTerm, otherRightTerm]

def atomicRowEqLeftBitIndexTerm
    (widthTerm leftTerm : ValuationTerm) : ValuationTerm :=
  .func Language.Add.add ![Rew.shift (paMulTerm leftTerm widthTerm), &0]

def atomicRowEqOtherLeftBitIndexTerm
    (widthTerm otherLeftTerm : ValuationTerm) : ValuationTerm :=
  .func Language.Add.add ![
    Rew.shift (paMulTerm otherLeftTerm widthTerm), &0]

def atomicRowEqBitValueTerm
    (tokenTableTerm : ValuationTerm) : ValuationTerm :=
  Rew.shift tokenTableTerm

def atomicRowEqBitBody
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  binaryBitAtomAtTerms
      (.func Language.Add.add ![
        Rew.bShift (paMulTerm leftTerm widthTerm), #0])
      (Rew.bShift tokenTableTerm) 🡘
    binaryBitAtomAtTerms
      (.func Language.Add.add ![
        Rew.bShift (paMulTerm otherLeftTerm widthTerm), #0])
      (Rew.bShift tokenTableTerm)

def compactAdditiveAtomicRowEqExplicitFormula
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm) : ValuationFormula :=
  “!!leftTerm < !!tokenCountTerm” ⋏
    (“!!rightTerm = !!leftTerm + 1” ⋏
      (“!!otherLeftTerm < !!tokenCountTerm” ⋏
        (“!!otherRightTerm = !!otherLeftTerm + 1” ⋏
          (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
            otherLeftTerm).ballLT widthTerm)))

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
  exact rewriting_embeddedFormulaSubstitution rewriting operator.sentence terms

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

private theorem rewriting_iff
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (left right : LO.FirstOrder.ArithmeticSemiformula sourceVariables
      sourceArity) :
    rewriting ▹ (left 🡘 right) =
      ((rewriting ▹ left) 🡘 (rewriting ▹ right)) := by
  simp [LO.FirstOrder.Semiformula.iff_eq]

private theorem rewrite_binaryBitAtomAtTerms
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ Nat sourceArity Nat targetArity)
    (indexTerm valueTerm :
      LO.FirstOrder.ArithmeticSemiterm Nat sourceArity) :
    rewriting ▹ binaryBitAtomAtTerms indexTerm valueTerm =
      binaryBitAtomAtTerms (rewriting indexTerm) (rewriting valueTerm) := by
  rw [← membershipOperator_eq_binaryBitAtomAtTerms indexTerm valueTerm]
  rw [rewriting_formulaOperator rewriting
    LO.FirstOrder.Semiformula.Operator.Mem.mem]
  simp [membershipOperator_eq_binaryBitAtomAtTerms]

private theorem free_binaryBitAtomAtTerms
    (indexTerm valueTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    Rewriting.free (binaryBitAtomAtTerms indexTerm valueTerm) =
      binaryBitAtomAtTerms (Rew.free indexTerm) (Rew.free valueTerm) :=
  rewrite_binaryBitAtomAtTerms Rew.free indexTerm valueTerm

private theorem termValue_paAddTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paAddTerm left right) =
      termValue valuation left + termValue valuation right := by
  rw [← finiteCaseAddTerm_eq_paAddTerm]
  exact termValue_add valuation ![left, right]

private theorem termValue_paMulTerm
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation (paMulTerm left right) =
      termValue valuation left * termValue valuation right := by
  rw [← finiteCaseMulTerm_eq_paMulTerm]
  exact termValue_mul valuation ![left, right]

private theorem termValue_paOneTerm (valuation : Nat -> Nat) :
    termValue valuation paOneTerm = 1 := by
  unfold paOneTerm FoundationCompactBinaryNumeralTerm.arithmeticOneTerm
  exact termValue_one valuation ![]

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : LO.FirstOrder.ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ :
      LO.FirstOrder.ArithmeticSemiterm Variable boundArity) =
      LO.FirstOrder.Semiterm.func Language.Add.add ![left, right] := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_languageAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation
        (LO.FirstOrder.Semiterm.func Language.Add.add ![left, right]) =
      termValue valuation left + termValue valuation right :=
  termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem atomicRowEqBitBody_free
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm) :
    Rewriting.free
        (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm) =
      (binaryBitAtomAtTerms
          (atomicRowEqLeftBitIndexTerm widthTerm leftTerm)
          (atomicRowEqBitValueTerm tokenTableTerm) 🡘
        binaryBitAtomAtTerms
          (atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm)
          (atomicRowEqBitValueTerm tokenTableTerm)) := by
  unfold atomicRowEqBitBody atomicRowEqLeftBitIndexTerm
    atomicRowEqOtherLeftBitIndexTerm atomicRowEqBitValueTerm
  rw [rewriting_iff, free_binaryBitAtomAtTerms,
    free_binaryBitAtomAtTerms]
  simp [Rew.func]

/-- Exact syntax alignment with the original quoted atomic-row equality. -/
theorem compactAdditiveAtomicRowEqAtValuationFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm) :
    compactAdditiveAtomicRowEqAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
          otherRightTerm =
      compactAdditiveAtomicRowEqExplicitFormula
        tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
          otherRightTerm := by
  unfold compactAdditiveAtomicRowEqAtValuationFormula
  unfold compactAdditiveAtomicRowEqExplicitFormula
  unfold compactAdditiveAtomicRowEqDef
  simp [rewriting_ballLT,
    membershipOperator_eq_binaryBitAtomAtTerms]
  congr 1
  rw [rewrite_binaryBitAtomAtTerms,
    rewrite_binaryBitAtomAtTerms]
  unfold atomicRowEqBitBody
  simp [paMulTerm, Rew.q, Rew.subst_bvar,
    arithmeticAddTerm_eq_func]

private theorem atomicRowEqLeftBitIndex_value
    (valuation : Nat -> Nat) (widthTerm leftTerm : ValuationTerm)
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (atomicRowEqLeftBitIndexTerm widthTerm leftTerm) =
      termValue valuation leftTerm * termValue valuation widthTerm + bitIndex := by
  rw [atomicRowEqLeftBitIndexTerm, termValue_languageAdd,
    termValue_shift, termValue_paMulTerm, termValue_fvar,
    extendValuation_zero]

private theorem atomicRowEqOtherLeftBitIndex_value
    (valuation : Nat -> Nat) (widthTerm otherLeftTerm : ValuationTerm)
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm) =
      termValue valuation otherLeftTerm * termValue valuation widthTerm +
        bitIndex := by
  rw [atomicRowEqOtherLeftBitIndexTerm, termValue_languageAdd,
    termValue_shift, termValue_paMulTerm, termValue_fvar,
    extendValuation_zero]

private theorem atomicRowEqBitValue_value
    (valuation : Nat -> Nat) (tokenTableTerm : ValuationTerm)
    (bitIndex : Nat) :
    termValue (extendValuation bitIndex valuation)
        (atomicRowEqBitValueTerm tokenTableTerm) =
      termValue valuation tokenTableTerm := by
  rw [atomicRowEqBitValueTerm, termValue_shift]

private theorem binaryBitHybridVariablesTrue
    (indexTerm valueTerm : ValuationTerm) :
    indexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simpa [binaryBitAtValuationFormula, binaryBitLiteralAtTerms,
    binaryBitAtomAtTerms,
    FoundationCompactPAFastArithmeticLeafRecognizer.bitInstance] using
      bitInstance_argument_freeVariables_union_subset indexTerm valueTerm

private theorem binaryBitFalse_freeVariables_eq_true
    (indexTerm valueTerm : ValuationTerm) :
    (binaryBitAtValuationFormula false indexTerm valueTerm).freeVariables =
      (binaryBitAtValuationFormula true indexTerm valueTerm).freeVariables := by
  simp [binaryBitAtValuationFormula, binaryBitLiteralAtTerms]

noncomputable def atomicRowEqBitBranchCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (bitIndex : Nat)
    (hbit : (termValue valuation tokenTableTerm).testBit
        (termValue valuation leftTerm * termValue valuation widthTerm +
          bitIndex) =
      (termValue valuation tokenTableTerm).testBit
        (termValue valuation otherLeftTerm * termValue valuation widthTerm +
          bitIndex)) :
    AtomicRowEqHybridCertificate (extendValuation bitIndex valuation)
      (Rewriting.free
        (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm)) := by
  let branchValuation := extendValuation bitIndex valuation
  let leftIndexTerm := atomicRowEqLeftBitIndexTerm widthTerm leftTerm
  let otherIndexTerm := atomicRowEqOtherLeftBitIndexTerm widthTerm otherLeftTerm
  let valueTerm := atomicRowEqBitValueTerm tokenTableTerm
  let leftAtom := binaryBitAtomAtTerms leftIndexTerm valueTerm
  let otherAtom := binaryBitAtomAtTerms otherIndexTerm valueTerm
  let expected := (termValue valuation tokenTableTerm).testBit
    (termValue valuation leftTerm * termValue valuation widthTerm + bitIndex)
  have hleft : (termValue branchValuation valueTerm).testBit
      (termValue branchValuation leftIndexTerm) = expected := by
    simp [branchValuation, leftIndexTerm, valueTerm, expected,
      atomicRowEqLeftBitIndex_value, atomicRowEqBitValue_value]
  have hother : (termValue branchValuation valueTerm).testBit
      (termValue branchValuation otherIndexTerm) = expected := by
    rw [atomicRowEqOtherLeftBitIndex_value,
      atomicRowEqBitValue_value]
    simpa [expected] using hbit.symm
  have hleftVariables := binaryBitHybridVariablesTrue leftIndexTerm valueTerm
  have hotherVariables := binaryBitHybridVariablesTrue otherIndexTerm valueTerm
  if hexpected : expected = true then
      let leftTrue :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
          branchValuation leftIndexTerm valueTerm
          (by simpa [hexpected] using hleft) hleftVariables
      let otherTrue :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit true
          branchValuation otherIndexTerm valueTerm
          (by simpa [hexpected] using hother) hotherVariables
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼leftAtom) otherTrue
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := ∼otherAtom) leftTrue
      let source :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼leftAtom ⋎ otherAtom) ⋏ (∼otherAtom ⋎ leftAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        exact (atomicRowEqBitBody_free tokenTableTerm widthTerm leftTerm
          otherLeftTerm).symm) source
  else
      have hexpectedFalse : expected = false := by
        cases h : expected <;> simp_all
      have hleftVariablesFalse :
          leftIndexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
            (binaryBitAtValuationFormula false
              leftIndexTerm valueTerm).freeVariables := by
        rw [binaryBitFalse_freeVariables_eq_true]
        exact hleftVariables
      have hotherVariablesFalse :
          otherIndexTerm.freeVariables ∪ valueTerm.freeVariables ⊆
            (binaryBitAtValuationFormula false
              otherIndexTerm valueTerm).freeVariables := by
        rw [binaryBitFalse_freeVariables_eq_true]
        exact hotherVariables
      let leftFalse :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
          branchValuation leftIndexTerm valueTerm
          (by simpa [hexpectedFalse] using hleft) hleftVariablesFalse
      let otherFalse :=
        CheckedHybridValuationBoundedFormulaCertificate.binaryBit false
          branchValuation otherIndexTerm valueTerm
          (by simpa [hexpectedFalse] using hother) hotherVariablesFalse
      let forward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := otherAtom) leftFalse
      let backward :=
        CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := leftAtom) otherFalse
      let source :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          forward backward
      exact .cast (by
        change ((∼leftAtom ⋎ otherAtom) ⋏ (∼otherAtom ⋎ leftAtom)) = _
        rw [← LO.FirstOrder.Semiformula.iff_eq]
        exact (atomicRowEqBitBody_free tokenTableTerm widthTerm leftTerm
          otherLeftTerm).symm) source

noncomputable def atomicRowEqDirectHybridBranches
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          (termValue valuation leftTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          (termValue valuation otherLeftTerm * termValue valuation widthTerm +
            bitIndex)) :
    CheckedHybridValuationUniversalBranches valuation
      (atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm)
      (termValue valuation widthTerm) :=
  buildExplicitHybridUniversalBranches
    (termValue valuation widthTerm)
    (fun bitIndex hbitIndex =>
      atomicRowEqBitBranchCertificate valuation tokenTableTerm widthTerm
        leftTerm otherLeftTerm bitIndex (hbits bitIndex hbitIndex))

noncomputable def atomicRowEqUniversalCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm leftTerm otherLeftTerm : ValuationTerm)
    (hbits : ∀ bitIndex < termValue valuation widthTerm,
      (termValue valuation tokenTableTerm).testBit
          (termValue valuation leftTerm * termValue valuation widthTerm +
            bitIndex) =
        (termValue valuation tokenTableTerm).testBit
          (termValue valuation otherLeftTerm * termValue valuation widthTerm +
            bitIndex)) :
    AtomicRowEqHybridCertificate valuation
      ((atomicRowEqBitBody tokenTableTerm widthTerm leftTerm
        otherLeftTerm).ballLT widthTerm) := by
  let body := atomicRowEqBitBody tokenTableTerm widthTerm leftTerm otherLeftTerm
  let branches := atomicRowEqDirectHybridBranches valuation tokenTableTerm
    widthTerm leftTerm otherLeftTerm hbits
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      widthTerm body branches
  exact .cast (by
    change (∀⁰ termBoundedUniversalBody (Rew.bShift widthTerm) body) = _
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

noncomputable def strictCertificate
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hstrict : termValue valuation leftTerm < termValue valuation rightTerm) :
    AtomicRowEqHybridCertificate valuation “!!leftTerm < !!rightTerm” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hstrict
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def successorCertificate
    (valuation : Nat -> Nat) (leftTerm rightTerm : ValuationTerm)
    (hsuccessor : termValue valuation rightTerm = termValue valuation leftTerm + 1) :
    AtomicRowEqHybridCertificate valuation
      “!!rightTerm = !!leftTerm + 1” := by
  let sumTerm : ValuationTerm := ‘!!leftTerm + 1’
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    valuation Language.Eq.eq ![rightTerm, sumTerm] (by
      change termValue valuation rightTerm = termValue valuation sumTerm
      change termValue valuation rightTerm =
        termValue valuation (paAddTerm leftTerm (‘1’ : ValuationTerm))
      rw [termValue_paAddTerm, termValue_arithmeticOne]
      exact hsuccessor)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

/-- A fully explicit certificate at any valuation.  Every component of
`hgraph`, including the bounded bit family, is consumed directly. -/
noncomputable def compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
      otherRightTerm : ValuationTerm)
    (hgraph : CompactAdditiveAtomicRowEq
      (termValue valuation tokenTableTerm)
      (termValue valuation widthTerm)
      (termValue valuation tokenCountTerm)
      (termValue valuation leftTerm)
      (termValue valuation rightTerm)
      (termValue valuation otherLeftTerm)
      (termValue valuation otherRightTerm)) :
    AtomicRowEqHybridCertificate valuation
      (compactAdditiveAtomicRowEqAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm otherLeftTerm
          otherRightTerm) :=
  .cast
    (compactAdditiveAtomicRowEqAtValuationFormula_alignment
      tokenTableTerm widthTerm tokenCountTerm leftTerm rightTerm
      otherLeftTerm otherRightTerm).symm
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (strictCertificate valuation leftTerm tokenCountTerm hgraph.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (successorCertificate valuation leftTerm rightTerm hgraph.2.1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (strictCertificate valuation otherLeftTerm tokenCountTerm
            hgraph.2.2.1)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (successorCertificate valuation otherLeftTerm otherRightTerm
              hgraph.2.2.2.1)
            (atomicRowEqUniversalCertificate valuation tokenTableTerm widthTerm
              leftTerm otherLeftTerm hgraph.2.2.2.2)))))

def zeroValuation : Nat -> Nat := fun _ => 0

/-- The closed seven-coordinate instance of the atomic-row equality. -/
def compactAdditiveAtomicRowEqClosedFormula
    (tokenTable width tokenCount left right otherLeft otherRight : Nat) :
    ValuationFormula :=
  compactAdditiveAtomicRowEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount) (shortBinaryNumeralTerm left)
    (shortBinaryNumeralTerm right) (shortBinaryNumeralTerm otherLeft)
    (shortBinaryNumeralTerm otherRight)

/-- Closed wrapper around the term-generic certificate. -/
noncomputable def compactAdditiveAtomicRowEqExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount left right otherLeft otherRight : Nat)
    (hgraph : CompactAdditiveAtomicRowEq tokenTable width tokenCount
      left right otherLeft otherRight) :
    AtomicRowEqHybridCertificate zeroValuation
      (compactAdditiveAtomicRowEqClosedFormula
        tokenTable width tokenCount left right otherLeft otherRight) := by
  unfold compactAdditiveAtomicRowEqClosedFormula
  apply compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
  simpa only [termValue_shortBinaryNumeralTerm] using hgraph

#print axioms compactAdditiveAtomicRowEqAtValuationFormula
#print axioms compactAdditiveAtomicRowEqAtValuationFormula_alignment
#print axioms compactAdditiveAtomicRowEqAtValuationExplicitHybridCertificate
#print axioms compactAdditiveAtomicRowEqClosedFormula
#print axioms compactAdditiveAtomicRowEqExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectAtomicRowEqualityExplicitHybridCertificate
