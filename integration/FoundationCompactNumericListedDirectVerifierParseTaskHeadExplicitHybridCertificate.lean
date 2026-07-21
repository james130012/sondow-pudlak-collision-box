import integration.FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
import integration.FoundationCompactPAExplicitWitnessExsClosureBuilder
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

/-!
# Explicit hybrid certificate for the initial verifier parse task

Every one of the fourteen bounded row coordinates is installed as an explicit
short-binary witness.  The terminal bounded formula is assembled from atomic,
binary-length, fixed-width-entry, and zero-branch universal certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate

open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectBoundedVectorQuantifier
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskBoundedHeadFormula
open FoundationCompactNumericListedDirectVerifierParseTaskHeadFormula
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryLengthValuationContextCompiler
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder.ExplicitWitnessHybridSigmaOnePayload
open FoundationCompactPAExplicitWitnessExsClosureBuilder
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof

abbrev HybridCertificate :=
  CheckedHybridValuationBoundedFormulaCertificate

def zeroValuation : Nat -> Nat := fun _ => 0

private theorem arithmeticRewritingApp_congr
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

private theorem rewriting_termOperator
    {sourceVariables targetVariables : Type*}
    {operatorArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (operator : Semiterm.Operator ℒₒᵣ operatorArity)
    (terms : Fin operatorArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting (operator.operator terms) =
      operator.operator (rewriting ∘ terms) := by
  unfold Semiterm.Operator.operator
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting (Rew.subst terms (Rew.emb operator.term)) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            sourceVariables operatorArity)) operator.term := by
      rw [Rew.comp_app, Rew.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty operatorArity
            targetVariables operatorArity)) operator.term := by
      rw [hcomposition]
    _ = Rew.subst (rewriting ∘ terms) (Rew.emb operator.term) := by
      rw [Rew.comp_app]

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

private def localVariable (coordinate : Fin 14) : Fin (5 + 14) :=
  Fin.castAdd 5 coordinate

private def globalVariable (coordinate : Fin 5) : Fin (5 + 14) :=
  Fin.natAdd 14 coordinate

private def arithmeticNumeral (value : Nat) :
    ArithmeticSemiterm Empty (5 + 14) :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private def arithmeticEq
    (left right : ArithmeticSemiterm Empty (5 + 14)) :
    ArithmeticSemiformula Empty (5 + 14) :=
  Semiformula.Operator.Eq.eq.operator ![left, right]

private def parseTaskHeadTerms :
    Fin 19 -> ArithmeticSemiterm Empty (5 + 14) :=
  ![(#(globalVariable 0) : ArithmeticSemiterm Empty (5 + 14)),
    #(globalVariable 1), #(globalVariable 2), #(globalVariable 3),
    #(globalVariable 4),
    #(localVariable 0), #(localVariable 1), #(localVariable 2),
    #(localVariable 3), #(localVariable 4), #(localVariable 5),
    #(localVariable 6), #(localVariable 7), #(localVariable 8),
    #(localVariable 9), #(localVariable 10), #(localVariable 11),
    #(localVariable 12), #(localVariable 13)]

private theorem parseTaskHeadTerms_eq_explicit :
    parseTaskHeadTerms =
      ![(#14 : ArithmeticSemiterm Empty 19), #15, #16, #17, #18,
        #0, #1, #2, #3, #4, #5, #6, #7, #8, #9, #10, #11, #12,
        #13] := by
  funext index
  fin_cases index <;>
    simp [parseTaskHeadTerms, localVariable, globalVariable]

/-- A public copy of the exact private matrix used by the source definition. -/
def compactNumericVerifierParseTaskHeadRawCore :
    ArithmeticSemiformula Empty (5 + 14) :=
  [compactNumericVerifierTaskBoundedHeadDef.val ⇜ parseTaskHeadTerms,
    arithmeticEq (#(localVariable 2)) (arithmeticNumeral 10),
    arithmeticEq (#(localVariable 4)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 7)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 9)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 11)) (arithmeticNumeral 0),
    arithmeticEq (#(localVariable 12)) (arithmeticNumeral 0)].conj₂

theorem compactNumericVerifierParseTaskHeadDef_val_eq_boundedVector :
    compactNumericVerifierParseTaskHeadDef.val =
      boundedVectorBExs (#4 : ArithmeticSemiterm Empty 5) 14
        compactNumericVerifierParseTaskHeadRawCore := by
  rfl

/-- The original five-coordinate predicate closed by short binary numerals. -/
def compactNumericVerifierParseTaskHeadClosedFormula
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierParseTaskHeadDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm taskBoundary,
      shortBinaryNumeralTerm valueBound]

private def normalizedGlobalSubstitutionQpow
    (terms : Fin 5 -> ValuationTerm) :
    (k : Nat) -> Rew ℒₒᵣ Empty (5 + k) Nat k
  | 0 => (Rew.subst terms).comp
      (Rew.emb : Rew ℒₒᵣ Empty 5 Nat 5)
  | k + 1 => (normalizedGlobalSubstitutionQpow terms k).q

/-- The private matrix after closing only the five public coordinates. -/
def compactNumericVerifierParseTaskHeadOpenWitnessMatrix
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    ArithmeticSemiformula Nat 14 :=
  normalizedGlobalSubstitutionQpow
      ![shortBinaryNumeralTerm tokenTable,
        shortBinaryNumeralTerm width,
        shortBinaryNumeralTerm tokenCount,
        shortBinaryNumeralTerm taskBoundary,
        shortBinaryNumeralTerm valueBound] 14 ▹
    compactNumericVerifierParseTaskHeadRawCore

def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

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
  | succ k ih =>
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
        _ = term := ih _

/-- A normalized closed specialization of the shared bounded-vector binder. -/
def explicitClosedBoundedVectorFormula (bound : ValuationTerm) :
    (k : Nat) -> ArithmeticSemiformula Nat k -> ValuationFormula
  | 0, body => body
  | k + 1, body =>
      explicitClosedBoundedVectorFormula bound k
        (body.bexsLTSucc (closedShift k bound))

@[simp] private theorem rewriting_bexsLTSucc
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (bound : ArithmeticSemiterm sourceVariables sourceArity)
    (body : ArithmeticSemiformula sourceVariables (sourceArity + 1)) :
    rewriting ▹ body.bexsLTSucc bound =
      (rewriting.q ▹ body).bexsLTSucc (rewriting bound) := by
  simp [LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT]

private def shiftedValueBoundVariable :
    (depth : Nat) -> Fin (5 + depth)
  | 0 => 4
  | depth + 1 => (shiftedValueBoundVariable depth).succ

@[simp] private theorem shiftedValueBoundVariable_val (depth : Nat) :
    (shiftedValueBoundVariable depth).val = 4 + depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      simp [shiftedValueBoundVariable, ih]
      omega

private theorem liftPast_valueBound (depth : Nat) :
    liftPast depth (#4 : ArithmeticSemiterm Empty 5) =
      (#(shiftedValueBoundVariable depth) :
        ArithmeticSemiterm Empty (5 + depth)) := by
  unfold liftPast
  rw [Rew.subst_bvar]
  congr 1
  apply Fin.ext
  simp

private def qClosedShift :
    (depth : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat (0 + depth)
  | 0, term => term
  | depth + 1, term => Rew.bShift (qClosedShift depth term)

@[simp] private theorem qpow_substitution_valueBound
    (terms : Fin 5 -> ValuationTerm) (depth : Nat) :
    (Rew.subst terms).qpow depth
        (#(shiftedValueBoundVariable depth) :
          ArithmeticSemiterm Nat (5 + depth)) =
      qClosedShift depth (terms 4) := by
  induction depth with
  | zero =>
      simp [shiftedValueBoundVariable, qClosedShift]
  | succ depth ih =>
      rw [Rew.qpow_succ]
      change ((Rew.subst terms).qpow depth).q
          (#(shiftedValueBoundVariable depth).succ) = _
      rw [Rew.q_bvar_succ, ih]
      rfl

@[simp] private theorem normalizedGlobalSubstitutionQpow_valueBound
    (terms : Fin 5 -> ValuationTerm) (depth : Nat) :
    normalizedGlobalSubstitutionQpow terms depth
        (#(shiftedValueBoundVariable depth) :
          ArithmeticSemiterm Empty (5 + depth)) =
      closedShift depth (terms 4) := by
  induction depth with
  | zero =>
      simp [normalizedGlobalSubstitutionQpow,
        shiftedValueBoundVariable, closedShift,
        Rew.comp_app, Rew.subst_bvar]
  | succ depth ih =>
      change (normalizedGlobalSubstitutionQpow terms depth).q
          (#(shiftedValueBoundVariable depth).succ) = _
      rw [Rew.q_bvar_succ, ih]
      rfl

private theorem closedMatrixRewriting_eq_openWitnessMatrix
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    normalizedGlobalSubstitutionQpow
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm valueBound] 14 ▹
      compactNumericVerifierParseTaskHeadRawCore =
      compactNumericVerifierParseTaskHeadOpenWitnessMatrix
        tokenTable width tokenCount taskBoundary valueBound := by
  rfl

private theorem parseTaskHeadBoundedVectorRewriting_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    (k : Nat) ->
    (body : ArithmeticSemiformula Empty (5 + k)) ->
    (Rewriting.emb (ξ := Nat)
        (boundedVectorBExs
          (#4 : ArithmeticSemiterm Empty 5) k body)) ⇜
      ![shortBinaryNumeralTerm tokenTable,
        shortBinaryNumeralTerm width,
        shortBinaryNumeralTerm tokenCount,
        shortBinaryNumeralTerm taskBoundary,
        shortBinaryNumeralTerm valueBound] =
      explicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm valueBound) k
        (normalizedGlobalSubstitutionQpow
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm taskBoundary,
            shortBinaryNumeralTerm valueBound] k ▹
          body)
  | 0, body => by
      simp only [boundedVectorBExs,
        explicitClosedBoundedVectorFormula,
        normalizedGlobalSubstitutionQpow]
      rw [TransitiveRewriting.comp_app]
  | k + 1, body => by
      simp only [boundedVectorBExs,
        explicitClosedBoundedVectorFormula]
      rw [parseTaskHeadBoundedVectorRewriting_alignment
        tokenTable width tokenCount taskBoundary valueBound k]
      congr 1
      rw [rewriting_bexsLTSucc]
      congr 1
      rw [liftPast_valueBound,
        normalizedGlobalSubstitutionQpow_valueBound]
      rfl

/-- Strict formula alignment with the actual source definition. -/
theorem compactNumericVerifierParseTaskHeadClosedFormula_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    compactNumericVerifierParseTaskHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound =
      explicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm valueBound) 14
        (compactNumericVerifierParseTaskHeadOpenWitnessMatrix
          tokenTable width tokenCount taskBoundary valueBound) := by
  unfold compactNumericVerifierParseTaskHeadClosedFormula
  rw [compactNumericVerifierParseTaskHeadDef_val_eq_boundedVector]
  rw [parseTaskHeadBoundedVectorRewriting_alignment
    tokenTable width tokenCount taskBoundary valueBound 14]
  exact congrArg
    (explicitClosedBoundedVectorFormula
      (shortBinaryNumeralTerm valueBound) 14)
    (closedMatrixRewriting_eq_openWitnessMatrix
      tokenTable width tokenCount taskBoundary valueBound)

private def explicitCoordinateValues
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) : Fin 14 -> Nat :=
  ![coordinates.start, coordinates.finish, coordinates.tag,
    coordinates.gammaFinish, coordinates.gammaCount,
    coordinates.gammaBoundary, coordinates.firstFinish,
    coordinates.firstCount, coordinates.secondFinish,
    coordinates.secondCount, coordinates.witnessFinish,
    coordinates.witnessCount, coordinates.suffixCount,
    sizeWitness.gammaBoundarySize]

private theorem shortBinarySubstitution_bexsLTSucc_tail
    {k : Nat}
    (bound : ValuationTerm)
    (body : ArithmeticSemiformula Nat (k + 1))
    (values : Fin (k + 1) -> Nat) :
    (body.bexsLTSucc (closedShift k bound)) ⇜
        (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ)) =
      (explicitWitnessBodyAfterTail body values).bexsLTSucc bound := by
  unfold LO.FirstOrder.Semiformula.bexsLTSucc
  unfold LO.FirstOrder.Semiformula.bexsLT
  have hbound :
      Rew.subst (fun index : Fin k =>
          shortBinaryNumeralTerm (values index.succ))
          (closedShift k bound) = bound := by
    exact substitute_closedShift _ bound
  simp [explicitWitnessBodyAfterTail, hbound]

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticMulTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left * !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Mul.mul ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Mul.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticMul
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left * !!right’ =
      termValue valuation left * termValue valuation right := by
  rw [arithmeticMulTerm_eq_func]
  exact termValue_mul valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation arithmeticZeroTerm = 0 := by
  unfold arithmeticZeroTerm
  exact termValue_zero valuation ![]

private noncomputable def closedEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) =
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using heq)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

private def unaryNumeralTerm (value : Nat) : ValuationTerm :=
  Semiterm.Operator.operator
    (Semiterm.Operator.numeral ℒₒᵣ value) ![]

private theorem termValue_unaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (unaryNumeralTerm value) = value := by
  unfold termValue unaryNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] valuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simpa using
    (LO.FirstOrder.Structure.numeral_eq_numeral
      (L := ℒₒᵣ) (M := Nat) value)

private noncomputable def closedFixedNumeralEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) = !!(unaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, unaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) =
        termValue zeroValuation (unaryNumeralTerm right)
      simpa only [termValue_shortBinaryNumeralTerm,
        termValue_unaryNumeralTerm] using heq)
  exact .cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm direct

noncomputable def closedLtCertificate
    (left right : Nat) (hlt : left < right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right)” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
      change termValue zeroValuation (shortBinaryNumeralTerm left) <
        termValue zeroValuation (shortBinaryNumeralTerm right)
      simpa [termValue_shortBinaryNumeralTerm] using hlt)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

noncomputable def closedLeCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) ≤
        !!(shortBinaryNumeralTerm right)” := by
  if heq : left = right then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) =
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using heq)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : left < right := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation (shortBinaryNumeralTerm right)
        simpa [termValue_shortBinaryNumeralTerm] using hlt)
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

def compactAdditiveTokenCellClosedFormula
    (tokenTable width tokenCount cursor value next : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm cursor,
      shortBinaryNumeralTerm value,
      shortBinaryNumeralTerm next]

def compactAdditiveTokenCellPartsFormula
    (tokenTable width tokenCount cursor value next : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm cursor) <
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
    (“!!(shortBinaryNumeralTerm next) =
        !!(shortBinaryNumeralTerm cursor) + 1” ⋏
      compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm cursor)
        (shortBinaryNumeralTerm value))

theorem compactAdditiveTokenCellClosedFormula_alignment
    (tokenTable width tokenCount cursor value next : Nat) :
    compactAdditiveTokenCellClosedFormula
        tokenTable width tokenCount cursor value next =
      compactAdditiveTokenCellPartsFormula
        tokenTable width tokenCount cursor value next := by
  unfold compactAdditiveTokenCellClosedFormula
  unfold compactAdditiveTokenCellPartsFormula
  unfold compactAdditiveTokenCellDef
  unfold compactFixedWidthEntryAtValuationFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def compactAdditiveTokenCellExplicitHybridCertificate
    (tokenTable width tokenCount cursor value next : Nat)
    (hcell : CompactAdditiveTokenCell
      tokenTable width tokenCount cursor value next) :
    HybridCertificate zeroValuation
      (compactAdditiveTokenCellClosedFormula
        tokenTable width tokenCount cursor value next) := by
  let successorTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm cursor) + 1’
  let successor := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm next, successorTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm next) =
        termValue zeroValuation successorTerm
      simpa [successorTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticOne] using hcell.2.1)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLtCertificate cursor tokenCount hcell.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (.cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm successor)
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm cursor)
        (shortBinaryNumeralTerm value) (by
          simpa [termValue_shortBinaryNumeralTerm] using hcell.2.2)))
  exact .cast
    (compactAdditiveTokenCellClosedFormula_alignment
      tokenTable width tokenCount cursor value next).symm parts

noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate zeroValuation “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (LO.FirstOrder.Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

def compactAdditiveListHeaderClosedFormula
    (tokenTable width tokenCount start count bodyStart : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm count,
      shortBinaryNumeralTerm bodyStart]

def compactAdditiveListHeaderPartsFormula
    (tokenTable width tokenCount start count bodyStart : Nat) :
    ValuationFormula :=
  compactAdditiveTokenCellClosedFormula
      tokenTable width tokenCount start count bodyStart ⋏
    “!!(shortBinaryNumeralTerm bodyStart) +
        !!(shortBinaryNumeralTerm count) ≤
      !!(shortBinaryNumeralTerm tokenCount)”

theorem compactAdditiveListHeaderClosedFormula_alignment
    (tokenTable width tokenCount start count bodyStart : Nat) :
    compactAdditiveListHeaderClosedFormula
        tokenTable width tokenCount start count bodyStart =
      compactAdditiveListHeaderPartsFormula
        tokenTable width tokenCount start count bodyStart := by
  unfold compactAdditiveListHeaderClosedFormula
  unfold compactAdditiveListHeaderPartsFormula
  unfold compactAdditiveListHeaderDef
  unfold compactAdditiveTokenCellClosedFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def compactAdditiveListHeaderExplicitHybridCertificate
    (tokenTable width tokenCount start count bodyStart : Nat)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart) :
    HybridCertificate zeroValuation
      (compactAdditiveListHeaderClosedFormula
        tokenTable width tokenCount start count bodyStart) := by
  let leftTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellExplicitHybridCertificate
      tokenTable width tokenCount start count bodyStart hheader.1)
    (valuationLeCertificate leftTerm
      (shortBinaryNumeralTerm tokenCount) (by
        simpa [leftTerm, termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd] using hheader.2))
  exact .cast
    (compactAdditiveListHeaderClosedFormula_alignment
      tokenTable width tokenCount start count bodyStart).symm parts

def compactAdditiveTokenCellAtValuationFormula
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveTokenCellDef.val) ⇜
    ![tokenTableTerm, widthTerm, tokenCountTerm, cursorTerm, valueTerm, nextTerm]

private def compactAdditiveTokenCellAtValuationPartsFormula
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) : ValuationFormula :=
  “!!cursorTerm < !!tokenCountTerm” ⋏
    (“!!nextTerm = !!cursorTerm + 1” ⋏
      compactFixedWidthEntryAtValuationFormula
        tokenTableTerm widthTerm cursorTerm valueTerm)

theorem compactAdditiveTokenCellAtValuationFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm) :
    compactAdditiveTokenCellAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm =
      compactAdditiveTokenCellAtValuationPartsFormula
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm := by
  unfold compactAdditiveTokenCellAtValuationFormula
  unfold compactAdditiveTokenCellAtValuationPartsFormula
  unfold compactAdditiveTokenCellDef
  unfold compactFixedWidthEntryAtValuationFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

noncomputable def
    compactAdditiveTokenCellAtValuationExplicitHybridCertificate
    (tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm :
      ValuationTerm)
    (hcell : CompactAdditiveTokenCell
      (termValue zeroValuation tokenTableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation tokenCountTerm)
      (termValue zeroValuation cursorTerm)
      (termValue zeroValuation valueTerm)
      (termValue zeroValuation nextTerm)) :
    HybridCertificate zeroValuation
      (compactAdditiveTokenCellAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm) := by
  let successorTerm : ValuationTerm := ‘!!cursorTerm + 1’
  let cursorLt := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt ![cursorTerm, tokenCountTerm] hcell.1
  let successor := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![nextTerm, successorTerm] (by
      change termValue zeroValuation nextTerm =
        termValue zeroValuation successorTerm
      simpa [successorTerm, termValue_arithmeticAdd,
        termValue_arithmeticOne] using hcell.2.1)
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (.cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm cursorLt)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (.cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm successor)
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation tokenTableTerm widthTerm cursorTerm valueTerm hcell.2.2))
  exact .cast
    (compactAdditiveTokenCellAtValuationFormula_alignment
      tokenTableTerm widthTerm tokenCountTerm cursorTerm valueTerm nextTerm).symm
    parts

private def compactAdditiveListHeaderAtValuationFormula
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
    ![tokenTableTerm, widthTerm, tokenCountTerm, startTerm, countTerm,
      bodyStartTerm]

private def compactAdditiveListHeaderAtValuationPartsFormula
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm) : ValuationFormula :=
  compactAdditiveTokenCellAtValuationFormula
      tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm ⋏
    “!!bodyStartTerm + !!countTerm ≤ !!tokenCountTerm”

private theorem compactAdditiveListHeaderAtValuationFormula_alignment
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm) :
    compactAdditiveListHeaderAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm =
      compactAdditiveListHeaderAtValuationPartsFormula
        tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
          bodyStartTerm := by
  unfold compactAdditiveListHeaderAtValuationFormula
  unfold compactAdditiveListHeaderAtValuationPartsFormula
  unfold compactAdditiveListHeaderDef
  unfold compactAdditiveTokenCellAtValuationFormula
  simp [Rew.comp_app, rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;> simp [Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

private noncomputable def
    compactAdditiveListHeaderAtValuationExplicitHybridCertificate
    (tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm :
      ValuationTerm)
    (hheader : CompactAdditiveListHeader
      (termValue zeroValuation tokenTableTerm)
      (termValue zeroValuation widthTerm)
      (termValue zeroValuation tokenCountTerm)
      (termValue zeroValuation startTerm)
      (termValue zeroValuation countTerm)
      (termValue zeroValuation bodyStartTerm)) :
    HybridCertificate zeroValuation
      (compactAdditiveListHeaderAtValuationFormula
        tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
          bodyStartTerm) := by
  let leftTerm : ValuationTerm := ‘!!bodyStartTerm + !!countTerm’
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      tokenTableTerm widthTerm tokenCountTerm startTerm countTerm bodyStartTerm
        hheader.1)
    (valuationLeCertificate leftTerm tokenCountTerm (by
      simpa [leftTerm, termValue_arithmeticAdd] using hheader.2))
  exact .cast
    (compactAdditiveListHeaderAtValuationFormula_alignment
      tokenTableTerm widthTerm tokenCountTerm startTerm countTerm
        bodyStartTerm).symm parts

private noncomputable def closedBoundGuardCertificate
    (left right : Nat) (hle : left ≤ right) :
    HybridCertificate zeroValuation
      “!!(shortBinaryNumeralTerm left) <
        !!(shortBinaryNumeralTerm right) + 1” := by
  let direct := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left,
      ‘!!(shortBinaryNumeralTerm right) + 1’] (by
        change termValue zeroValuation (shortBinaryNumeralTerm left) <
          termValue zeroValuation
            ‘!!(shortBinaryNumeralTerm right) + 1’
        simp only [termValue_shortBinaryNumeralTerm,
          termValue_arithmeticAdd, termValue_arithmeticOne]
        omega)
  exact .cast
    (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

def compactAdditiveNatListSliceClosedFormula
    (tokenTable width tokenCount start count finish : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveNatListSliceDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm count,
      shortBinaryNumeralTerm finish]

private def compactAdditiveNatListSliceWitnessBody
    (tokenTable width tokenCount start count finish : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (shortBinaryNumeralTerm start),
        Rew.bShift (shortBinaryNumeralTerm count),
        (#0 : ArithmeticSemiterm Nat 1)]) ⋏
      “!!(Rew.bShift (shortBinaryNumeralTerm finish)) =
        #0 + !!(Rew.bShift (shortBinaryNumeralTerm count))”)

private theorem compactAdditiveNatListSliceClosedFormula_alignment
    (tokenTable width tokenCount start count finish : Nat) :
    compactAdditiveNatListSliceClosedFormula
        tokenTable width tokenCount start count finish =
      ∃⁰ compactAdditiveNatListSliceWitnessBody
        tokenTable width tokenCount start count finish := by
  unfold compactAdditiveNatListSliceClosedFormula
  unfold compactAdditiveNatListSliceWitnessBody
  unfold compactAdditiveNatListSliceDef
  simp [Rew.comp_app, LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private theorem zeroNatListSliceData
    {tokenTable width tokenCount start finish : Nat}
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start 0 finish) :
    CompactAdditiveListHeader tokenTable width tokenCount
        start 0 (start + 1) ∧
      finish = start + 1 := by
  rcases hslice with ⟨bodyStart, _hbodyBound, hheader, hfinish⟩
  have hbodyStart : bodyStart = start + 1 := hheader.1.2.1
  subst bodyStart
  simpa using ⟨hheader, hfinish⟩

/-- Explicit checked certificate for an arbitrary additive natural-number
list slice.  The caller supplies the concrete body-start witness, its checked
header, and the exact endpoint equation; no existential witness is selected
from semantic truth. -/
noncomputable def compactAdditiveNatListSliceExplicitHybridCertificate
    (tokenTable width tokenCount start count finish bodyStart : Nat)
    (hbodyBound : bodyStart ≤ tokenCount)
    (hheader : CompactAdditiveListHeader
      tokenTable width tokenCount start count bodyStart)
    (hfinish : finish = bodyStart + count) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListSliceClosedFormula
        tokenTable width tokenCount start count finish) := by
  rw [compactAdditiveNatListSliceClosedFormula_alignment]
  refine .existsWitness
    (compactAdditiveNatListSliceWitnessBody
      tokenTable width tokenCount start count finish) bodyStart ?_
  let endpointTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm count)’
  let endpoint := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm finish, endpointTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm finish) =
        termValue zeroValuation endpointTerm
      simpa [endpointTerm, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd] using hfinish)
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedBoundGuardCertificate bodyStart tokenCount hbodyBound)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveListHeaderExplicitHybridCertificate
        tokenTable width tokenCount start count bodyStart hheader)
      (.cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm endpoint))
  exact .cast (by
    simp [Rew.comp_app, compactAdditiveNatListSliceWitnessBody,
      compactAdditiveListHeaderClosedFormula,
      rewriting_embeddedFormulaSubstitution,
      ← TransitiveRewriting.comp_app]
    constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, Rew.q_bvar_succ]
      · intro coordinate
        exact Empty.elim coordinate
    · rfl) post

/-- Derive the explicit slice certificate from a concrete bounded slice. -/
noncomputable def compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
    (tokenTable width tokenCount start count finish : Nat)
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start count finish) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListSliceClosedFormula
        tokenTable width tokenCount start count finish) := by
  let bodyStart := Classical.choose hslice
  have hbody := Classical.choose_spec hslice
  exact compactAdditiveNatListSliceExplicitHybridCertificate
    tokenTable width tokenCount start count finish bodyStart
    hbody.1 hbody.2.1 hbody.2.2

private noncomputable def compactAdditiveNatListSliceZeroExplicitHybridCertificate
    (tokenTable width tokenCount start finish : Nat)
    (hslice : CompactAdditiveNatListSlice
      tokenTable width tokenCount start 0 finish) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListSliceClosedFormula
        tokenTable width tokenCount start 0 finish) := by
  let bodyStart := start + 1
  have hdata := zeroNatListSliceData hslice
  rw [compactAdditiveNatListSliceClosedFormula_alignment]
  refine .existsWitness
    (compactAdditiveNatListSliceWitnessBody
      tokenTable width tokenCount start 0 finish) bodyStart ?_
  let endpointTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm bodyStart) +
      !!(shortBinaryNumeralTerm 0)’
  let endpoint := CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm finish, endpointTerm] (by
      change termValue zeroValuation (shortBinaryNumeralTerm finish) =
        termValue zeroValuation endpointTerm
      simpa [endpointTerm, bodyStart, termValue_shortBinaryNumeralTerm,
        termValue_arithmeticAdd, termValue_arithmeticZero] using hdata.2)
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedBoundGuardCertificate bodyStart tokenCount (by
      exact Nat.le_trans (Nat.le_add_right _ 0) hdata.1.2))
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveListHeaderExplicitHybridCertificate
        tokenTable width tokenCount start 0 bodyStart hdata.1)
      (.cast (LO.FirstOrder.Semiformula.Operator.eq_def _ _).symm endpoint))
  exact .cast (by
    simp [Rew.comp_app, compactAdditiveNatListSliceWitnessBody,
      compactAdditiveListHeaderClosedFormula, bodyStart,
      rewriting_embeddedFormulaSubstitution,
      ← TransitiveRewriting.comp_app]
    constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar, Rew.q_bvar_succ]
      · intro coordinate
        exact Empty.elim coordinate
    · rfl) post

private noncomputable def emptyBallHybridCertificate
    (body : ArithmeticSemiformula Nat 1) :
    HybridCertificate zeroValuation
      (body.ballLT (shortBinaryNumeralTerm 0)) := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.boundedUniversal
      (shortBinaryNumeralTerm 0) body
      (.nil zeroValuation body)
  exact .cast (by
    change
      (∀⁰ termBoundedUniversalBody
        (Rew.bShift (shortBinaryNumeralTerm 0)) body) =
        body.ballLT (shortBinaryNumeralTerm 0)
    rw [termBoundedUniversal_eq_ball]
    rfl) direct

private def compactAdditiveBoundaryTableClosedFormula
    (tokenCount partCount start finish boundaryTable : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveBoundaryTableDef.val) ⇜
    ![shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm partCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm boundaryTable]

private def compactAdditiveBoundaryTableRowTerminal
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 3 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
        closedShift 3 (shortBinaryNumeralTerm tokenCount),
        (#2 : ArithmeticSemiterm Nat 3),
        (#1 : ArithmeticSemiterm Nat 3)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 3 (shortBinaryNumeralTerm boundaryTable),
          closedShift 3 (shortBinaryNumeralTerm tokenCount),
          ‘#2 + 1’,
          (#0 : ArithmeticSemiterm Nat 3)]) ⋏
      “#1 < #0”)

private def compactAdditiveBoundaryTableRowBody
    (tokenCount boundaryTable : Nat) : ArithmeticSemiformula Nat 1 :=
  ((compactAdditiveBoundaryTableRowTerminal tokenCount boundaryTable).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount))

private def compactAdditiveBoundaryTableZeroPartsFormula
    (tokenCount start finish boundaryTable : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm start) ≤
      !!(shortBinaryNumeralTerm tokenCount)” ⋏
    (“!!(shortBinaryNumeralTerm finish) ≤
        !!(shortBinaryNumeralTerm tokenCount)” ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm start) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm finish) ⋏
          (compactAdditiveBoundaryTableRowBody
            tokenCount boundaryTable).ballLT
              (shortBinaryNumeralTerm 0))))

private theorem compactAdditiveBoundaryTableZeroClosedFormula_alignment
    (tokenCount start finish boundaryTable : Nat) :
    compactAdditiveBoundaryTableClosedFormula
        tokenCount 0 start finish boundaryTable =
      compactAdditiveBoundaryTableZeroPartsFormula
        tokenCount start finish boundaryTable := by
  unfold compactAdditiveBoundaryTableClosedFormula
  unfold compactAdditiveBoundaryTableZeroPartsFormula
  unfold compactAdditiveBoundaryTableRowBody
  unfold compactAdditiveBoundaryTableRowTerminal
  unfold compactAdditiveBoundaryTableDef
  unfold compactFixedWidthEntryAtValuationFormula
  simp [Rew.comp_app, LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    rewriting_embeddedFormulaSubstitution, rewriting_ballLT,
    ← TransitiveRewriting.comp_app]
  constructor
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar, unaryNumeralTerm,
          rewriting_termOperator]
    · intro coordinate
      exact Empty.elim coordinate
  · constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      congr 1
      congr 1
      congr 1
      congr 1
      · apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar,
              arithmeticZeroTerm]
        · intro coordinate
          exact Empty.elim coordinate
      · congr 1
        congr 1
        · congr 1
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar,
                arithmeticZeroTerm]
          · intro coordinate
            exact Empty.elim coordinate

private noncomputable def
    compactAdditiveBoundaryTableZeroExplicitHybridCertificate
    (tokenCount start finish boundaryTable : Nat)
    (hboundary : CompactAdditiveBoundaryTable
      tokenCount 0 start finish boundaryTable) :
    HybridCertificate zeroValuation
      (compactAdditiveBoundaryTableClosedFormula
        tokenCount 0 start finish boundaryTable) := by
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLeCertificate start tokenCount hboundary.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLeCertificate finish tokenCount hboundary.2.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm boundaryTable)
          (shortBinaryNumeralTerm tokenCount)
          (unaryNumeralTerm 0)
          (shortBinaryNumeralTerm start) (by
            simpa only [termValue_shortBinaryNumeralTerm,
              termValue_unaryNumeralTerm] using
              hboundary.2.2.1))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm boundaryTable)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm 0)
            (shortBinaryNumeralTerm finish) (by
              simpa only [termValue_shortBinaryNumeralTerm] using
                hboundary.2.2.2.1))
          (emptyBallHybridCertificate
            (compactAdditiveBoundaryTableRowBody
              tokenCount boundaryTable)))))
  exact .cast
    (compactAdditiveBoundaryTableZeroClosedFormula_alignment
      tokenCount start finish boundaryTable).symm parts

private def compactAdditiveNatListListRowsClosedFormula
    (tokenTable width tokenCount boundaryTable count : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactAdditiveNatListListRowsWellFormedDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm boundaryTable,
      shortBinaryNumeralTerm count]

private def compactAdditiveNatListListRowsTerminal
    (tokenTable width tokenCount boundaryTable : Nat) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm boundaryTable),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        (#3 : ArithmeticSemiterm Nat 4),
        (#2 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm boundaryTable),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          ‘#3 + 1’,
          (#1 : ArithmeticSemiterm Nat 4)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveNatListSliceDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          (#2 : ArithmeticSemiterm Nat 4),
          (#0 : ArithmeticSemiterm Nat 4),
          (#1 : ArithmeticSemiterm Nat 4)]))

private def compactAdditiveNatListListRowsBody
    (tokenTable width tokenCount boundaryTable : Nat) :
    ArithmeticSemiformula Nat 1 :=
  ((((compactAdditiveNatListListRowsTerminal
      tokenTable width tokenCount boundaryTable).bexsLTSucc
        (closedShift 3 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
      (closedShift 2 (shortBinaryNumeralTerm tokenCount))).bexsLTSucc
    (closedShift 1 (shortBinaryNumeralTerm tokenCount)))

private theorem compactAdditiveNatListListRowsZeroClosedFormula_alignment
    (tokenTable width tokenCount boundaryTable : Nat) :
    compactAdditiveNatListListRowsClosedFormula
        tokenTable width tokenCount boundaryTable 0 =
      (compactAdditiveNatListListRowsBody
        tokenTable width tokenCount boundaryTable).ballLT
          (shortBinaryNumeralTerm 0) := by
  unfold compactAdditiveNatListListRowsClosedFormula
  unfold compactAdditiveNatListListRowsBody
  unfold compactAdditiveNatListListRowsTerminal
  unfold compactAdditiveNatListListRowsWellFormedDef
  simp [Rew.comp_app, LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    rewriting_embeddedFormulaSubstitution, rewriting_ballLT,
    ← TransitiveRewriting.comp_app]
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
        simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar,
          arithmeticZeroTerm]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar,
            arithmeticZeroTerm]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [closedShift, Rew.q, Rew.comp_app, Rew.subst_bvar,
            arithmeticZeroTerm]
      · intro coordinate
        exact Empty.elim coordinate

private noncomputable def
    compactAdditiveNatListListRowsZeroExplicitHybridCertificate
    (tokenTable width tokenCount boundaryTable : Nat) :
    HybridCertificate zeroValuation
      (compactAdditiveNatListListRowsClosedFormula
        tokenTable width tokenCount boundaryTable 0) := by
  exact .cast
    (compactAdditiveNatListListRowsZeroClosedFormula_alignment
      tokenTable width tokenCount boundaryTable).symm
    (emptyBallHybridCertificate
      (compactAdditiveNatListListRowsBody
        tokenTable width tokenCount boundaryTable))

private def compactAdditiveStructuredListLayoutClosedFormula
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveStructuredListLayoutDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm start,
      shortBinaryNumeralTerm count,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm boundaryTable]

private def compactAdditiveStructuredListLayoutWitnessBody
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (shortBinaryNumeralTerm start),
        Rew.bShift (shortBinaryNumeralTerm count),
        (#0 : ArithmeticSemiterm Nat 1)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveBoundaryTableDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm count),
          (#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm finish),
          Rew.bShift (shortBinaryNumeralTerm boundaryTable)]))

private theorem compactAdditiveStructuredListLayoutClosedFormula_alignment
    (tokenTable width tokenCount start count finish boundaryTable : Nat) :
    compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start count finish boundaryTable =
      ∃⁰ compactAdditiveStructuredListLayoutWitnessBody
        tokenTable width tokenCount start count finish boundaryTable := by
  unfold compactAdditiveStructuredListLayoutClosedFormula
  unfold compactAdditiveStructuredListLayoutWitnessBody
  unfold compactAdditiveStructuredListLayoutDef
  simp [Rew.comp_app, LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm,
          unaryNumeralTerm]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm]
    · intro coordinate
      exact Empty.elim coordinate

private theorem zeroStructuredListLayoutData
    {tokenTable width tokenCount start finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start 0 finish boundaryTable) :
    start + 1 ≤ tokenCount ∧
      CompactAdditiveListHeader
        tokenTable width tokenCount start 0 (start + 1) ∧
      CompactAdditiveBoundaryTable
        tokenCount 0 (start + 1) finish boundaryTable := by
  rcases hlayout with ⟨bodyStart, hbodyBound, hheader, hboundary⟩
  have hbodyStart : bodyStart = start + 1 := hheader.1.2.1
  subst bodyStart
  exact ⟨hbodyBound, hheader, hboundary⟩

private noncomputable def
    compactAdditiveStructuredListLayoutZeroExplicitHybridCertificate
    (tokenTable width tokenCount start finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start 0 finish boundaryTable) :
    HybridCertificate zeroValuation
      (compactAdditiveStructuredListLayoutClosedFormula
        tokenTable width tokenCount start 0 finish boundaryTable) := by
  let bodyStart := start + 1
  have hdata := zeroStructuredListLayoutData hlayout
  rw [compactAdditiveStructuredListLayoutClosedFormula_alignment]
  refine .existsWitness
    (compactAdditiveStructuredListLayoutWitnessBody
      tokenTable width tokenCount start 0 finish boundaryTable)
    bodyStart ?_
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedBoundGuardCertificate bodyStart tokenCount hdata.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveListHeaderExplicitHybridCertificate
        tokenTable width tokenCount start 0 bodyStart hdata.2.1)
      (compactAdditiveBoundaryTableZeroExplicitHybridCertificate
        tokenCount bodyStart finish boundaryTable hdata.2.2))
  exact .cast (by
    simp [Rew.comp_app, compactAdditiveStructuredListLayoutWitnessBody,
      compactAdditiveListHeaderClosedFormula,
      compactAdditiveBoundaryTableClosedFormula, bodyStart,
      rewriting_embeddedFormulaSubstitution,
      ← TransitiveRewriting.comp_app]
    constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm]
      · intro coordinate
        exact Empty.elim coordinate) post

private def closedSuccessorTerm (value : Nat) : ValuationTerm :=
  ‘!!(shortBinaryNumeralTerm value) + 1’

private def compactAdditiveStructuredListLayoutSuccessorClosedFormula
    (tokenTable width tokenCount start finish boundaryTable : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactAdditiveStructuredListLayoutDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      closedSuccessorTerm start,
      shortBinaryNumeralTerm 0,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm boundaryTable]

private def compactAdditiveStructuredListLayoutSuccessorWitnessBody
    (tokenTable width tokenCount start finish boundaryTable : Nat) :
    ArithmeticSemiformula Nat 1 :=
  “#0 < !!(Rew.bShift (shortBinaryNumeralTerm tokenCount)) + 1” ⋏
    (((Rewriting.emb (ξ := Nat) compactAdditiveListHeaderDef.val) ⇜
      ![Rew.bShift (shortBinaryNumeralTerm tokenTable),
        Rew.bShift (shortBinaryNumeralTerm width),
        Rew.bShift (shortBinaryNumeralTerm tokenCount),
        Rew.bShift (closedSuccessorTerm start),
        Rew.bShift (shortBinaryNumeralTerm 0),
        (#0 : ArithmeticSemiterm Nat 1)]) ⋏
      ((Rewriting.emb (ξ := Nat) compactAdditiveBoundaryTableDef.val) ⇜
        ![Rew.bShift (shortBinaryNumeralTerm tokenCount),
          Rew.bShift (shortBinaryNumeralTerm 0),
          (#0 : ArithmeticSemiterm Nat 1),
          Rew.bShift (shortBinaryNumeralTerm finish),
          Rew.bShift (shortBinaryNumeralTerm boundaryTable)]))

private theorem
    compactAdditiveStructuredListLayoutSuccessorClosedFormula_alignment
    (tokenTable width tokenCount start finish boundaryTable : Nat) :
    compactAdditiveStructuredListLayoutSuccessorClosedFormula
        tokenTable width tokenCount start finish boundaryTable =
      ∃⁰ compactAdditiveStructuredListLayoutSuccessorWitnessBody
        tokenTable width tokenCount start finish boundaryTable := by
  unfold compactAdditiveStructuredListLayoutSuccessorClosedFormula
  unfold compactAdditiveStructuredListLayoutSuccessorWitnessBody
  unfold compactAdditiveStructuredListLayoutDef
  simp [Rew.comp_app, LO.FirstOrder.Semiformula.bexsLTSucc,
    LO.FirstOrder.Semiformula.bexsLT,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  · congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate

private noncomputable def
    compactAdditiveStructuredListLayoutSuccessorZeroExplicitHybridCertificate
    (tokenTable width tokenCount start finish boundaryTable : Nat)
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount (start + 1) 0 finish boundaryTable) :
    HybridCertificate zeroValuation
      (compactAdditiveStructuredListLayoutSuccessorClosedFormula
        tokenTable width tokenCount start finish boundaryTable) := by
  let bodyStart := (start + 1) + 1
  have hdata := zeroStructuredListLayoutData hlayout
  rw [compactAdditiveStructuredListLayoutSuccessorClosedFormula_alignment]
  refine .existsWitness
    (compactAdditiveStructuredListLayoutSuccessorWitnessBody
      tokenTable width tokenCount start finish boundaryTable) bodyStart ?_
  have hheaderAtTerms : CompactAdditiveListHeader
      (termValue zeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue zeroValuation (shortBinaryNumeralTerm width))
      (termValue zeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue zeroValuation (closedSuccessorTerm start))
      (termValue zeroValuation (shortBinaryNumeralTerm 0))
      (termValue zeroValuation (shortBinaryNumeralTerm bodyStart)) := by
    simpa [closedSuccessorTerm, bodyStart,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne, termValue_arithmeticZero] using hdata.2.1
  let post := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedBoundGuardCertificate bodyStart tokenCount hdata.1)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveListHeaderAtValuationExplicitHybridCertificate
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width)
        (shortBinaryNumeralTerm tokenCount)
        (closedSuccessorTerm start)
        (shortBinaryNumeralTerm 0)
        (shortBinaryNumeralTerm bodyStart) hheaderAtTerms)
      (compactAdditiveBoundaryTableZeroExplicitHybridCertificate
        tokenCount bodyStart finish boundaryTable hdata.2.2))
  exact .cast (by
    simp [Rew.comp_app,
      compactAdditiveStructuredListLayoutSuccessorWitnessBody,
      compactAdditiveListHeaderAtValuationFormula,
      compactAdditiveBoundaryTableClosedFormula, bodyStart,
      rewriting_embeddedFormulaSubstitution,
      ← TransitiveRewriting.comp_app]
    constructor
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      congr 1
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.q, Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate) post

private def compactNumericVerifierTaskCoreClosedFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskCoreGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tag,
      shortBinaryNumeralTerm coordinates.gammaFinish,
      shortBinaryNumeralTerm coordinates.gammaCount,
      shortBinaryNumeralTerm coordinates.gammaBoundary,
      shortBinaryNumeralTerm coordinates.firstFinish,
      shortBinaryNumeralTerm coordinates.firstCount,
      shortBinaryNumeralTerm coordinates.secondFinish,
      shortBinaryNumeralTerm coordinates.secondCount,
      shortBinaryNumeralTerm coordinates.witnessFinish,
      shortBinaryNumeralTerm coordinates.witnessCount,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm sizeWitness.gammaBoundarySize]

private def compactNumericVerifierTaskCoreZeroPartsFormula
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  compactAdditiveTokenCellAtValuationFormula
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm coordinates.start)
      (shortBinaryNumeralTerm coordinates.tag)
      (closedSuccessorTerm coordinates.start) ⋏
    (compactAdditiveStructuredListLayoutSuccessorClosedFormula
        tokenTable width tokenCount coordinates.start
          coordinates.gammaFinish coordinates.gammaBoundary ⋏
      (compactAdditiveNatListListRowsClosedFormula
          tokenTable width tokenCount coordinates.gammaBoundary 0 ⋏
        (binaryLengthAtValuationFormula
            (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
            (shortBinaryNumeralTerm coordinates.gammaBoundary) ⋏
          (“!!(shortBinaryNumeralTerm sizeWitness.gammaBoundarySize) ≤
              (!!(shortBinaryNumeralTerm 0) + 1) *
                !!(shortBinaryNumeralTerm tokenCount)” ⋏
            (compactAdditiveNatListSliceClosedFormula
                tokenTable width tokenCount coordinates.gammaFinish 0
                  coordinates.firstFinish ⋏
              (compactAdditiveNatListSliceClosedFormula
                  tokenTable width tokenCount coordinates.firstFinish 0
                    coordinates.secondFinish ⋏
                (compactAdditiveNatListSliceClosedFormula
                    tokenTable width tokenCount coordinates.secondFinish 0
                      coordinates.witnessFinish ⋏
                  compactAdditiveNatListSliceClosedFormula
                    tokenTable width tokenCount coordinates.witnessFinish 0
                      coordinates.finish)))))))

private theorem compactNumericVerifierTaskCoreClosedFormula_alignment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    compactNumericVerifierTaskCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness =
      compactNumericVerifierTaskCoreZeroPartsFormula
        tokenTable width tokenCount coordinates sizeWitness := by
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  dsimp at hgammaCount hfirstCount hsecondCount hwitnessCount hsuffixCount
  subst gammaCount
  subst firstCount
  subst secondCount
  subst witnessCount
  subst suffixCount
  unfold compactNumericVerifierTaskCoreClosedFormula
  unfold compactNumericVerifierTaskCoreZeroPartsFormula
  unfold compactNumericVerifierTaskCoreGraphDef
  simp [Rew.comp_app, compactAdditiveTokenCellAtValuationFormula,
    compactAdditiveStructuredListLayoutSuccessorClosedFormula,
    closedSuccessorTerm,
    compactAdditiveNatListListRowsClosedFormula,
    compactAdditiveNatListSliceClosedFormula,
    compactNatSizeDef, binaryLengthAtValuationFormula,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm,
          unaryNumeralTerm]
    · intro coordinate
      exact Empty.elim coordinate

private noncomputable def
    compactNumericVerifierTaskCoreZeroExplicitHybridCertificate
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hcore : CompactNumericVerifierTaskCoreGraph
      tokenTable width tokenCount coordinates sizeWitness)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    HybridCertificate zeroValuation
      (compactNumericVerifierTaskCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness) := by
  rw [compactNumericVerifierTaskCoreClosedFormula_alignment
    tokenTable width tokenCount coordinates sizeWitness hgammaCount
      hfirstCount hsecondCount hwitnessCount hsuffixCount]
  rcases hcore with
    ⟨htagCell, hgammaLayout, hgammaRows, hsizeEq, hsizeBound,
      hfirstSlice, hsecondSlice, hwitnessSlice, hsuffixSlice⟩
  have hgammaLayoutZero : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount (coordinates.start + 1) 0
        coordinates.gammaFinish coordinates.gammaBoundary := by
    simpa [hgammaCount] using hgammaLayout
  have hfirstSliceZero : CompactAdditiveNatListSlice
      tokenTable width tokenCount coordinates.gammaFinish 0
        coordinates.firstFinish := by
    simpa [hfirstCount] using hfirstSlice
  have hsecondSliceZero : CompactAdditiveNatListSlice
      tokenTable width tokenCount coordinates.firstFinish 0
        coordinates.secondFinish := by
    simpa [hsecondCount] using hsecondSlice
  have hwitnessSliceZero : CompactAdditiveNatListSlice
      tokenTable width tokenCount coordinates.secondFinish 0
        coordinates.witnessFinish := by
    simpa [hwitnessCount] using hwitnessSlice
  have hsuffixSliceZero : CompactAdditiveNatListSlice
      tokenTable width tokenCount coordinates.witnessFinish 0
        coordinates.finish := by
    simpa [hsuffixCount] using hsuffixSlice
  let sizeBoundTerm : ValuationTerm :=
    ‘(!!(shortBinaryNumeralTerm 0) + 1) *
      !!(shortBinaryNumeralTerm tokenCount)’
  have htagCellAtTerms : CompactAdditiveTokenCell
      (termValue zeroValuation (shortBinaryNumeralTerm tokenTable))
      (termValue zeroValuation (shortBinaryNumeralTerm width))
      (termValue zeroValuation (shortBinaryNumeralTerm tokenCount))
      (termValue zeroValuation (shortBinaryNumeralTerm coordinates.start))
      (termValue zeroValuation (shortBinaryNumeralTerm coordinates.tag))
      (termValue zeroValuation (closedSuccessorTerm coordinates.start)) := by
    simpa [closedSuccessorTerm, termValue_shortBinaryNumeralTerm,
      termValue_arithmeticAdd, termValue_arithmeticOne] using htagCell
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactAdditiveTokenCellAtValuationExplicitHybridCertificate
      (shortBinaryNumeralTerm tokenTable)
      (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (shortBinaryNumeralTerm coordinates.start)
      (shortBinaryNumeralTerm coordinates.tag)
      (closedSuccessorTerm coordinates.start) htagCellAtTerms)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactAdditiveStructuredListLayoutSuccessorZeroExplicitHybridCertificate
        tokenTable width tokenCount coordinates.start
          coordinates.gammaFinish coordinates.gammaBoundary hgammaLayoutZero)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListListRowsZeroExplicitHybridCertificate
          tokenTable width tokenCount coordinates.gammaBoundary)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (.binaryLength zeroValuation
            (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
            (shortBinaryNumeralTerm coordinates.gammaBoundary) (by
              simpa [termValue_shortBinaryNumeralTerm] using hsizeEq))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (valuationLeCertificate
              (shortBinaryNumeralTerm sizeWitness.gammaBoundarySize)
              sizeBoundTerm (by
                simpa [sizeBoundTerm, hgammaCount,
                  termValue_shortBinaryNumeralTerm,
                  termValue_arithmeticAdd, termValue_arithmeticMul,
                  termValue_arithmeticOne, termValue_arithmeticZero] using
                    hsizeBound))
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListSliceZeroExplicitHybridCertificate
                tokenTable width tokenCount coordinates.gammaFinish
                  coordinates.firstFinish hfirstSliceZero)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListSliceZeroExplicitHybridCertificate
                  tokenTable width tokenCount coordinates.firstFinish
                    coordinates.secondFinish hsecondSliceZero)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactAdditiveNatListSliceZeroExplicitHybridCertificate
                    tokenTable width tokenCount coordinates.secondFinish
                      coordinates.witnessFinish hwitnessSliceZero)
                  (compactAdditiveNatListSliceZeroExplicitHybridCertificate
                    tokenTable width tokenCount coordinates.witnessFinish
                      coordinates.finish hsuffixSliceZero))))))))
  simpa only [compactNumericVerifierTaskCoreZeroPartsFormula,
    sizeBoundTerm] using parts

private def compactNumericVerifierTaskBoundedHeadClosedFormula
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskBoundedHeadDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm taskBoundary,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm coordinates.start,
      shortBinaryNumeralTerm coordinates.finish,
      shortBinaryNumeralTerm coordinates.tag,
      shortBinaryNumeralTerm coordinates.gammaFinish,
      shortBinaryNumeralTerm coordinates.gammaCount,
      shortBinaryNumeralTerm coordinates.gammaBoundary,
      shortBinaryNumeralTerm coordinates.firstFinish,
      shortBinaryNumeralTerm coordinates.firstCount,
      shortBinaryNumeralTerm coordinates.secondFinish,
      shortBinaryNumeralTerm coordinates.secondCount,
      shortBinaryNumeralTerm coordinates.witnessFinish,
      shortBinaryNumeralTerm coordinates.witnessCount,
      shortBinaryNumeralTerm coordinates.suffixCount,
      shortBinaryNumeralTerm sizeWitness.gammaBoundarySize]

private def compactNumericVerifierTaskBoundedHeadPartsFormula
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  [“!!(shortBinaryNumeralTerm coordinates.start) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.finish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.tag) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaBoundary) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.firstFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.firstCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.secondFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.secondCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.witnessFinish) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.witnessCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm coordinates.suffixCount) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    “!!(shortBinaryNumeralTerm sizeWitness.gammaBoundarySize) ≤
      !!(shortBinaryNumeralTerm valueBound)”,
    compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm taskBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 0)
      (shortBinaryNumeralTerm coordinates.start),
    compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm taskBoundary)
      (shortBinaryNumeralTerm tokenCount)
      (unaryNumeralTerm 1)
      (shortBinaryNumeralTerm coordinates.finish),
    compactNumericVerifierTaskCoreClosedFormula
      tokenTable width tokenCount coordinates sizeWitness].conj₂

private theorem compactNumericVerifierTaskBoundedHeadClosedFormula_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    compactNumericVerifierTaskBoundedHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness =
      compactNumericVerifierTaskBoundedHeadPartsFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness := by
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  unfold compactNumericVerifierTaskBoundedHeadClosedFormula
  unfold compactNumericVerifierTaskBoundedHeadPartsFormula
  unfold compactNumericVerifierTaskBoundedHeadDef
  simp [Rew.comp_app, compactFixedWidthEntryAtValuationFormula,
    compactNumericVerifierTaskCoreClosedFormula,
    rewriting_embeddedFormulaSubstitution,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.q, Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm,
          unaryNumeralTerm]
    · intro coordinate
      exact Empty.elim coordinate

private noncomputable def
    compactNumericVerifierTaskBoundedHeadExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    HybridCertificate zeroValuation
      (compactNumericVerifierTaskBoundedHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness) := by
  rcases hhead with
    ⟨hstart, hfinish, htag, hgammaFinish, hgammaCountBound,
      hgammaBoundary, hfirstFinish, hfirstCountBound,
      hsecondFinish, hsecondCountBound, hwitnessFinish,
      hwitnessCountBound, hsuffixCountBound, hsizeBound,
      hstartEntry, hfinishEntry, hcore⟩
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (closedLeCertificate coordinates.start valueBound hstart)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (closedLeCertificate coordinates.finish valueBound hfinish)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (closedLeCertificate coordinates.tag valueBound htag)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (closedLeCertificate coordinates.gammaFinish valueBound hgammaFinish)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedLeCertificate coordinates.gammaCount valueBound
              hgammaCountBound)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (closedLeCertificate coordinates.gammaBoundary valueBound
                hgammaBoundary)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (closedLeCertificate coordinates.firstFinish valueBound
                  hfirstFinish)
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (closedLeCertificate coordinates.firstCount valueBound
                    hfirstCountBound)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (closedLeCertificate coordinates.secondFinish valueBound
                      hsecondFinish)
                    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                      (closedLeCertificate coordinates.secondCount valueBound
                        hsecondCountBound)
                      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                        (closedLeCertificate coordinates.witnessFinish valueBound
                          hwitnessFinish)
                        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                          (closedLeCertificate coordinates.witnessCount valueBound
                            hwitnessCountBound)
                          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                            (closedLeCertificate coordinates.suffixCount valueBound
                              hsuffixCountBound)
                            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                              (closedLeCertificate
                                sizeWitness.gammaBoundarySize valueBound hsizeBound)
                              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                                  zeroValuation
                                  (shortBinaryNumeralTerm taskBoundary)
                                  (shortBinaryNumeralTerm tokenCount)
                                  (unaryNumeralTerm 0)
                                  (shortBinaryNumeralTerm coordinates.start) (by
                                    simpa only [termValue_shortBinaryNumeralTerm,
                                      termValue_unaryNumeralTerm]
                                      using hstartEntry))
                                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                                  (compactFixedWidthEntryAtValuationExplicitHybridCertificate
                                    zeroValuation
                                    (shortBinaryNumeralTerm taskBoundary)
                                    (shortBinaryNumeralTerm tokenCount)
                                    (unaryNumeralTerm 1)
                                    (shortBinaryNumeralTerm coordinates.finish) (by
                                      simpa only [termValue_shortBinaryNumeralTerm,
                                        termValue_unaryNumeralTerm]
                                        using hfinishEntry))
                                  (compactNumericVerifierTaskCoreZeroExplicitHybridCertificate
                                    tokenTable width tokenCount coordinates sizeWitness
                                      hcore hgammaCount hfirstCount hsecondCount
                                        hwitnessCount hsuffixCount))))))))))))))))
  exact .cast
    (compactNumericVerifierTaskBoundedHeadClosedFormula_alignment
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness).symm parts

/-- Install every coordinate of a closed bounded vector as an explicit
short-binary existential witness.  The terminal certificate is supplied as
data; no witness is recovered from formula truth. -/
noncomputable def buildExplicitClosedBoundedVectorHybridCertificate :
    {k : Nat} ->
    (bound : Nat) ->
    (body : ArithmeticSemiformula Nat k) ->
    (values : Fin k -> Nat) ->
    (∀ index, values index ≤ bound) ->
    HybridCertificate zeroValuation
      (body ⇜ fun index => shortBinaryNumeralTerm (values index)) ->
    HybridCertificate zeroValuation
      (explicitClosedBoundedVectorFormula
        (shortBinaryNumeralTerm bound) k body)
  | 0, bound, body, values, hbounds, terminal => by
      simpa [explicitClosedBoundedVectorFormula] using terminal
  | k + 1, bound, body, values, hbounds, terminal => by
      let tailValues : Fin k -> Nat := fun index => values index.succ
      let witnessBody := explicitWitnessBodyAfterTail body values
      let guard : ValuationFormula :=
        “!!(shortBinaryNumeralTerm (values 0)) <
          !!(shortBinaryNumeralTerm bound) + 1”
      let guardCertificate :=
        closedBoundGuardCertificate (values 0) bound (hbounds 0)
      have hbodySubstitution :
          witnessBody/[shortBinaryNumeralTerm (values 0)] =
            body ⇜ fun index =>
              shortBinaryNumeralTerm (values index) :=
        explicitWitnessBodyAfterTail_subst_head body values
      let installed : HybridCertificate zeroValuation
          (witnessBody/[shortBinaryNumeralTerm (values 0)]) :=
        .cast hbodySubstitution.symm terminal
      let guarded :=
        CheckedHybridValuationBoundedFormulaCertificate.conjunction
          guardCertificate installed
      let inner : HybridCertificate zeroValuation
          (witnessBody.bexsLTSucc
            (shortBinaryNumeralTerm bound)) := by
        let boundedMatrix : ArithmeticSemiformula Nat 1 :=
          Semiformula.Operator.LT.lt.operator
              ![(#0 : ArithmeticSemiterm Nat 1),
                Rew.bShift
                  ‘!!(shortBinaryNumeralTerm bound) + 1’] ⋏
            witnessBody
        let direct : HybridCertificate zeroValuation (∃⁰ boundedMatrix) :=
          .existsWitness boundedMatrix (values 0) (.cast (by
            simp [boundedMatrix, guard,
              ← TransitiveRewriting.comp_app]) guarded)
        exact .cast (by
          rfl) direct
      let recursiveTerminal : HybridCertificate zeroValuation
          ((body.bexsLTSucc
              (closedShift k (shortBinaryNumeralTerm bound))) ⇜
            (fun index : Fin k =>
              shortBinaryNumeralTerm (tailValues index))) :=
        .cast
          (shortBinarySubstitution_bexsLTSucc_tail
            (shortBinaryNumeralTerm bound) body values).symm inner
      simpa only [explicitClosedBoundedVectorFormula] using
        buildExplicitClosedBoundedVectorHybridCertificate bound
          (body.bexsLTSucc
            (closedShift k (shortBinaryNumeralTerm bound)))
          tailValues (fun index => hbounds index.succ) recursiveTerminal

private def compactNumericVerifierParseTaskHeadTerminalPartsFormula
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    ValuationFormula :=
  [compactNumericVerifierTaskBoundedHeadClosedFormula
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness,
    “!!(shortBinaryNumeralTerm coordinates.tag) =
      !!(unaryNumeralTerm 10)”,
    “!!(shortBinaryNumeralTerm coordinates.gammaCount) =
      !!(unaryNumeralTerm 0)”,
    “!!(shortBinaryNumeralTerm coordinates.firstCount) =
      !!(unaryNumeralTerm 0)”,
    “!!(shortBinaryNumeralTerm coordinates.secondCount) =
      !!(unaryNumeralTerm 0)”,
    “!!(shortBinaryNumeralTerm coordinates.witnessCount) =
      !!(unaryNumeralTerm 0)”,
    “!!(shortBinaryNumeralTerm coordinates.suffixCount) =
      !!(unaryNumeralTerm 0)”].conj₂

private theorem compactNumericVerifierParseTaskHeadTerminalRewriting_alignment
    (tokenTable width tokenCount taskBoundary valueBound
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    (((Rew.subst
        ![shortBinaryNumeralTerm start,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm tag,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm firstFinish,
          shortBinaryNumeralTerm firstCount,
          shortBinaryNumeralTerm secondFinish,
          shortBinaryNumeralTerm secondCount,
          shortBinaryNumeralTerm witnessFinish,
          shortBinaryNumeralTerm witnessCount,
          shortBinaryNumeralTerm suffixCount,
          shortBinaryNumeralTerm gammaBoundarySize,
          shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm valueBound]).comp
        (Rew.emb : Rew ℒₒᵣ Empty 19 Nat 19)).comp
      (Rew.subst parseTaskHeadTerms)) =
    (Rew.subst
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm valueBound,
          shortBinaryNumeralTerm start,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm tag,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm firstFinish,
          shortBinaryNumeralTerm firstCount,
          shortBinaryNumeralTerm secondFinish,
          shortBinaryNumeralTerm secondCount,
          shortBinaryNumeralTerm witnessFinish,
          shortBinaryNumeralTerm witnessCount,
          shortBinaryNumeralTerm suffixCount,
          shortBinaryNumeralTerm gammaBoundarySize]).comp
      (Rew.emb : Rew ℒₒᵣ Empty 19 Nat 19) := by
  apply Rew.ext
  · intro coordinate
    fin_cases coordinate <;>
      simp [parseTaskHeadTerms, localVariable, globalVariable,
        Rew.comp_app, Rew.subst_bvar]
  · intro coordinate
    exact Empty.elim coordinate

private theorem
    compactNumericVerifierParseTaskHeadTerminalFormula_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness) :
    compactNumericVerifierParseTaskHeadOpenWitnessMatrix
        tokenTable width tokenCount taskBoundary valueBound ⇜
      (fun index => shortBinaryNumeralTerm
        (explicitCoordinateValues coordinates sizeWitness index)) =
      compactNumericVerifierParseTaskHeadTerminalPartsFormula
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness := by
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  unfold compactNumericVerifierParseTaskHeadOpenWitnessMatrix
  unfold explicitCoordinateValues
  have hlocalTerms :
      (fun index =>
        shortBinaryNumeralTerm
          (![start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
            firstFinish, firstCount, secondFinish, secondCount,
            witnessFinish, witnessCount, suffixCount, gammaBoundarySize]
            index)) =
        ![shortBinaryNumeralTerm start,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm tag,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm firstFinish,
          shortBinaryNumeralTerm firstCount,
          shortBinaryNumeralTerm secondFinish,
          shortBinaryNumeralTerm secondCount,
          shortBinaryNumeralTerm witnessFinish,
          shortBinaryNumeralTerm witnessCount,
          shortBinaryNumeralTerm suffixCount,
          shortBinaryNumeralTerm gammaBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  rw [hlocalTerms]
  have hrew :
      (Rew.subst
          ![shortBinaryNumeralTerm start,
            shortBinaryNumeralTerm finish,
            shortBinaryNumeralTerm tag,
            shortBinaryNumeralTerm gammaFinish,
            shortBinaryNumeralTerm gammaCount,
            shortBinaryNumeralTerm gammaBoundary,
            shortBinaryNumeralTerm firstFinish,
            shortBinaryNumeralTerm firstCount,
            shortBinaryNumeralTerm secondFinish,
            shortBinaryNumeralTerm secondCount,
            shortBinaryNumeralTerm witnessFinish,
            shortBinaryNumeralTerm witnessCount,
            shortBinaryNumeralTerm suffixCount,
            shortBinaryNumeralTerm gammaBoundarySize]).comp
          (normalizedGlobalSubstitutionQpow
            ![shortBinaryNumeralTerm tokenTable,
              shortBinaryNumeralTerm width,
              shortBinaryNumeralTerm tokenCount,
              shortBinaryNumeralTerm taskBoundary,
              shortBinaryNumeralTerm valueBound] 14) =
        (Rew.subst
          ![shortBinaryNumeralTerm start,
            shortBinaryNumeralTerm finish,
            shortBinaryNumeralTerm tag,
            shortBinaryNumeralTerm gammaFinish,
            shortBinaryNumeralTerm gammaCount,
            shortBinaryNumeralTerm gammaBoundary,
            shortBinaryNumeralTerm firstFinish,
            shortBinaryNumeralTerm firstCount,
            shortBinaryNumeralTerm secondFinish,
            shortBinaryNumeralTerm secondCount,
            shortBinaryNumeralTerm witnessFinish,
            shortBinaryNumeralTerm witnessCount,
            shortBinaryNumeralTerm suffixCount,
            shortBinaryNumeralTerm gammaBoundarySize,
            shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm taskBoundary,
            shortBinaryNumeralTerm valueBound]).comp
          (Rew.emb : Rew ℒₒᵣ Empty 19 Nat 19) := by
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [normalizedGlobalSubstitutionQpow, Rew.q, Rew.comp_app,
          Rew.subst_bvar]
      all_goals
        change
          Rew.subst
            ![shortBinaryNumeralTerm start,
              shortBinaryNumeralTerm finish,
              shortBinaryNumeralTerm tag,
              shortBinaryNumeralTerm gammaFinish,
              shortBinaryNumeralTerm gammaCount,
              shortBinaryNumeralTerm gammaBoundary,
              shortBinaryNumeralTerm firstFinish,
              shortBinaryNumeralTerm firstCount,
              shortBinaryNumeralTerm secondFinish,
              shortBinaryNumeralTerm secondCount,
              shortBinaryNumeralTerm witnessFinish,
              shortBinaryNumeralTerm witnessCount,
              shortBinaryNumeralTerm suffixCount,
              shortBinaryNumeralTerm gammaBoundarySize]
            (closedShift 14 _) = _
        apply substitute_closedShift
    · intro coordinate
      exact Empty.elim coordinate
  calc
    _ = ((Rew.subst
        ![shortBinaryNumeralTerm start,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm tag,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm firstFinish,
          shortBinaryNumeralTerm firstCount,
          shortBinaryNumeralTerm secondFinish,
          shortBinaryNumeralTerm secondCount,
          shortBinaryNumeralTerm witnessFinish,
          shortBinaryNumeralTerm witnessCount,
          shortBinaryNumeralTerm suffixCount,
          shortBinaryNumeralTerm gammaBoundarySize]).comp
        (normalizedGlobalSubstitutionQpow
          ![shortBinaryNumeralTerm tokenTable,
            shortBinaryNumeralTerm width,
            shortBinaryNumeralTerm tokenCount,
            shortBinaryNumeralTerm taskBoundary,
            shortBinaryNumeralTerm valueBound] 14)) ▹
          compactNumericVerifierParseTaskHeadRawCore :=
      (TransitiveRewriting.comp_app _ _ _).symm
    _ = _ := congrArg
      (fun rewriting => rewriting ▹
        compactNumericVerifierParseTaskHeadRawCore) hrew
    _ = _ := by
      unfold compactNumericVerifierParseTaskHeadRawCore
      unfold compactNumericVerifierParseTaskHeadTerminalPartsFormula
      unfold compactNumericVerifierTaskBoundedHeadClosedFormula
      unfold parseTaskHeadTerms
      unfold localVariable
      unfold globalVariable
      unfold arithmeticEq
      unfold arithmeticNumeral
      simp [Rew.comp_app, Rew.subst_bvar, Rew.q_bvar_succ,
        normalizedGlobalSubstitutionQpow, unaryNumeralTerm,
        rewriting_embeddedFormulaSubstitution,
        ← TransitiveRewriting.comp_app]
      simpa only [parseTaskHeadTerms_eq_explicit] using
        congrArg
          (fun rewriting => rewriting ▹
            (↑compactNumericVerifierTaskBoundedHeadDef :
              ArithmeticSemiformula Empty 19))
          (compactNumericVerifierParseTaskHeadTerminalRewriting_alignment
            tokenTable width tokenCount taskBoundary valueBound
            start finish tag gammaFinish gammaCount gammaBoundary
            firstFinish firstCount secondFinish secondCount
            witnessFinish witnessCount suffixCount gammaBoundarySize)

private theorem explicitCoordinateValues_le_valueBound
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness) :
    ∀ index, explicitCoordinateValues coordinates sizeWitness index ≤
      valueBound := by
  rcases hhead with
    ⟨hstart, hfinish, htag, hgammaFinish, hgammaCount,
      hgammaBoundary, hfirstFinish, hfirstCount,
      hsecondFinish, hsecondCount, hwitnessFinish,
      hwitnessCount, hsuffixCount, hsize, _hstartEntry,
      _hfinishEntry, _hcore⟩
  intro index
  fin_cases index <;>
    assumption

/-- Explicit hybrid certificate for the genuine initial parse-task predicate.
The fourteen witnesses are the supplied row coordinates and size witness. -/
noncomputable def compactNumericVerifierParseTaskHeadExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    HybridCertificate zeroValuation
      (compactNumericVerifierParseTaskHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound) := by
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactNumericVerifierTaskBoundedHeadExplicitHybridCertificate
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness hhead hgammaCount hfirstCount
            hsecondCount hwitnessCount hsuffixCount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (closedFixedNumeralEqCertificate coordinates.tag 10 htag)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (closedFixedNumeralEqCertificate
            coordinates.gammaCount 0 hgammaCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (closedFixedNumeralEqCertificate
              coordinates.firstCount 0 hfirstCount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (closedFixedNumeralEqCertificate
                coordinates.secondCount 0 hsecondCount)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (closedFixedNumeralEqCertificate
                  coordinates.witnessCount 0 hwitnessCount)
                (closedFixedNumeralEqCertificate coordinates.suffixCount 0
                  hsuffixCount))))))
  let terminal : HybridCertificate zeroValuation
      (compactNumericVerifierParseTaskHeadOpenWitnessMatrix
          tokenTable width tokenCount taskBoundary valueBound ⇜
        (fun index => shortBinaryNumeralTerm
          (explicitCoordinateValues coordinates sizeWitness index))) :=
    .cast
      (compactNumericVerifierParseTaskHeadTerminalFormula_alignment
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness).symm terminalParts
  let vectorCertificate :=
    buildExplicitClosedBoundedVectorHybridCertificate valueBound
      (compactNumericVerifierParseTaskHeadOpenWitnessMatrix
        tokenTable width tokenCount taskBoundary valueBound)
      (explicitCoordinateValues coordinates sizeWitness)
      (explicitCoordinateValues_le_valueBound
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness hhead)
      terminal
  exact .cast
    (compactNumericVerifierParseTaskHeadClosedFormula_alignment
      tokenTable width tokenCount taskBoundary valueBound).symm
    vectorCertificate

theorem compactNumericVerifierParseTaskHeadClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    (compactNumericVerifierParseTaskHeadClosedFormula
      tokenTable width tokenCount taskBoundary valueBound).freeVariables = ∅ := by
  unfold compactNumericVerifierParseTaskHeadClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

/-- Empty-context PA proof compiled from the explicit parse-task certificate. -/
noncomputable def compileCompactNumericVerifierParseTaskHeadExplicitHybridContext
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    CertifiedPAContextProof ∅
      (compactNumericVerifierParseTaskHeadClosedFormula
        tokenTable width tokenCount taskBoundary valueBound) := by
  let raw :=
    (compactNumericVerifierParseTaskHeadExplicitHybridCertificate
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness hhead htag hgammaCount hfirstCount
          hsecondCount hwitnessCount hsuffixCount).compile
  have hcontext :
      valuationContext
          (compactNumericVerifierParseTaskHeadClosedFormula
            tokenTable width tokenCount taskBoundary valueBound).freeVariables
          zeroValuation = ∅ := by
    rw [compactNumericVerifierParseTaskHeadClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hcontext raw

/-- Proof-free recursive resource of the explicit parse-task certificate. -/
noncomputable def
    compactNumericVerifierParseTaskHeadExplicitHybridStructuralResource
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) : Nat :=
  CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
    (compactNumericVerifierParseTaskHeadExplicitHybridCertificate
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness hhead htag hgammaCount hfirstCount
          hsecondCount hwitnessCount hsuffixCount)

theorem
    compileCompactNumericVerifierParseTaskHeadExplicitHybridContext_payloadLength_le
    (tokenTable width tokenCount taskBoundary valueBound : Nat)
    (coordinates : CompactNumericVerifierTaskRowCoordinates)
    (sizeWitness : CompactNumericVerifierTaskSizeWitness)
    (hhead : CompactNumericVerifierTaskBoundedHead
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness)
    (htag : coordinates.tag = 10)
    (hgammaCount : coordinates.gammaCount = 0)
    (hfirstCount : coordinates.firstCount = 0)
    (hsecondCount : coordinates.secondCount = 0)
    (hwitnessCount : coordinates.witnessCount = 0)
    (hsuffixCount : coordinates.suffixCount = 0) :
    (compileCompactNumericVerifierParseTaskHeadExplicitHybridContext
      tokenTable width tokenCount taskBoundary valueBound
        coordinates sizeWitness hhead htag hgammaCount hfirstCount
          hsecondCount hwitnessCount hsuffixCount).payloadLength ≤
      compactNumericVerifierParseTaskHeadExplicitHybridStructuralResource
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness hhead htag hgammaCount hfirstCount
            hsecondCount hwitnessCount hsuffixCount := by
  unfold compileCompactNumericVerifierParseTaskHeadExplicitHybridContext
  rw [CertifiedPAContextProof.castContext_payloadLength]
  exact
    CheckedHybridValuationBoundedFormulaCertificate.compile_payloadLength_le_structuralPayloadBound
      (compactNumericVerifierParseTaskHeadExplicitHybridCertificate
        tokenTable width tokenCount taskBoundary valueBound
          coordinates sizeWitness hhead htag hgammaCount hfirstCount
            hsecondCount hwitnessCount hsuffixCount)

#print axioms buildExplicitClosedBoundedVectorHybridCertificate
#print axioms compactAdditiveTokenCellExplicitHybridCertificate
#print axioms compactAdditiveListHeaderExplicitHybridCertificate
#print axioms compactAdditiveNatListSliceExplicitHybridCertificate
#print axioms compactAdditiveNatListSliceExplicitHybridCertificateOfSlice
#print axioms compactNumericVerifierParseTaskHeadExplicitHybridCertificate
#print axioms
  compileCompactNumericVerifierParseTaskHeadExplicitHybridContext_payloadLength_le

end FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
