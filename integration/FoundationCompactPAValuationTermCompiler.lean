import integration.FoundationCompactPACertifiedContextEquality
import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPABinaryNumeralMultiplication
import integration.FoundationCompactPAFiniteCaseSyntax

/-!
# PA term compiler under a concrete free-variable valuation

This module is the atomic layer of the nested bounded-formula compiler.  It
instantiates every free variable by an explicit iterated-successor numeral,
computes the same term in the standard natural-number model, and constructs
real certified PA equalities connecting:

* the short binary numeral of the computed value;
* the instantiated closed term; and
* the original term under the finite valuation-equality context.

No proof object, proof-existence statement, or proof-length bound is accepted
as an input.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAValuationTermCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationPudlakQuantitativeConditions
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeFunctionCongruence
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralMultiplication
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPACertifiedContextEquality

abbrev ValuationTerm := LO.FirstOrder.ArithmeticSemiterm Nat 0
abbrev ValuationFormula := LO.FirstOrder.ArithmeticProposition

/-! ## Direct term instantiation and standard-model value -/

def instantiateTerm (valuation : Nat -> Nat) :
    ValuationTerm -> ValuationTerm
  | #index => Fin.elim0 index
  | &index => iteratedSuccessorTerm 0 (valuation index)
  | .func .zero args => .func .zero args
  | .func .one args => .func .one args
  | .func .add args => .func .add ![
      instantiateTerm valuation (args 0),
      instantiateTerm valuation (args 1)]
  | .func .mul args => .func .mul ![
      instantiateTerm valuation (args 0),
      instantiateTerm valuation (args 1)]

def termValue (valuation : Nat -> Nat) (term : ValuationTerm) : Nat :=
  LO.FirstOrder.Semiterm.val ![] valuation term

@[simp] theorem termValue_fvar
    (valuation : Nat -> Nat) (index : Nat) :
    termValue valuation (&index : ValuationTerm) = valuation index := rfl

@[simp] theorem termValue_zero
    (valuation : Nat -> Nat) (args : Fin 0 -> ValuationTerm) :
    termValue valuation (.func .zero args) = 0 := by
  change (LO.FirstOrder.Arithmetic.standardModel Nat).func .zero
    (fun index => LO.FirstOrder.Semiterm.val ![] valuation (args index)) = 0
  rfl

@[simp] theorem termValue_one
    (valuation : Nat -> Nat) (args : Fin 0 -> ValuationTerm) :
    termValue valuation (.func .one args) = 1 := by
  change (LO.FirstOrder.Arithmetic.standardModel Nat).func .one
    (fun index => LO.FirstOrder.Semiterm.val ![] valuation (args index)) = 1
  rfl

@[simp] theorem termValue_add
    (valuation : Nat -> Nat) (args : Fin 2 -> ValuationTerm) :
    termValue valuation (.func .add args) =
      termValue valuation (args 0) + termValue valuation (args 1) := by
  change (LO.FirstOrder.Arithmetic.standardModel Nat).func .add
    (fun index => LO.FirstOrder.Semiterm.val ![] valuation (args index)) = _
  rfl

@[simp] theorem termValue_mul
    (valuation : Nat -> Nat) (args : Fin 2 -> ValuationTerm) :
    termValue valuation (.func .mul args) =
      termValue valuation (args 0) * termValue valuation (args 1) := by
  change (LO.FirstOrder.Arithmetic.standardModel Nat).func .mul
    (fun index => LO.FirstOrder.Semiterm.val ![] valuation (args index)) = _
  rfl

theorem shortBinaryNumeralTerm_freeVariables_eq_empty
    (value : Nat) :
    (shortBinaryNumeralTerm value).freeVariables = ∅ := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp [shortBinaryNumeralTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
        arithmeticZeroTerm]
  | bit bit value hcanonical inductionHypothesis =>
      rw [show shortBinaryNumeralTerm (Nat.bit bit value) =
          binaryNumeralBitTerm bit (shortBinaryNumeralTerm value) by
        exact FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_bit
          bit value hcanonical]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro index hindex
      cases bit <;>
        simp [binaryNumeralBitTerm, binaryNumeralDoubleTerm,
          arithmeticTwoTerm, arithmeticOneTerm,
          Semiterm.freeVariables_func, inductionHypothesis] at hindex

theorem termValue_shortBinaryNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (shortBinaryNumeralTerm value) = value := by
  induction value using Nat.binaryRec' with
  | zero =>
      simp [termValue, shortBinaryNumeralTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
        arithmeticZeroTerm, Semiterm.val_func]
  | bit bit value hcanonical inductionHypothesis =>
      rw [show shortBinaryNumeralTerm (Nat.bit bit value) =
          binaryNumeralBitTerm bit (shortBinaryNumeralTerm value) by
        exact FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_bit
          bit value hcanonical]
      change LO.FirstOrder.Semiterm.val ![] valuation
        (shortBinaryNumeralTerm value) = value at inductionHypothesis
      cases bit <;>
        simp [termValue, binaryNumeralBitTerm, binaryNumeralDoubleTerm,
          arithmeticTwoTerm, arithmeticOneTerm, Semiterm.val_func,
          inductionHypothesis, Nat.bit_val]

/-! ## Short-binary to iterated-successor numeral bridge -/

noncomputable def proveShortBinaryNumeralEqualsIterated :
    (value : Nat) ->
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm value) =
        !!(iteratedSuccessorTerm 0 value)” :
        LO.FirstOrder.ArithmeticProposition)
  | 0 => by
      simpa [shortBinaryNumeralTerm,
        FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
        finiteCaseZeroTerm, paZeroTerm, arithmeticZeroTerm] using
        (proveEqualityReflexivityAtTerm (shortBinaryNumeralTerm 0))
  | value + 1 => by
      let inductionProof := proveShortBinaryNumeralEqualsIterated value
      let oneRaw := proveShortBinaryOneEqualsPaOne
      let oneProof : CertifiedPAProof
          (“!!(shortBinaryNumeralTerm 1) =
            !!(finiteCaseOneTerm 0)” :
            LO.FirstOrder.ArithmeticProposition) := by
        simpa [finiteCaseOneTerm, paOneTerm, arithmeticOneTerm] using oneRaw
      let source := paAddTerm
        (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
      let middle := paAddTerm
        (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0)
      let congruenceRaw := proveAddCongruence
        (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
        (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0)
        inductionProof oneProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” :
            LO.FirstOrder.ArithmeticProposition) := by
        exact CertifiedPAProof.cast
          (addEqualityAsTerm_formula
            (shortBinaryNumeralTerm value) (shortBinaryNumeralTerm 1)
            (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0))
          congruenceRaw
      let arithmetic := proveBinaryNumeralAddition value 1
      let arithmeticBackward := proveEqualitySymmetry
        source (shortBinaryNumeralTerm (value + 1)) arithmetic
      let through := proveEqualityTransitivity
        (shortBinaryNumeralTerm (value + 1)) source middle
        arithmeticBackward congruence
      have hmiddle : middle = finiteCaseAddTerm
          (iteratedSuccessorTerm 0 value) (finiteCaseOneTerm 0) := by
        simp [middle, paAddTerm, finiteCaseAddTerm,
          Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
          Matrix.fun_eq_vec_two]
      have hformula :
          (“!!(shortBinaryNumeralTerm (value + 1)) = !!middle” :
            LO.FirstOrder.ArithmeticProposition) =
          (“!!(shortBinaryNumeralTerm (value + 1)) =
            !!(iteratedSuccessorTerm 0 (value + 1))” :
            LO.FirstOrder.ArithmeticProposition) := by
        rw [hmiddle, iteratedSuccessorTerm_succ]
      exact CertifiedPAProof.cast hformula through

/-! ## Finite valuation context -/

def valuationEqualityAssumption
    (valuation : Nat -> Nat) (index : Nat) : ValuationFormula :=
  ∼finiteCaseEqualityFormula
    (iteratedSuccessorTerm 0 (valuation index)) (&index)

def valuationContext
    (vars : Finset Nat) (valuation : Nat -> Nat) :
    Finset ValuationFormula :=
  vars.image (valuationEqualityAssumption valuation)

theorem valuationContext_mono
    (valuation : Nat -> Nat)
    {small large : Finset Nat}
    (hsubset : small ⊆ large) :
    valuationContext small valuation ⊆ valuationContext large valuation := by
  intro formula hformula
  rcases Finset.mem_image.mp hformula with ⟨index, hindex, rfl⟩
  exact Finset.mem_image.mpr ⟨index, hsubset hindex, rfl⟩

theorem freeVariables_arg_subset_func
    {arity : Nat}
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ arity)
    (args : Fin arity -> ValuationTerm)
    (index : Fin arity) :
    (args index).freeVariables ⊆
      (LO.FirstOrder.Semiterm.func functionSymbol args).freeVariables := by
  intro candidate hcandidate
  simp only [LO.FirstOrder.Semiterm.freeVariables_func]
  simp
  exact ⟨index, hcandidate⟩

theorem finiteCaseAddTerm_eq_paAddTerm
    (left right : ValuationTerm) :
    finiteCaseAddTerm left right = paAddTerm left right := by
  unfold finiteCaseAddTerm paAddTerm
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

theorem finiteCaseMulTerm_eq_paMulTerm
    (left right : ValuationTerm) :
    LO.FirstOrder.Semiterm.func Language.Mul.mul ![left, right] =
      paMulTerm left right := by
  unfold paMulTerm
  simp [Semiterm.Operator.operator, Semiterm.Operator.Mul.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

/-! ## Instantiated term to source term under the valuation context -/

noncomputable def compileInstantiatedTermTransport
    (valuation : Nat -> Nat) :
    (term : ValuationTerm) ->
    CertifiedPAContextProof
      (valuationContext term.freeVariables valuation)
      (“!!(instantiateTerm valuation term) = !!term” : ValuationFormula)
  | #index => Fin.elim0 index
  | &index => by
      have hmembership :
          ∼(“!!(iteratedSuccessorTerm 0 (valuation index)) =
              !!(&index : ValuationTerm)” : ValuationFormula) ∈
            valuationContext ({index} : Finset Nat) valuation := by
        simp [valuationContext, valuationEqualityAssumption,
          finiteCaseEqualityFormula_eq_operator]
      exact CertifiedPAContextProof.assumption _ _ hmembership
  | .func .zero args =>
      CertifiedPAContextProof.weakenCertified _
        (proveEqualityReflexivityAtTerm (.func .zero args))
  | .func .one args =>
      CertifiedPAContextProof.weakenCertified _
        (proveEqualityReflexivityAtTerm (.func .one args))
  | .func .add args => by
      let leftRaw := compileInstantiatedTermTransport valuation (args 0)
      let rightRaw := compileInstantiatedTermTransport valuation (args 1)
      have hleftVariables : (args 0).freeVariables ⊆
          (LO.FirstOrder.Semiterm.func Language.Add.add args).freeVariables :=
        freeVariables_arg_subset_func Language.Add.add args 0
      have hrightVariables : (args 1).freeVariables ⊆
          (LO.FirstOrder.Semiterm.func Language.Add.add args).freeVariables :=
        freeVariables_arg_subset_func Language.Add.add args 1
      let left := CertifiedPAContextProof.weakenContext leftRaw
        (valuationContext_mono valuation hleftVariables)
      let right := CertifiedPAContextProof.weakenContext rightRaw
        (valuationContext_mono valuation hrightVariables)
      let congruenceRaw := contextualAddCongruence
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        (args 0) (args 1) left right
      have hsource : instantiateTerm valuation (.func .add args) =
          paAddTerm (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1)) := by
        calc
          instantiateTerm valuation (.func .add args) =
              finiteCaseAddTerm
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1)) := rfl
          _ = paAddTerm (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1)) :=
            finiteCaseAddTerm_eq_paAddTerm _ _
      have htarget : (.func .add args : ValuationTerm) =
          paAddTerm (args 0) (args 1) := by
        calc
          (.func .add args : ValuationTerm) =
              finiteCaseAddTerm (args 0) (args 1) := by
            unfold finiteCaseAddTerm
            congr 1
            exact Matrix.fun_eq_vec_two args
          _ = paAddTerm (args 0) (args 1) :=
            finiteCaseAddTerm_eq_paAddTerm _ _
      have hformula :
          (“!!(instantiateTerm valuation (LO.FirstOrder.Semiterm.func
                Language.ORing.Func.add args)) =
              !!(LO.FirstOrder.Semiterm.func Language.ORing.Func.add args)” :
              ValuationFormula) =
            (“!!(instantiateTerm valuation (args 0)) +
                !!(instantiateTerm valuation (args 1)) =
              !!(args 0) + !!(args 1)” : ValuationFormula) := by
        rw [hsource, htarget]
        exact (addEqualityAsTerm_formula
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1)).symm
      exact CertifiedPAContextProof.cast hformula.symm congruenceRaw
  | .func .mul args => by
      let leftRaw := compileInstantiatedTermTransport valuation (args 0)
      let rightRaw := compileInstantiatedTermTransport valuation (args 1)
      have hleftVariables : (args 0).freeVariables ⊆
          (LO.FirstOrder.Semiterm.func Language.Mul.mul args).freeVariables :=
        freeVariables_arg_subset_func Language.Mul.mul args 0
      have hrightVariables : (args 1).freeVariables ⊆
          (LO.FirstOrder.Semiterm.func Language.Mul.mul args).freeVariables :=
        freeVariables_arg_subset_func Language.Mul.mul args 1
      let left := CertifiedPAContextProof.weakenContext leftRaw
        (valuationContext_mono valuation hleftVariables)
      let right := CertifiedPAContextProof.weakenContext rightRaw
        (valuationContext_mono valuation hrightVariables)
      let congruenceRaw := contextualMulCongruence
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        (args 0) (args 1) left right
      have hsource : instantiateTerm valuation (.func .mul args) =
          paMulTerm (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1)) := by
        calc
          instantiateTerm valuation (.func .mul args) =
              LO.FirstOrder.Semiterm.func Language.Mul.mul ![
                instantiateTerm valuation (args 0),
                instantiateTerm valuation (args 1)] := rfl
          _ = paMulTerm (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1)) :=
            finiteCaseMulTerm_eq_paMulTerm _ _
      have htarget : (.func .mul args : ValuationTerm) =
          paMulTerm (args 0) (args 1) := by
        calc
          (.func .mul args : ValuationTerm) =
              LO.FirstOrder.Semiterm.func Language.Mul.mul
                ![args 0, args 1] := by
            congr 1
            exact Matrix.fun_eq_vec_two args
          _ = paMulTerm (args 0) (args 1) :=
            finiteCaseMulTerm_eq_paMulTerm _ _
      have hformula :
          (“!!(instantiateTerm valuation (LO.FirstOrder.Semiterm.func
                Language.ORing.Func.mul args)) =
              !!(LO.FirstOrder.Semiterm.func Language.ORing.Func.mul args)” :
              ValuationFormula) =
            (“!!(instantiateTerm valuation (args 0)) *
                !!(instantiateTerm valuation (args 1)) =
              !!(args 0) * !!(args 1)” : ValuationFormula) := by
        rw [hsource, htarget]
        exact (mulEqualityAsTerm_formula
          (instantiateTerm valuation (args 0))
          (instantiateTerm valuation (args 1))
          (args 0) (args 1)).symm
      exact CertifiedPAContextProof.cast hformula.symm congruenceRaw

/-! ## Computed short numeral to instantiated closed term -/

noncomputable def compileInstantiatedTermNormalization
    (valuation : Nat -> Nat) :
    (term : ValuationTerm) ->
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm (termValue valuation term)) =
        !!(instantiateTerm valuation term)” : ValuationFormula)
  | #index => Fin.elim0 index
  | &index => by
      simpa [termValue, instantiateTerm] using
        (proveShortBinaryNumeralEqualsIterated (valuation index))
  | .func .zero args => by
      let raw := proveShortBinaryNumeralEqualsIterated 0
      have hclosed : instantiateTerm valuation (.func .zero args) =
          iteratedSuccessorTerm 0 0 := by
        simp only [instantiateTerm, iteratedSuccessorTerm_zero]
        unfold finiteCaseZeroTerm
        congr 1
        funext index
        exact Fin.elim0 index
      have hformula :
          (“!!(shortBinaryNumeralTerm 0) =
            !!(iteratedSuccessorTerm 0 0)” : ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
                (termValue valuation (.func .zero args))) =
            !!(instantiateTerm valuation (.func .zero args))” :
            ValuationFormula) := by
        rw [termValue_zero, hclosed]
      exact CertifiedPAProof.cast hformula raw
  | .func .one args => by
      let raw := proveShortBinaryOneEqualsPaOne
      have hclosed : instantiateTerm valuation (.func .one args) =
          paOneTerm := by
        calc
          instantiateTerm valuation (.func .one args) =
              (.func .one args : ValuationTerm) := rfl
          _ = finiteCaseOneTerm 0 := by
            unfold finiteCaseOneTerm
            congr 1
            funext index
            exact Fin.elim0 index
          _ = paOneTerm := by rfl
      have hformula :
          (“!!(shortBinaryNumeralTerm 1) = !!paOneTerm” :
            ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
                (termValue valuation (.func .one args))) =
            !!(instantiateTerm valuation (.func .one args))” :
            ValuationFormula) := by
        rw [termValue_one, hclosed]
      exact CertifiedPAProof.cast hformula raw
  | .func .add args => by
      let leftValue := termValue valuation (args 0)
      let rightValue := termValue valuation (args 1)
      let leftProof := compileInstantiatedTermNormalization valuation (args 0)
      let rightProof := compileInstantiatedTermNormalization valuation (args 1)
      let source := paAddTerm
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
      let middle := paAddTerm
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
      let congruenceRaw := proveAddCongruence
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        leftProof rightProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” : ValuationFormula) :=
        CertifiedPAProof.cast
          (addEqualityAsTerm_formula
            (shortBinaryNumeralTerm leftValue)
            (shortBinaryNumeralTerm rightValue)
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1)))
          congruenceRaw
      let arithmetic := proveBinaryNumeralAddition leftValue rightValue
      let arithmeticBackward := proveEqualitySymmetry source
        (shortBinaryNumeralTerm (leftValue + rightValue)) arithmetic
      let through := proveEqualityTransitivity
        (shortBinaryNumeralTerm (leftValue + rightValue)) source middle
        arithmeticBackward congruence
      have hclosed : instantiateTerm valuation (.func .add args) =
          middle := by
        calc
          instantiateTerm valuation (.func .add args) =
              finiteCaseAddTerm
                (instantiateTerm valuation (args 0))
                (instantiateTerm valuation (args 1)) := rfl
          _ = middle := by
            exact finiteCaseAddTerm_eq_paAddTerm _ _
      have hformula :
          (“!!(shortBinaryNumeralTerm (leftValue + rightValue)) =
            !!middle” : ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
                (termValue valuation (.func .add args))) =
            !!(instantiateTerm valuation (.func .add args))” :
            ValuationFormula) := by
        rw [termValue_add, hclosed]
      exact CertifiedPAProof.cast hformula through
  | .func .mul args => by
      let leftValue := termValue valuation (args 0)
      let rightValue := termValue valuation (args 1)
      let leftProof := compileInstantiatedTermNormalization valuation (args 0)
      let rightProof := compileInstantiatedTermNormalization valuation (args 1)
      let source := paMulTerm
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
      let middle := paMulTerm
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
      let congruenceRaw := proveMulCongruence
        (shortBinaryNumeralTerm leftValue)
        (shortBinaryNumeralTerm rightValue)
        (instantiateTerm valuation (args 0))
        (instantiateTerm valuation (args 1))
        leftProof rightProof
      let congruence : CertifiedPAProof
          (“!!source = !!middle” : ValuationFormula) :=
        CertifiedPAProof.cast
          (mulEqualityAsTerm_formula
            (shortBinaryNumeralTerm leftValue)
            (shortBinaryNumeralTerm rightValue)
            (instantiateTerm valuation (args 0))
            (instantiateTerm valuation (args 1)))
          congruenceRaw
      let arithmetic := proveBinaryNumeralMultiplication leftValue rightValue
      let arithmeticBackward := proveEqualitySymmetry source
        (shortBinaryNumeralTerm (leftValue * rightValue)) arithmetic
      let through := proveEqualityTransitivity
        (shortBinaryNumeralTerm (leftValue * rightValue)) source middle
        arithmeticBackward congruence
      have hclosed : instantiateTerm valuation (.func .mul args) =
          middle := by
        calc
          instantiateTerm valuation (.func .mul args) =
              LO.FirstOrder.Semiterm.func Language.Mul.mul ![
                instantiateTerm valuation (args 0),
                instantiateTerm valuation (args 1)] := rfl
          _ = middle := by
            exact finiteCaseMulTerm_eq_paMulTerm _ _
      have hformula :
          (“!!(shortBinaryNumeralTerm (leftValue * rightValue)) =
            !!middle” : ValuationFormula) =
          (“!!(shortBinaryNumeralTerm
                (termValue valuation (.func .mul args))) =
            !!(instantiateTerm valuation (.func .mul args))” :
            ValuationFormula) := by
        rw [termValue_mul, hclosed]
      exact CertifiedPAProof.cast hformula through

/-! ## Final term-value equality in the source valuation context -/

noncomputable def compileTermValueEquality
    (valuation : Nat -> Nat) (term : ValuationTerm) :
    CertifiedPAContextProof
      (valuationContext term.freeVariables valuation)
      (“!!(shortBinaryNumeralTerm (termValue valuation term)) = !!term” :
        ValuationFormula) :=
  let normalization := CertifiedPAContextProof.weakenCertified
    (valuationContext term.freeVariables valuation)
    (compileInstantiatedTermNormalization valuation term)
  let transport := compileInstantiatedTermTransport valuation term
  contextualEqualityTransitivity
    (shortBinaryNumeralTerm (termValue valuation term))
    (instantiateTerm valuation term) term normalization transport

#print axioms proveShortBinaryNumeralEqualsIterated
#print axioms compileInstantiatedTermTransport
#print axioms compileInstantiatedTermNormalization
#print axioms compileTermValueEquality

end FoundationCompactPAValuationTermCompiler
