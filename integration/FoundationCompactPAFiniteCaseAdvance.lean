import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPAUnaryAtomicTransport
import integration.FoundationCompactPALowerBoundSuccessor

/-!
# Advancing one finite equality case

Under the local assumption `i = x`, the unary-term equality compiler proves
`i + 1 = x + 1`.  Non-final branches inject that equality into the next
finite case table.  A final branch transports strict-order irreflexivity to
obtain the lower-bound alternative.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteCaseAdvance

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeOrder
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAUnaryTermSubstitutionEquality
open FoundationCompactPAUnaryTermEqualityImplication
open FoundationCompactPAUnaryAtomicTransport
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPATermSuccessorOrder
open FoundationCompactPALowerBoundSuccessor

def unarySuccessorTerm :
    LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  finiteCaseAddTerm (#0) (finiteCaseOneTerm 1)

theorem instantiateUnarySuccessorTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    instantiateUnaryTerm unarySuccessorTerm term = successorOf term := by
  unfold unarySuccessorTerm successorOf instantiateUnaryTerm
  simp [finiteCaseAddTerm, finiteCaseOneTerm, Rew.func,
    Matrix.fun_eq_vec_two]

theorem instantiateUnaryIteratedSuccessorTerm
    (value : Nat)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    instantiateUnaryTerm (iteratedSuccessorTerm 1 value) term =
      iteratedSuccessorTerm 0 value := by
  exact iteratedSuccessorTerm_substitution value term

theorem instantiateUnaryFiniteCaseOneTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    instantiateUnaryTerm (finiteCaseOneTerm 1) term =
      finiteCaseOneTerm 0 := by
  unfold instantiateUnaryTerm finiteCaseOneTerm
  simp [Rew.func]

theorem instantiateUnaryFiniteCaseAddTerm
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    instantiateUnaryTerm (finiteCaseAddTerm left right) term =
      finiteCaseAddTerm
        (instantiateUnaryTerm left term)
        (instantiateUnaryTerm right term) := by
  unfold instantiateUnaryTerm finiteCaseAddTerm
  simp [Rew.func, Matrix.fun_eq_vec_two]

theorem finiteCaseEqualityFormula_eq_parameterEqualityFormula
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    finiteCaseEqualityFormula left right =
      parameterEqualityFormula left right := by
  rw [finiteCaseEqualityFormula_eq_operator]
  rfl

theorem finiteCaseEqualityContext_eq_parameterEqualityContext
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ({∼finiteCaseEqualityFormula left right} :
        Finset LO.FirstOrder.ArithmeticProposition) =
      parameterEqualityContext left right := by
  rw [finiteCaseEqualityFormula_eq_parameterEqualityFormula]
  rfl

theorem unarySuccessorEqualityFormula_eq
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    unaryTermEqualityFormula unarySuccessorTerm
        (iteratedSuccessorTerm 0 index) subject =
      finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 (index + 1))
        (successorOf subject) := by
  unfold unaryTermEqualityFormula
  rw [instantiateUnarySuccessorTerm,
    instantiateUnarySuccessorTerm]
  rw [finiteCaseEqualityFormula_eq_operator]
  simp only [iteratedSuccessorTerm_succ, successorOf]

def proveSuccessorEqualityUnderCase
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof
      ({∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 (index + 1))
        (successorOf subject)) := by
  let raw := compileUnaryTermEqualityUnderAssumption
    unarySuccessorTerm (iteratedSuccessorTerm 0 index) subject
  let formulaCasted := CertifiedPAContextProof.cast
    (unarySuccessorEqualityFormula_eq index subject) raw
  exact CertifiedPAContextProof.castContext
    (finiteCaseEqualityContext_eq_parameterEqualityContext
      (iteratedSuccessorTerm 0 index) subject)
    formulaCasted

noncomputable def injectEqualityCase
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (index : Nat)
    (remaining : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (equalityProof : CertifiedPAContextProof Gamma
      (finiteCaseEqualityFormula
        (iteratedSuccessorTerm 0 index) subject)) :
    CertifiedPAContextProof Gamma
      (finiteEqualityCases subject (Nat.succ (index + remaining))) :=
  match remaining with
  | 0 => by
      simpa only [Nat.add_zero, finiteEqualityCases_succ] using
        (CertifiedPAContextProof.disjunctionRight
          (left := finiteEqualityCases subject index) equalityProof)
  | remaining + 1 => by
      let previous := injectEqualityCase index remaining subject equalityProof
      simpa only [Nat.add_succ, finiteEqualityCases_succ] using
        (CertifiedPAContextProof.disjunctionLeft
          (right := finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 (Nat.succ (index + remaining)))
            subject)
          previous)
termination_by remaining

def finalCaseArguments
    (index : Nat) :
    Fin 2 → LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ![unarySuccessorTerm, iteratedSuccessorTerm 1 (index + 1)]

theorem finalCaseSourceFormula_eq
    (index : Nat) :
    ∼unaryRelationFormula Language.ORing.Rel.lt
        (finalCaseArguments index)
        (iteratedSuccessorTerm 0 index) =
      ∼finiteCaseLessThanFormula
        (iteratedSuccessorTerm 0 (index + 1))
        (iteratedSuccessorTerm 0 (index + 1)) := by
  unfold finalCaseArguments unaryRelationFormula
  rw [finiteCaseLessThanFormula_eq_operator]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    instantiateUnarySuccessorTerm,
    instantiateUnaryFiniteCaseAddTerm,
    instantiateUnaryFiniteCaseOneTerm,
    instantiateUnaryIteratedSuccessorTerm,
    iteratedSuccessorTerm_succ, successorOf]
  rfl

theorem finalCaseTargetFormula_eq
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    ∼unaryRelationFormula Language.ORing.Rel.lt
        (finalCaseArguments index) subject =
      ∼finiteCaseLessThanFormula
        (successorOf subject)
        (iteratedSuccessorTerm 0 (index + 1)) := by
  unfold finalCaseArguments unaryRelationFormula
  rw [finiteCaseLessThanFormula_eq_operator]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    instantiateUnarySuccessorTerm,
    instantiateUnaryIteratedSuccessorTerm]
  rfl

def proveFinalLowerBoundUnderCase
    (index : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof
      ({∼finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 index) subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (∼finiteCaseLessThanFormula
        (successorOf subject)
        (iteratedSuccessorTerm 0 (index + 1))) := by
  let reflexiveNegative := proveLtIrrefl
    (iteratedSuccessorTerm 0 (index + 1))
  let sourceProof : CertifiedPAProof
      (∼unaryRelationFormula Language.ORing.Rel.lt
        (finalCaseArguments index)
        (iteratedSuccessorTerm 0 index)) :=
    CertifiedPAProof.cast (finalCaseSourceFormula_eq index).symm
      (CertifiedPAProof.cast
        (congrArg
          (fun formula : LO.FirstOrder.ArithmeticProposition => ∼formula)
          (finiteCaseLessThanFormula_eq_operator
            (iteratedSuccessorTerm 0 (index + 1))
            (iteratedSuccessorTerm 0 (index + 1))).symm)
        reflexiveNegative)
  let raw := negativeTransportUnderAssumption Language.ORing.Rel.lt
    (finalCaseArguments index)
    (iteratedSuccessorTerm 0 index) subject sourceProof
  let formulaCasted := CertifiedPAContextProof.cast
    (finalCaseTargetFormula_eq index subject) raw
  exact CertifiedPAContextProof.castContext
    (finiteCaseEqualityContext_eq_parameterEqualityContext
      (iteratedSuccessorTerm 0 index) subject)
    formulaCasted

#print axioms proveSuccessorEqualityUnderCase
#print axioms injectEqualityCase
#print axioms proveFinalLowerBoundUnderCase

end FoundationCompactPAFiniteCaseAdvance
