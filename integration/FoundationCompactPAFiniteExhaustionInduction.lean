import integration.FoundationCompactPAFiniteExhaustionBase
import integration.FoundationCompactPAFiniteExhaustionSuccessor
import integration.FoundationCompactCertifiedUniversalIntroduction

/-!
# Certified PA induction for finite exhaustion

This module combines the explicit zero case and successor compiler with one
genuine PA induction node.  The successor implication is first proved at the
eigenvariable `&0`, then universally introduced, and finally cast to the exact
step formula consumed by the induction axiom.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteExhaustionInduction

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPACertifiedInduction
open FoundationCompactCertifiedUniversalIntroduction
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPALowerBoundSuccessor
open FoundationCompactPAFiniteExhaustionBase
open FoundationCompactPAFiniteExhaustionSuccessor

def finiteExhaustionStepWitness :
    LO.FirstOrder.ArithmeticSemiterm Nat 1 :=
  ‘#0 + 1’

def finiteExhaustionStepBody (bound : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  (finiteExhaustionBody bound)/[(#0 :
      LO.FirstOrder.ArithmeticSemiterm Nat 1)] 🡒
    (finiteExhaustionBody bound)/[finiteExhaustionStepWitness]

theorem finiteExhaustionBody_shift_eq_self
    (bound : Nat) :
    Rewriting.shift (finiteExhaustionBody bound) =
      finiteExhaustionBody bound := by
  apply Semiformula.rew_eq_self_of
  · intro index
    simp
  · intro index hindex
    have hempty := finiteExhaustionBody_freeVariables_eq_empty bound
    have : index ∈ (finiteExhaustionBody bound).freeVariables := hindex
    rw [hempty] at this
    simp at this

theorem finiteExhaustionBody_free_substitution
    (bound : Nat)
    (witness : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    Rewriting.free ((finiteExhaustionBody bound)/[witness]) =
      (finiteExhaustionBody bound)/[Rew.free witness] := by
  change Rew.free ▹
      (Rew.subst ![witness] ▹ finiteExhaustionBody bound) = _
  rw [← TransitiveRewriting.comp_app]
  rw [Rew.free_comp_subst_eq_subst_comp_shift]
  rw [TransitiveRewriting.comp_app]
  rw [finiteExhaustionBody_shift_eq_self]
  have hvector : (Rew.free ∘ ![witness]) =
      ![Rew.free witness] := by
    funext index
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    rfl
  rw [hvector]

theorem finiteExhaustionStepWitness_free :
    Rew.free finiteExhaustionStepWitness =
      successorOf (&0) := by
  unfold finiteExhaustionStepWitness successorOf
  simp [finiteCaseAddTerm, finiteCaseOneTerm,
    Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func]
  funext index
  have hindex : index = 0 ∨ index = 1 := by omega
  rcases hindex with hindex | hindex
  · subst index
    rfl
  · subst index
    simp [Function.comp_def, Semiterm.numeral,
      Semiterm.Operator.numeral_one, Semiterm.Operator.const,
      Semiterm.Operator.operator, Semiterm.Operator.One.term_eq,
      Rew.func]
    funext emptyIndex
    exact Fin.elim0 emptyIndex

theorem finiteExhaustionStepBody_free
    (bound : Nat) :
    Rewriting.free (finiteExhaustionStepBody bound) =
      (finiteExhaustionFormula bound (&0) 🡒
        finiteExhaustionFormula bound (successorOf (&0))) := by
  unfold finiteExhaustionStepBody
  rw [LogicalConnective.HomClass.map_imply]
  rw [finiteExhaustionBody_free_substitution,
    finiteExhaustionBody_free_substitution]
  rw [show Rew.free
      (#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1) = (&0) by rfl]
  rw [finiteExhaustionStepWitness_free]
  rw [finiteExhaustionBody_substitution,
    finiteExhaustionBody_substitution]

theorem finiteExhaustionStepBody_all_eq_inductionStepFormula
    (bound : Nat) :
    (∀⁰ finiteExhaustionStepBody bound) =
      inductionStepFormula (finiteExhaustionBody bound) := by
  unfold inductionStepFormula finiteExhaustionStepBody
  rw [substitutionByBoundVariable_eq_self]
  unfold finiteExhaustionStepWitness
  rfl

def proveFiniteExhaustionStepOpen
    (bound : Nat) :
    CertifiedPAProof (Rewriting.free (finiteExhaustionStepBody bound)) :=
  CertifiedPAProof.cast
    (finiteExhaustionStepBody_free bound).symm
    (proveFiniteExhaustionSuccessorImplication bound (&0))

def proveFiniteExhaustionStep
    (bound : Nat) :
    CertifiedPAProof
      (inductionStepFormula (finiteExhaustionBody bound)) :=
  CertifiedPAProof.cast
    (finiteExhaustionStepBody_all_eq_inductionStepFormula bound)
    (universalIntroduction (finiteExhaustionStepBody bound)
      (proveFiniteExhaustionStepOpen bound))

def proveFiniteExhaustion
    (bound : Nat) :
    CertifiedPAProof (∀⁰ finiteExhaustionBody bound) :=
  proveInduction
    (finiteExhaustionBody bound)
    (finiteExhaustionBody_freeVariables_eq_empty bound)
    (proveFiniteExhaustionZero bound)
    (proveFiniteExhaustionStep bound)

theorem proveFiniteExhaustion_verifier_eq_true
    (bound : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveFiniteExhaustion bound).code
      (compactFormulaCode (∀⁰ finiteExhaustionBody bound)) = true :=
  (proveFiniteExhaustion bound).verifier_eq_true

#print axioms finiteExhaustionBody_free_substitution
#print axioms proveFiniteExhaustionStep
#print axioms proveFiniteExhaustion_verifier_eq_true

end FoundationCompactPAFiniteExhaustionInduction
