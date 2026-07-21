import integration.FoundationCompactPAFiniteCaseSyntax
import integration.FoundationCompactCertifiedDisjunction
import integration.FoundationCompactPAQuantitativeOrder

/-!
# Certified zero case for finite PA exhaustion

For every fixed bound `B`, this module proves the zero instance of
`Cases_B(x) ∨ B ≤ x`.  When `B = 0` it uses strict-order irreflexivity; when
`B > 0` it inserts the reflexive equality `0 = 0` into the explicit finite
case disjunction.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteExhaustionBase

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedDisjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPACertifiedInduction
open FoundationCompactPAFiniteCaseSyntax

theorem finiteCaseZeroTerm_eq_inductionZeroTerm :
    finiteCaseZeroTerm 0 = inductionZeroTerm := by
  unfold finiteCaseZeroTerm inductionZeroTerm
  simp [Semiterm.numeral, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.const, Semiterm.Operator.operator,
    Semiterm.Operator.Zero.term_eq, Rew.func]

theorem finiteCaseZeroEqualityFormula_eq :
    finiteCaseEqualityFormula (finiteCaseZeroTerm 0)
        inductionZeroTerm =
      (“!!inductionZeroTerm = !!inductionZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [finiteCaseEqualityFormula_eq_operator]
  rw [finiteCaseZeroTerm_eq_inductionZeroTerm]

theorem finiteCaseZeroNotLessFormula_eq :
    ∼finiteCaseLessThanFormula inductionZeroTerm
        (finiteCaseZeroTerm 0) =
      ∼(“!!inductionZeroTerm < !!inductionZeroTerm” :
        LO.FirstOrder.ArithmeticProposition) := by
  rw [finiteCaseLessThanFormula_eq_operator]
  rw [finiteCaseZeroTerm_eq_inductionZeroTerm]

def finiteCaseZeroEqualityProof :
    CertifiedPAProof
      (finiteCaseEqualityFormula (finiteCaseZeroTerm 0)
        inductionZeroTerm) :=
  CertifiedPAProof.cast finiteCaseZeroEqualityFormula_eq.symm
    (proveEqualityReflexivityAtTerm inductionZeroTerm)

def finiteCaseZeroNotLessProof :
    CertifiedPAProof
      (∼finiteCaseLessThanFormula inductionZeroTerm
        (finiteCaseZeroTerm 0)) :=
  CertifiedPAProof.cast finiteCaseZeroNotLessFormula_eq.symm
    (proveLtIrrefl inductionZeroTerm)

noncomputable def injectZeroEqualityCase :
    (tailLength : Nat) →
    CertifiedPAProof
      (finiteEqualityCases inductionZeroTerm (tailLength + 1))
  | 0 => by
      simpa only [finiteEqualityCases_succ, finiteEqualityCases_zero,
        iteratedSuccessorTerm_zero] using
        (FoundationCompactCertifiedDisjunction.disjunctionRight
          (left := (⊥ : LO.FirstOrder.ArithmeticProposition))
          finiteCaseZeroEqualityProof)
  | tailLength + 1 => by
      simpa only [finiteEqualityCases_succ] using
        (FoundationCompactCertifiedDisjunction.disjunctionLeft
          (right := finiteCaseEqualityFormula
            (iteratedSuccessorTerm 0 (tailLength + 1))
            inductionZeroTerm)
          (injectZeroEqualityCase tailLength))

noncomputable def proveFiniteExhaustionZeroFormula :
    (bound : Nat) →
    CertifiedPAProof (finiteExhaustionFormula bound inductionZeroTerm)
  | 0 => by
      unfold finiteExhaustionFormula
      simpa only [finiteEqualityCases_zero,
        iteratedSuccessorTerm_zero] using
        (FoundationCompactCertifiedDisjunction.disjunctionRight
          (left := (⊥ : LO.FirstOrder.ArithmeticProposition))
          finiteCaseZeroNotLessProof)
  | tailLength + 1 => by
      unfold finiteExhaustionFormula
      exact FoundationCompactCertifiedDisjunction.disjunctionLeft
        (right := ∼finiteCaseLessThanFormula inductionZeroTerm
          (iteratedSuccessorTerm 0 (tailLength + 1)))
        (injectZeroEqualityCase tailLength)

noncomputable def proveFiniteExhaustionZero
    (bound : Nat) :
    CertifiedPAProof ((finiteExhaustionBody bound)/[inductionZeroTerm]) :=
  CertifiedPAProof.cast
    (finiteExhaustionBody_substitution bound inductionZeroTerm).symm
    (proveFiniteExhaustionZeroFormula bound)

theorem proveFiniteExhaustionZero_verifier_eq_true
    (bound : Nat) :
    listedCompactCertifiedPAProofVerifier
      (proveFiniteExhaustionZero bound).code
      (compactFormulaCode
        ((finiteExhaustionBody bound)/[inductionZeroTerm])) = true :=
  (proveFiniteExhaustionZero bound).verifier_eq_true

#print axioms proveFiniteExhaustionZero_verifier_eq_true

end FoundationCompactPAFiniteExhaustionBase
