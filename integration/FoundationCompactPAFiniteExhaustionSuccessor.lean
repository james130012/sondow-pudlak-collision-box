import integration.FoundationCompactPAFiniteCaseAdvance

/-!
# Certified successor step for finite PA exhaustion

This module proves, for a fixed finite bound `B`, that
`Cases_B(x) ∨ B ≤ x` implies `Cases_B(x+1) ∨ B ≤ x+1`.  The finite case
disjunction is eliminated recursively.  Non-final equality branches advance
to the next case; the final equality branch produces the lower bound; and an
existing lower-bound branch is preserved by strict-order transitivity.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAFiniteExhaustionSuccessor

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPALowerBoundSuccessor
open FoundationCompactPAFiniteCaseAdvance

def finiteLowerBoundFormula
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  ∼finiteCaseLessThanFormula subject
    (iteratedSuccessorTerm 0 bound)

theorem finiteLowerBoundFormula_eq_standard
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    finiteLowerBoundFormula bound subject =
      ∼termLessThanFormula subject (iteratedSuccessorTerm 0 bound) := by
  unfold finiteLowerBoundFormula termLessThanFormula
  exact congrArg
    (fun formula : LO.FirstOrder.ArithmeticProposition => ∼formula)
    (finiteCaseLessThanFormula_eq_operator subject
      (iteratedSuccessorTerm 0 bound))

theorem finiteSuccessorLowerBoundFormula_eq_standard
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    finiteLowerBoundFormula bound (successorOf subject) =
      ∼successorLessThanFormula subject
        (iteratedSuccessorTerm 0 bound) := by
  unfold finiteLowerBoundFormula successorLessThanFormula
  exact congrArg
    (fun formula : LO.FirstOrder.ArithmeticProposition => ∼formula)
    (finiteCaseLessThanFormula_eq_operator (successorOf subject)
      (iteratedSuccessorTerm 0 bound))

def preserveLowerBoundBranch
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof
      ({∼finiteLowerBoundFormula bound subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteExhaustionFormula bound (successorOf subject)) := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼finiteLowerBoundFormula bound subject}
  let lowerRaw := CertifiedPAContextProof.assumption Gamma
    (finiteLowerBoundFormula bound subject) (by simp [Gamma])
  let lowerStandard := CertifiedPAContextProof.cast
    (finiteLowerBoundFormula_eq_standard bound subject) lowerRaw
  let successorStandard := liftLowerBoundThroughSuccessor
    subject (iteratedSuccessorTerm 0 bound) lowerStandard
  let successorFinite := CertifiedPAContextProof.cast
    (finiteSuccessorLowerBoundFormula_eq_standard bound subject).symm
    successorStandard
  unfold finiteExhaustionFormula
  exact CertifiedPAContextProof.disjunctionRight
    (left := finiteEqualityCases (successorOf subject) bound)
    successorFinite

noncomputable def advanceFiniteCasePrefix
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (prefixLength remainingLength : Nat) →
    CertifiedPAContextProof
      ({∼finiteEqualityCases subject prefixLength} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteExhaustionFormula (prefixLength + remainingLength)
        (successorOf subject))
  | 0, remainingLength => by
      let raw := CertifiedPAContextProof.exFalsoAssumption
        (finiteExhaustionFormula remainingLength (successorOf subject))
      let formulaCasted := CertifiedPAContextProof.cast
        (congrArg
          (fun bound => finiteExhaustionFormula bound
            (successorOf subject))
          (Nat.zero_add remainingLength).symm)
        raw
      have hcontext :
          ({∼(⊥ : LO.FirstOrder.ArithmeticProposition)} :
              Finset LO.FirstOrder.ArithmeticProposition) =
            ({∼finiteEqualityCases subject 0} :
              Finset LO.FirstOrder.ArithmeticProposition) := by
        rw [finiteEqualityCases_zero]
      exact CertifiedPAContextProof.castContext hcontext formulaCasted
  | prefixLength + 1, 0 => by
      let leftBranch := advanceFiniteCasePrefix subject prefixLength 1
      let lowerProof := proveFinalLowerBoundUnderCase prefixLength subject
      let rightBranch : CertifiedPAContextProof
          ({∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 prefixLength) subject} :
            Finset LO.FirstOrder.ArithmeticProposition)
          (finiteExhaustionFormula (prefixLength + 1)
            (successorOf subject)) := by
        unfold finiteExhaustionFormula
        exact CertifiedPAContextProof.disjunctionRight
          (left := finiteEqualityCases
            (successorOf subject) (prefixLength + 1))
          lowerProof
      let combined := CertifiedPAContextProof.eliminateDisjunctionAssumption
        (Gamma := ∅)
        (target := finiteExhaustionFormula (prefixLength + 1)
          (successorOf subject))
        (left := finiteEqualityCases subject prefixLength)
        (right := finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 prefixLength) subject)
        leftBranch rightBranch
      have hcontext :
          insert
              (∼(finiteEqualityCases subject prefixLength ⋎
                finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 prefixLength) subject)) ∅ =
            ({∼finiteEqualityCases subject (prefixLength + 1)} :
              Finset LO.FirstOrder.ArithmeticProposition) := by
        rw [finiteEqualityCases_succ]
        ext formula
        simp
      let singletonCombined := CertifiedPAContextProof.castContext
        hcontext combined
      exact singletonCombined
  | prefixLength + 1, remainingLength + 1 => by
      let leftRaw := advanceFiniteCasePrefix subject prefixLength
        (remainingLength + 2)
      have htotal : prefixLength + (remainingLength + 2) =
          (prefixLength + 1) + (remainingLength + 1) := by
        omega
      let leftBranch := CertifiedPAContextProof.cast
        (congrArg
          (fun bound => finiteExhaustionFormula bound
            (successorOf subject)) htotal)
        leftRaw
      let nextEquality := proveSuccessorEqualityUnderCase
        prefixLength subject
      let casesProof := injectEqualityCase (prefixLength + 1)
        remainingLength (successorOf subject) nextEquality
      let rightBranch : CertifiedPAContextProof
          ({∼finiteCaseEqualityFormula
              (iteratedSuccessorTerm 0 prefixLength) subject} :
            Finset LO.FirstOrder.ArithmeticProposition)
          (finiteExhaustionFormula
            ((prefixLength + 1) + (remainingLength + 1))
            (successorOf subject)) := by
        unfold finiteExhaustionFormula
        apply CertifiedPAContextProof.disjunctionLeft
          (right := finiteLowerBoundFormula
            ((prefixLength + 1) + (remainingLength + 1))
            (successorOf subject))
        simpa only [Nat.add_succ] using casesProof
      let combined := CertifiedPAContextProof.eliminateDisjunctionAssumption
        (Gamma := ∅)
        (target := finiteExhaustionFormula
          ((prefixLength + 1) + (remainingLength + 1))
          (successorOf subject))
        (left := finiteEqualityCases subject prefixLength)
        (right := finiteCaseEqualityFormula
          (iteratedSuccessorTerm 0 prefixLength) subject)
        leftBranch rightBranch
      have hcontext :
          insert
              (∼(finiteEqualityCases subject prefixLength ⋎
                finiteCaseEqualityFormula
                  (iteratedSuccessorTerm 0 prefixLength) subject)) ∅ =
            ({∼finiteEqualityCases subject (prefixLength + 1)} :
              Finset LO.FirstOrder.ArithmeticProposition) := by
        rw [finiteEqualityCases_succ]
        ext formula
        simp
      let singletonCombined := CertifiedPAContextProof.castContext
        hcontext combined
      exact singletonCombined
termination_by prefixLength _ => prefixLength

def advanceAllFiniteCases
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof
      ({∼finiteEqualityCases subject bound} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteExhaustionFormula bound (successorOf subject)) :=
  advanceFiniteCasePrefix subject bound 0

def proveFiniteExhaustionSuccessorUnderAssumption
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAContextProof
      ({∼finiteExhaustionFormula bound subject} :
        Finset LO.FirstOrder.ArithmeticProposition)
      (finiteExhaustionFormula bound (successorOf subject)) :=
  CertifiedPAContextProof.eliminateDisjunctionAssumption
    (Gamma := ∅)
    (target := finiteExhaustionFormula bound (successorOf subject))
    (left := finiteEqualityCases subject bound)
    (right := finiteLowerBoundFormula bound subject)
    (advanceAllFiniteCases bound subject)
    (preserveLowerBoundBranch bound subject)

def proveFiniteExhaustionSuccessorImplication
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (finiteExhaustionFormula bound subject 🡒
        finiteExhaustionFormula bound (successorOf subject)) :=
  CertifiedPAContextProof.discharge
    (finiteExhaustionFormula bound subject)
    (finiteExhaustionFormula bound (successorOf subject))
    (proveFiniteExhaustionSuccessorUnderAssumption bound subject)

theorem proveFiniteExhaustionSuccessorImplication_verifier_eq_true
    (bound : Nat)
    (subject : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveFiniteExhaustionSuccessorImplication bound subject).code
      (compactFormulaCode
        (finiteExhaustionFormula bound subject 🡒
          finiteExhaustionFormula bound (successorOf subject))) = true :=
  (proveFiniteExhaustionSuccessorImplication bound subject).verifier_eq_true

#print axioms advanceFiniteCasePrefix
#print axioms proveFiniteExhaustionSuccessorImplication_verifier_eq_true

end FoundationCompactPAFiniteExhaustionSuccessor
