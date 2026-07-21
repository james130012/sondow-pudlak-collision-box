import integration.FoundationCompactCertifiedContextConnectives
import integration.FoundationCompactPATermSuccessorOrder

/-!
# Transporting a lower bound through successor

The central implication is `(x + 1 < B) -> (x < B)`, obtained from
`x < x + 1` and strict-order transitivity.  Contextual modus tollens then
turns any proof of `B ≤ x` into a proof of `B ≤ x + 1`.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPALowerBoundSuccessor

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAQuantitativeOrder
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPATermSuccessorOrder

def successorOf
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticSemiterm Nat 0 :=
  finiteCaseAddTerm term (finiteCaseOneTerm 0)

def successorLessThanFormula
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!(successorOf term) < !!bound” :
    LO.FirstOrder.ArithmeticProposition)

def termLessThanFormula
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    LO.FirstOrder.ArithmeticProposition :=
  (“!!term < !!bound” : LO.FirstOrder.ArithmeticProposition)

def proveSuccessorLessThanImpliesLessThan
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (successorLessThanFormula term bound 🡒
        termLessThanFormula term bound) := by
  let Gamma : Finset LO.FirstOrder.ArithmeticProposition :=
    {∼successorLessThanFormula term bound}
  let successorAssumption := CertifiedPAContextProof.assumption
    Gamma (successorLessThanFormula term bound) (by simp [Gamma])
  let termSuccessorRaw := proveTermLtSuccessor term
  let termSuccessor : CertifiedPAProof
      (“!!term < !!(successorOf term)” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAProof.cast
      (finiteCaseSuccessorLessThan_formula term).symm termSuccessorRaw
  let contextualTermSuccessor :=
    CertifiedPAContextProof.weakenCertified Gamma termSuccessor
  let antecedentProof := CertifiedPAContextProof.conjunction
    contextualTermSuccessor successorAssumption
  let implicationProof := CertifiedPAContextProof.weakenCertified Gamma
    (ltTransImplication term (successorOf term) bound)
  let result := CertifiedPAContextProof.modusPonens
    implicationProof antecedentProof
  exact CertifiedPAContextProof.discharge
    (successorLessThanFormula term bound)
    (termLessThanFormula term bound) result

def liftLowerBoundThroughSuccessor
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (lowerBoundProof : CertifiedPAContextProof Gamma
      (∼termLessThanFormula term bound)) :
    CertifiedPAContextProof Gamma
      (∼successorLessThanFormula term bound) :=
  CertifiedPAContextProof.modusTollens
    (CertifiedPAContextProof.weakenCertified Gamma
      (proveSuccessorLessThanImpliesLessThan term bound))
    lowerBoundProof

theorem proveSuccessorLessThanImpliesLessThan_verifier_eq_true
    (term bound : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveSuccessorLessThanImpliesLessThan term bound).code
      (compactFormulaCode
        (successorLessThanFormula term bound 🡒
          termLessThanFormula term bound)) = true :=
  (proveSuccessorLessThanImpliesLessThan term bound).verifier_eq_true

#print axioms proveSuccessorLessThanImpliesLessThan_verifier_eq_true
#print axioms liftLowerBoundThroughSuccessor

end FoundationCompactPALowerBoundSuccessor
