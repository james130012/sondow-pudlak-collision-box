import integration.FoundationCompactPAFiniteCaseSyntax
import integration.FoundationCompactPAQuantitativeOrder

/-!
# Certified strict increase by one

For every arithmetic term `t`, this module constructs a certified PA proof
of `t < t + 1`.  The proof specializes `0 < 1`, applies addition
monotonicity, and transports both endpoints through explicit equalities.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPATermSuccessorOrder

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAQuantitativeEqualityTransitivity
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAFiniteCaseSyntax

theorem finiteCaseZeroTerm_eq_paZeroTerm :
    finiteCaseZeroTerm 0 = paZeroTerm := by
  rfl

theorem finiteCaseOneTerm_eq_paOneTerm :
    finiteCaseOneTerm 0 = paOneTerm := by
  rfl

theorem finiteCaseAddTerm_eq_paAddTerm
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    finiteCaseAddTerm left right = paAddTerm left right := by
  unfold finiteCaseAddTerm paAddTerm
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

def proveZeroAddTermEqualsTerm
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!(paAddTerm paZeroTerm term) = !!term” :
        LO.FirstOrder.ArithmeticProposition) :=
  proveEqualityTransitivity
    (paAddTerm paZeroTerm term)
    (paAddTerm term paZeroTerm)
    term
    (proveAddCommutativity paZeroTerm term)
    (proveAddZeroAtPaZero term)

def proveTermLtPaSuccessor
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (“!!term < !!(paAddTerm term paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) :=
  let shifted := proveAddLtAdd paZeroTerm paOneTerm term proveZeroLtOne
  proveLtTransport
    (paAddTerm paZeroTerm term)
    (paAddTerm paOneTerm term)
    term
    (paAddTerm term paOneTerm)
    (proveZeroAddTermEqualsTerm term)
    (proveAddCommutativity paOneTerm term)
    shifted

theorem finiteCaseSuccessorLessThan_formula
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    (“!!term < !!(paAddTerm term paOneTerm)” :
        LO.FirstOrder.ArithmeticProposition) =
      finiteCaseLessThanFormula term
        (finiteCaseAddTerm term (finiteCaseOneTerm 0)) := by
  rw [finiteCaseLessThanFormula_eq_operator]
  rw [finiteCaseOneTerm_eq_paOneTerm]
  rw [finiteCaseAddTerm_eq_paAddTerm]

def proveTermLtSuccessor
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    CertifiedPAProof
      (finiteCaseLessThanFormula term
        (finiteCaseAddTerm term (finiteCaseOneTerm 0))) :=
  CertifiedPAProof.cast (finiteCaseSuccessorLessThan_formula term)
    (proveTermLtPaSuccessor term)

theorem proveTermLtSuccessor_verifier_eq_true
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    listedCompactCertifiedPAProofVerifier
      (proveTermLtSuccessor term).code
      (compactFormulaCode
        (finiteCaseLessThanFormula term
          (finiteCaseAddTerm term (finiteCaseOneTerm 0)))) = true :=
  (proveTermLtSuccessor term).verifier_eq_true

#print axioms proveTermLtSuccessor_verifier_eq_true

end FoundationCompactPATermSuccessorOrder
