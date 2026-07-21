import integration.FoundationCompactPAContextualBoundedUniversalCompiler
import integration.FoundationCompactPAUnaryAtomicTransport

/-!
# Contextual bounded-universal compiler with an arbitrary bound term

The finite-exhaustion engine uses the canonical iterated-successor numeral as
its bound.  Real bounded-arithmetic formulas instead contain arbitrary
`0/1/+/*` bound terms.  This module transports an assumed original bound to
the canonical bound through a real contextual equality proof, applies the
finite compiler, discharges the original bound, and universally introduces
the eigenvariable.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAContextualTermBoundedUniversalCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactCertifiedContextDischarge
open FoundationCompactCertifiedContextUniversalIntroduction
open FoundationCompactPAContextualBoundedUniversalCompiler
open FoundationCompactPAContextualBoundedUniversalCompiler.CertifiedContextFiniteUniversalBranches
open FoundationCompactPAQuantitativeRelationCongruence
open FoundationCompactPAQuantitativeOrder
open FoundationCompactPAUnaryAtomicTransport

def termBoundFormula
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  finiteCaseLessThanFormula (#0) boundTerm

def freedTermBoundFormula
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    LO.FirstOrder.ArithmeticProposition :=
  finiteCaseLessThanFormula (&0) (Rew.free boundTerm)

def termBoundedUniversalBody
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    LO.FirstOrder.ArithmeticSemiformula Nat 1 :=
  LO.Arrow.arrow (termBoundFormula boundTerm) body

theorem termBoundFormula_free
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1) :
    Rewriting.free (termBoundFormula boundTerm) =
      freedTermBoundFormula boundTerm := by
  unfold termBoundFormula freedTermBoundFormula finiteCaseLessThanFormula
  simp only [Semiformula.rew_rel]
  rw [Matrix.fun_eq_vec_two (fun index =>
    Rew.free
      (![(#0 : LO.FirstOrder.ArithmeticSemiterm Nat 1), boundTerm] index))]
  rfl

theorem termBoundedUniversalBody_free
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    Rewriting.free (termBoundedUniversalBody boundTerm body) =
      LO.Arrow.arrow
        (freedTermBoundFormula boundTerm) (Rewriting.free body) := by
  unfold termBoundedUniversalBody
  rw [LogicalConnective.HomClass.map_imply]
  rw [termBoundFormula_free]

theorem binaryRelationFormula_lt_eq_finiteCaseLessThan
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0) :
    binaryRelationFormula Language.ORing.Rel.lt left right =
      finiteCaseLessThanFormula left right := by
  rw [binaryRelationFormula_lt_formula]
  rw [finiteCaseLessThanFormula_eq_operator]

/-! The supplied equality is an internal output of the valuation term
compiler: the canonical iterated numeral equals the freed original bound.
It is not an external proof-existence premise. -/
noncomputable def compileContextualTermBoundedUniversal
    {Gamma : Finset LO.FirstOrder.ArithmeticProposition}
    (bound : Nat)
    (boundTerm : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (boundEquality : CertifiedPAContextProof
      (Gamma.image Rewriting.shift)
      (“!!(iteratedSuccessorTerm 0 bound) =
        !!(Rew.free boundTerm)” :
        LO.FirstOrder.ArithmeticProposition))
    (branches : CertifiedContextFiniteUniversalBranches
      (Gamma.image Rewriting.shift) (Rewriting.free body) bound) :
    CertifiedPAContextProof Gamma
      (∀⁰ termBoundedUniversalBody boundTerm body) := by
  let shiftedGamma := Gamma.image Rewriting.shift
  let originalBound := freedTermBoundFormula boundTerm
  let canonicalBound := finiteBoundFormula bound
  let originalContext := insert (∼originalBound) shiftedGamma
  let underCanonical := branches.compileUnderBoundAssumption
  let canonicalImplication := contextualDischarge
    canonicalBound (Rewriting.free body) underCanonical
  let canonicalImplicationUnderOriginal : CertifiedPAContextProof
      originalContext
      (LO.Arrow.arrow canonicalBound (Rewriting.free body)) :=
    CertifiedPAContextProof.weakenContext canonicalImplication (by
      intro formula hformula
      exact Finset.mem_insert_of_mem hformula)
  let originalAssumption := CertifiedPAContextProof.assumption
    originalContext originalBound (Finset.mem_insert_self _ _)
  let boundBackward := CertifiedPAContextProof.equalitySymmetry
    (iteratedSuccessorTerm 0 bound) (Rew.free boundTerm)
    boundEquality
  let boundBackwardUnderOriginal : CertifiedPAContextProof originalContext
      (“!!(Rew.free boundTerm) =
        !!(iteratedSuccessorTerm 0 bound)” :
        LO.FirstOrder.ArithmeticProposition) :=
    CertifiedPAContextProof.weakenContext boundBackward (by
      intro formula hformula
      exact Finset.mem_insert_of_mem hformula)
  let subjectReflexivity := CertifiedPAContextProof.weakenCertified
    originalContext
    (FoundationCompactPABinaryNumeralAddition.proveEqualityReflexivityAtTerm
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0))
  let transportRaw := relationTransportImplicationFromEqualities
    Language.ORing.Rel.lt
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (Rew.free boundTerm)
    (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (iteratedSuccessorTerm 0 bound)
    subjectReflexivity boundBackwardUnderOriginal
  let transport : CertifiedPAContextProof originalContext
      (LO.Arrow.arrow originalBound canonicalBound) := by
    have horiginal := binaryRelationFormula_lt_eq_finiteCaseLessThan
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (Rew.free boundTerm)
    have hcanonical := binaryRelationFormula_lt_eq_finiteCaseLessThan
      (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
      (iteratedSuccessorTerm 0 bound)
    have hfinite : finiteCaseLessThanFormula
        (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
        (iteratedSuccessorTerm 0 bound) = canonicalBound := by
      rfl
    have hformula :
        (LO.Arrow.arrow
          (binaryRelationFormula Language.ORing.Rel.lt
            (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
            (Rew.free boundTerm))
          (binaryRelationFormula Language.ORing.Rel.lt
            (&0 : LO.FirstOrder.ArithmeticSemiterm Nat 0)
            (iteratedSuccessorTerm 0 bound))) =
        LO.Arrow.arrow originalBound canonicalBound := by
      rw [horiginal, hcanonical, hfinite]
      rfl
    exact CertifiedPAContextProof.cast hformula transportRaw
  let canonicalAssumption := CertifiedPAContextProof.modusPonens
    transport originalAssumption
  let bodyUnderOriginal := CertifiedPAContextProof.modusPonens
    canonicalImplicationUnderOriginal canonicalAssumption
  let originalImplication := contextualDischarge
    originalBound (Rewriting.free body) bodyUnderOriginal
  let freeBodyProof : CertifiedPAContextProof shiftedGamma
      (Rewriting.free (termBoundedUniversalBody boundTerm body)) :=
    CertifiedPAContextProof.cast
      (termBoundedUniversalBody_free boundTerm body).symm
      originalImplication
  exact contextualUniversalIntroduction
    (termBoundedUniversalBody boundTerm body) freeBodyProof

#print axioms compileContextualTermBoundedUniversal

end FoundationCompactPAContextualTermBoundedUniversalCompiler
