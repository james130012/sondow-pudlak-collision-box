import integration.FoundationCompactPAClosedAtomicCompiler
import integration.FoundationCompactPABoundedUniversalCompiler

/-!
# Proof-producing compiler for checked closed bounded formulas

This module is the structural layer above the closed atomic-literal compiler.
Its certificate contains only checked atomic truth, connective choices, and an
explicit closed witness for an existential.  It never stores a PA derivation,
a proof code, or a proof-length premise.

The bounded-universal constructor is backed by the genuine finite-exhaustion
compiler, not by a proof-existence field.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPABoundedFormulaCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactCertifiedDisjunction
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactPAClosedAtomicCompiler
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm
open FoundationCompactPAClosedAtomicCompiler.ClosedPATerm.ClosedPAAtomicLiteral
open FoundationCompactPABoundedUniversalCompiler
open FoundationCompactPABoundedUniversalCompiler.CheckedFiniteBoundedUniversalCertificate

/-- A proof-free truth certificate for the currently supported closed bounded
formula fragment.  Every constructor records the exact formula it certifies. -/
inductive CheckedClosedBoundedFormulaCertificate :
    LO.FirstOrder.ArithmeticProposition → Type
  | verum : CheckedClosedBoundedFormulaCertificate
      (⊤ : LO.FirstOrder.ArithmeticProposition)
  | atomic (literal : ClosedPAAtomicLiteral)
      (hvalue : literal.Truth) :
      CheckedClosedBoundedFormulaCertificate literal.formula
  | conjunction
      {left right : LO.FirstOrder.ArithmeticProposition}
      (leftCertificate : CheckedClosedBoundedFormulaCertificate left)
      (rightCertificate : CheckedClosedBoundedFormulaCertificate right) :
      CheckedClosedBoundedFormulaCertificate (left ⋏ right)
  | disjunctionLeft
      {left right : LO.FirstOrder.ArithmeticProposition}
      (leftCertificate : CheckedClosedBoundedFormulaCertificate left) :
      CheckedClosedBoundedFormulaCertificate (left ⋎ right)
  | disjunctionRight
      {left right : LO.FirstOrder.ArithmeticProposition}
      (rightCertificate : CheckedClosedBoundedFormulaCertificate right) :
      CheckedClosedBoundedFormulaCertificate (left ⋎ right)
  | existsWitness
      (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
      (witness : ClosedPATerm)
      (bodyCertificate : CheckedClosedBoundedFormulaCertificate
        (body/[witness.term])) :
      CheckedClosedBoundedFormulaCertificate (∃⁰ body)
  | boundedUniversal
      {bound : Nat}
      {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
      (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
      CheckedClosedBoundedFormulaCertificate
        (∀⁰ finiteBoundedUniversalBody bound body)

namespace CheckedClosedBoundedFormulaCertificate

/-- Compile a proof-free structural truth certificate into a real Foundation
`Derivation2 PA` paired with the exact certificate accepted by the public
compact verifier. -/
noncomputable def compile :
    {formula : LO.FirstOrder.ArithmeticProposition} →
    CheckedClosedBoundedFormulaCertificate formula →
    CertifiedPAProof formula
  | _, .verum => CertifiedPAProof.verumProof
  | _, .atomic literal hvalue => literal.compile hvalue
  | _, .conjunction leftCertificate rightCertificate =>
      CertifiedPAProof.conjunction
        leftCertificate.compile rightCertificate.compile
  | _, .disjunctionLeft leftCertificate =>
      FoundationCompactCertifiedDisjunction.disjunctionLeft
        leftCertificate.compile
  | _, .disjunctionRight rightCertificate =>
      FoundationCompactCertifiedDisjunction.disjunctionRight
        rightCertificate.compile
  | _, .existsWitness body witness bodyCertificate =>
      CertifiedPAProof.existsIntro witness.term bodyCertificate.compile
  | _, .boundedUniversal certificate => certificate.compile

theorem compile_verifier_eq_true
    {formula : LO.FirstOrder.ArithmeticProposition}
    (certificate : CheckedClosedBoundedFormulaCertificate formula) :
    listedCompactCertifiedPAProofVerifier
      certificate.compile.code (compactFormulaCode formula) = true :=
  certificate.compile.verifier_eq_true

theorem atomic_compile_eq
    (literal : ClosedPAAtomicLiteral) (hvalue : literal.Truth) :
    (CheckedClosedBoundedFormulaCertificate.atomic literal hvalue).compile =
      literal.compile hvalue := by
  rfl

theorem conjunction_compile_eq
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftCertificate : CheckedClosedBoundedFormulaCertificate left)
    (rightCertificate : CheckedClosedBoundedFormulaCertificate right) :
    (CheckedClosedBoundedFormulaCertificate.conjunction
      leftCertificate rightCertificate).compile =
      CertifiedPAProof.conjunction
        leftCertificate.compile rightCertificate.compile := by
  rfl

theorem disjunctionLeft_compile_eq
    {left right : LO.FirstOrder.ArithmeticProposition}
    (leftCertificate : CheckedClosedBoundedFormulaCertificate left) :
    (CheckedClosedBoundedFormulaCertificate.disjunctionLeft
      (right := right) leftCertificate).compile =
      FoundationCompactCertifiedDisjunction.disjunctionLeft
        leftCertificate.compile := by
  rfl

theorem disjunctionRight_compile_eq
    {left right : LO.FirstOrder.ArithmeticProposition}
    (rightCertificate : CheckedClosedBoundedFormulaCertificate right) :
    (CheckedClosedBoundedFormulaCertificate.disjunctionRight
      (left := left) rightCertificate).compile =
      FoundationCompactCertifiedDisjunction.disjunctionRight
        rightCertificate.compile := by
  rfl

theorem existsWitness_compile_eq
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : ClosedPATerm)
    (bodyCertificate : CheckedClosedBoundedFormulaCertificate
      (body/[witness.term])) :
    (CheckedClosedBoundedFormulaCertificate.existsWitness
      body witness bodyCertificate).compile =
      CertifiedPAProof.existsIntro
        witness.term bodyCertificate.compile := by
  rfl

theorem boundedUniversal_compile_eq
    {bound : Nat}
    {body : LO.FirstOrder.ArithmeticSemiformula Nat 1}
    (certificate : CheckedFiniteBoundedUniversalCertificate bound body) :
    (CheckedClosedBoundedFormulaCertificate.boundedUniversal
      certificate).compile = certificate.compile := by
  rfl

#print axioms compile_verifier_eq_true

end CheckedClosedBoundedFormulaCertificate

end FoundationCompactPABoundedFormulaCompiler
