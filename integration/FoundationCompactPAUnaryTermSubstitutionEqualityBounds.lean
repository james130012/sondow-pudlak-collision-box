import integration.FoundationCompactPAUnaryTermSubstitutionEquality
import integration.FoundationCompactPABinaryNumeralAdditionBounds

/-!
# Fixed polynomial endpoint for unary-term equality transport

The recursive compiler already carries its exact structural payload bound.
This module compresses that bound to one fixed expression in the canonical
open-term code, the two substitution factors, and the input proof payload.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactPAUnaryTermSubstitutionEqualityBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationPudlakQuantitativeConditions
open FoundationCompactListedCertifiedVerifier
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAUnaryTermSubstitutionEquality

def unaryTermSubstitutionPayloadPolynomial
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterPayloadLength : Nat) : Nat :=
  (binaryTermCode term).length *
    (parameterPayloadLength +
      paPrimitiveCostEnvelope
        (unaryTermSubstitutionCodeEnvelope left right
          (binaryTermCode term).length))

theorem proveUnaryTermSubstitutionEquality_payloadLength_le_polynomial
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterEquality : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    (proveUnaryTermSubstitutionEquality
      term left right parameterEquality).payloadLength <=
      unaryTermSubstitutionPayloadPolynomial
        term left right parameterEquality.payloadLength := by
  let compilation := compileUnaryTermSubstitutionEquality
    term left right parameterEquality
      (binaryTermCode term).length le_rfl
  have hraw := compilation.payloadLength_le
  have hsymbols := termSymbolCount_le_binaryTermCode_length term
  change compilation.proof.payloadLength <= _
  unfold unaryTermSubstitutionPayloadPolynomial
  exact hraw.trans (Nat.mul_le_mul_right _ hsymbols)

theorem proveUnaryTermSubstitutionEquality_checked_polynomial
    (term : LO.FirstOrder.ArithmeticSemiterm Nat 1)
    (left right : LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (parameterEquality : CertifiedPAProof
      (“!!left = !!right” : LO.FirstOrder.ArithmeticProposition)) :
    listedCompactCertifiedPAProofVerifier
        (proveUnaryTermSubstitutionEquality
          term left right parameterEquality).code
        (compactFormulaCode
          (“!!(instantiateUnaryTerm term left) =
            !!(instantiateUnaryTerm term right)” :
            LO.FirstOrder.ArithmeticProposition)) = true ∧
      (proveUnaryTermSubstitutionEquality
        term left right parameterEquality).payloadLength <=
        unaryTermSubstitutionPayloadPolynomial
          term left right parameterEquality.payloadLength :=
  ⟨proveUnaryTermSubstitutionEquality_verifier_eq_true
      term left right parameterEquality,
    proveUnaryTermSubstitutionEquality_payloadLength_le_polynomial
      term left right parameterEquality⟩

#print axioms proveUnaryTermSubstitutionEquality_payloadLength_le_polynomial
#print axioms proveUnaryTermSubstitutionEquality_checked_polynomial

end FoundationCompactPAUnaryTermSubstitutionEqualityBounds
