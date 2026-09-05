import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter04CodeBound

/-! # Syntax bound after closing the second cons-tail witness -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter03CodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources

theorem natListConsRowsTailBodyAfter03_code_length_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (h04 :
      (binaryFormulaCode
        (natListConsRowsTailBodyAfter04 tokenTable width tokenCount
          sourceBoundary targetBoundary)).length <=
        natListConsRowsTailBodyAfter04FormulaCodePolynomial numericBound
          bitBound) :
    (binaryFormulaCode
      (natListConsRowsTailBodyAfter03 tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      natListConsRowsTailBodyAfter03FormulaCodePolynomial numericBound
        bitBound := by
  have hraw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    tokenCount
    (natListConsRowsTailBodyAfter04FormulaCodePolynomial numericBound bitBound)
    (natListConsRowsTailBodyAfter04 tokenTable width tokenCount sourceBoundary
      targetBoundary) h04
  have hmono := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono 3
    htokenCount
    (Nat.le_refl
      (natListConsRowsTailBodyAfter04FormulaCodePolynomial numericBound
        bitBound))
  unfold natListConsRowsTailBodyAfter03
    natListConsRowsTailBodyAfter03FormulaCodePolynomial
  exact hraw.trans hmono

#print axioms natListConsRowsTailBodyAfter03_code_length_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter03CodeBound
