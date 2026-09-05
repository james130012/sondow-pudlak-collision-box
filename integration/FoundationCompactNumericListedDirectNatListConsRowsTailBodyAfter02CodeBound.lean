import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter03CodeBound

/-! # Syntax bound after closing the third cons-tail witness -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 140000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter02CodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources

theorem natListConsRowsTailBodyAfter02_code_length_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (h03 :
      (binaryFormulaCode
        (natListConsRowsTailBodyAfter03 tokenTable width tokenCount
          sourceBoundary targetBoundary)).length <=
        natListConsRowsTailBodyAfter03FormulaCodePolynomial numericBound
          bitBound) :
    (binaryFormulaCode
      (natListConsRowsTailBodyAfter02 tokenTable width tokenCount
        sourceBoundary targetBoundary)).length <=
      natListConsRowsTailBodyAfter02FormulaCodePolynomial numericBound
        bitBound := by
  have hraw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    tokenCount
    (natListConsRowsTailBodyAfter03FormulaCodePolynomial numericBound bitBound)
    (natListConsRowsTailBodyAfter03 tokenTable width tokenCount sourceBoundary
      targetBoundary) h03
  have hmono := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono 2
    htokenCount
    (Nat.le_refl
      (natListConsRowsTailBodyAfter03FormulaCodePolynomial numericBound
        bitBound))
  unfold natListConsRowsTailBodyAfter02
    natListConsRowsTailBodyAfter02FormulaCodePolynomial
  exact hraw.trans hmono

#print axioms natListConsRowsTailBodyAfter02_code_length_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter02CodeBound
