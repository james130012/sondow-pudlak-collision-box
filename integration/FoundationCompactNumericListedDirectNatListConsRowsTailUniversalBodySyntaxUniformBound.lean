import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter02CodeBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter04CodeBound

/-! # Fixed syntax bound for the one-variable cons-tail universal body -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectRecursiveBodyMonotonicity
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyDefinitions
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodyPolynomialResources
open FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter04CodeBound
open FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter03CodeBound
open FoundationCompactNumericListedDirectNatListConsRowsTailBodyAfter02CodeBound

theorem compactAdditiveNatListConsRowsTailBody_code_length_le_uniform
    (tokenTable width tokenCount sourceBoundary targetBoundary numericBound
      bitBound : Nat)
    (htokenCount : tokenCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound) :
    (binaryFormulaCode
      (FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.compactAdditiveNatListConsRowsTailBody
        tokenTable width tokenCount sourceBoundary targetBoundary)).length <=
      natListConsRowsTailUniversalBodyFormulaCodePolynomial numericBound
        bitBound := by
  have h04 := natListConsRowsTailBodyAfter04_code_length_le_uniform tokenTable
    width tokenCount sourceBoundary targetBoundary numericBound bitBound
    htokenCount htokenTableSize hwidthSize htokenCountSize hsourceBoundarySize
    htargetBoundarySize
  have h03 := natListConsRowsTailBodyAfter03_code_length_le_uniform tokenTable
    width tokenCount sourceBoundary targetBoundary numericBound bitBound
    htokenCount h04
  have h02 := natListConsRowsTailBodyAfter02_code_length_le_uniform tokenTable
    width tokenCount sourceBoundary targetBoundary numericBound bitBound
    htokenCount h03
  have hraw := explicitBoundedWitnessRecursiveBody_code_length_le_public
    tokenCount
    (natListConsRowsTailBodyAfter02FormulaCodePolynomial numericBound bitBound)
    (natListConsRowsTailBodyAfter02 tokenTable width tokenCount sourceBoundary
      targetBoundary) h02
  have hmono := explicitBoundedWitnessRecursiveBodyPublicCodeEnvelope_mono 1
    htokenCount
    (Nat.le_refl
      (natListConsRowsTailBodyAfter02FormulaCodePolynomial numericBound
        bitBound))
  rw [compactAdditiveNatListConsRowsTailBody_eq_after01]
  unfold natListConsRowsTailBodyAfter01
    natListConsRowsTailUniversalBodyFormulaCodePolynomial
  exact hraw.trans hmono

#print axioms compactAdditiveNatListConsRowsTailBody_code_length_le_uniform

end FoundationCompactNumericListedDirectNatListConsRowsTailUniversalBodySyntaxUniformBound
