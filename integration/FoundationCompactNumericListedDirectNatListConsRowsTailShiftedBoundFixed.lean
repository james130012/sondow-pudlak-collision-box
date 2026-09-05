import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
import integration.FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds

/-! # Fixed shifted-bound equality resource for the cons-tail universal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 180000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsTailShiftedBoundFixed

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerFixedPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate

private abbrev consRowsTailShiftedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation

def natListConsRowsTailShiftedBoundFixedScalePolynomial
    (numericBound bitBound : Nat) : Nat :=
  numericBound + binaryNumeralTermCodeEnvelope bitBound

def natListConsRowsTailShiftedBoundFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compileShiftedBoundEqualityFixedPayloadPolynomial
    (natListConsRowsTailShiftedBoundFixedScalePolynomial numericBound bitBound)

theorem natListConsRowsTailShiftedBoundResource_le_fullyFixed
    (sourceCount numericBound bitBound : Nat)
    (hsourceCount : sourceCount <= numericBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound) :
    compileShiftedBoundEqualityPayloadResource
        consRowsTailShiftedZeroValuation ∅
        (shortBinaryNumeralTerm sourceCount) <=
      natListConsRowsTailShiftedBoundFixedPayloadPolynomial numericBound
        bitBound := by
  let boundTerm : ValuationTerm := shortBinaryNumeralTerm sourceCount
  let scale := natListConsRowsTailShiftedBoundFixedScalePolynomial numericBound
    bitBound
  have hclosed : boundTerm.freeVariables = ∅ := by
    dsimp only [boundTerm]
    exact shortBinaryNumeralTerm_freeVariables_eq_empty sourceCount
  have hpublic :=
    compileShiftedBoundEqualityPayloadResource_le_publicPolynomial
      consRowsTailShiftedZeroValuation ∅ boundTerm hclosed
  have hcode : (binaryTermCode boundTerm).length <= scale := by
    have hraw := binaryNumeralTerm_code_length_le_envelope sourceCount
      bitBound hsourceCountSize
    dsimp only [boundTerm, scale]
    unfold natListConsRowsTailShiftedBoundFixedScalePolynomial
    omega
  have hfixed :=
    compileShiftedBoundEqualityPayloadPublicPolynomial_le_fixed_of_eq
      consRowsTailShiftedZeroValuation ∅ boundTerm
      (compileShiftedBoundEqualityPayloadPublicPolynomial
        consRowsTailShiftedZeroValuation ∅ boundTerm)
      (compileShiftedBoundEqualityFixedPayloadPolynomial scale)
      scale rfl rfl hclosed (by simp)
      (by
        dsimp only [consRowsTailShiftedZeroValuation]
        simp [
          FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate.zeroValuation,
          scale, natListConsRowsTailShiftedBoundFixedScalePolynomial])
      (by
        dsimp only [boundTerm]
        rw [termValue_shortBinaryNumeralTerm]
        dsimp only [scale]
        unfold natListConsRowsTailShiftedBoundFixedScalePolynomial
        omega)
      hcode
  unfold natListConsRowsTailShiftedBoundFixedPayloadPolynomial
  exact hpublic.trans hfixed

#print axioms natListConsRowsTailShiftedBoundResource_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsTailShiftedBoundFixed
