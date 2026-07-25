import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase21FixedBounds

/-! # Resource-carrying valid function-code case `(2,1)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase21

open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase21FixedBounds

theorem funcCodeValidCase21FixedPayloadEnvelope_le_full
    (bitBound : Nat) :
    funcCodeValidCase21FixedPayloadEnvelope bitBound <=
      compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
        bitBound := by
  unfold compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
  omega

theorem funcCodeValidCase21Certificate_structuralPayloadBound_le_full
    (arity code : Nat) (hpair : arity = 2 ∧ code = 1) :
    ∀ bitBound,
      Nat.size arity <= bitBound ->
      Nat.size code <= bitBound ->
      FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
          (funcCodeValidCase21Certificate arity code hpair) <=
        compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
          bitBound :=
  fun bitBound haritySize hcodeSize =>
    (funcCodeValidCase21Certificate_structuralPayloadBound_le_fixed arity
      code bitBound hpair haritySize hcodeSize).trans
        (funcCodeValidCase21FixedPayloadEnvelope_le_full bitBound)

noncomputable def arithmeticFuncCodeValidBoundedDataCase21
    (arity code : Nat) (hpair : arity = 2 ∧ code = 1) :
    ArithmeticFuncCodeValidBoundedData arity code :=
  ⟨funcCodeValidCase21Certificate arity code hpair,
    funcCodeValidCase21Certificate_structuralPayloadBound_le_full arity code
      hpair⟩

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase21
