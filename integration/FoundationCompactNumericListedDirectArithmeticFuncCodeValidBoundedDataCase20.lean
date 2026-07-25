import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase20FixedBounds

/-! # Resource-carrying valid function-code case `(2,0)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase20

open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase20FixedBounds

theorem funcCodeValidCase20FixedPayloadEnvelope_le_full
    (bitBound : Nat) :
    funcCodeValidCase20FixedPayloadEnvelope bitBound <=
      compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
        bitBound := by
  unfold compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
  omega

theorem funcCodeValidCase20Certificate_structuralPayloadBound_le_full
    (arity code : Nat) (hpair : arity = 2 ∧ code = 0) :
    ∀ bitBound,
      Nat.size arity <= bitBound ->
      Nat.size code <= bitBound ->
      FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate.hybridFormulaStructuralPayloadBound
          (funcCodeValidCase20Certificate arity code hpair) <=
        compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
          bitBound :=
  fun bitBound haritySize hcodeSize =>
    (funcCodeValidCase20Certificate_structuralPayloadBound_le_fixed arity
      code bitBound hpair haritySize hcodeSize).trans
        (funcCodeValidCase20FixedPayloadEnvelope_le_full bitBound)

noncomputable def arithmeticFuncCodeValidBoundedDataCase20
    (arity code : Nat) (hpair : arity = 2 ∧ code = 0) :
    ArithmeticFuncCodeValidBoundedData arity code :=
  ⟨funcCodeValidCase20Certificate arity code hpair,
    funcCodeValidCase20Certificate_structuralPayloadBound_le_full arity code
      hpair⟩

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase20
