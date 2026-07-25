import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase01FixedBounds

/-! # Resource-carrying valid function-code case `(0,1)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase01

open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase01FixedBounds

noncomputable def arithmeticFuncCodeValidBoundedDataCase01
    (arity code : Nat) (hpair : arity = 0 ∧ code = 1) :
    ArithmeticFuncCodeValidBoundedData arity code where
  certificate := funcCodeValidCase01Certificate arity code hpair
  structuralPayloadBound_le := by
    intro bitBound haritySize hcodeSize
    exact
      (funcCodeValidCase01Certificate_structuralPayloadBound_le_fixed arity
        code bitBound hpair haritySize hcodeSize).trans (by
          unfold
            compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
          omega)

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase01
