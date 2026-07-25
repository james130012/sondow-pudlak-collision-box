import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase00FixedBounds

/-! # Resource-carrying valid function-code case `(0,0)` -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase00

open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidCase00FixedBounds

noncomputable def arithmeticFuncCodeValidBoundedDataCase00
    (arity code : Nat) (hpair : arity = 0 ∧ code = 0) :
    ArithmeticFuncCodeValidBoundedData arity code where
  certificate := funcCodeValidCase00Certificate arity code hpair
  structuralPayloadBound_le := by
    intro bitBound haritySize hcodeSize
    exact
      (funcCodeValidCase00Certificate_structuralPayloadBound_le_fixed arity
        code bitBound hpair haritySize hcodeSize).trans (by
          unfold
            compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
          omega)

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase00
