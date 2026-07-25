import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataGraph

/-! # Fully fixed graph endpoint for valid arithmetic function codes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBounds

open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataGraph

theorem
    compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (arity code bitBound : Nat)
    (hvalid : ArithmeticFuncCodeValid arity code)
    (haritySize : Nat.size arity <= bitBound)
    (hcodeSize : Nat.size code <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph arity
          code hvalid) <=
      compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
        bitBound := by
  change hybridFormulaStructuralPayloadBound
      (arithmeticFuncCodeValidBoundedDataOfGraph arity code hvalid).certificate <=
    compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial bitBound
  exact
    (arithmeticFuncCodeValidBoundedDataOfGraph arity code hvalid).structuralPayloadBound_le
      bitBound haritySize hcodeSize

#print axioms
  compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBounds
