import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

/-! # Resource-carrying checked data for valid arithmetic function codes -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

structure ArithmeticFuncCodeValidBoundedData (arity code : Nat) where
  certificate :
    CheckedHybridValuationBoundedFormulaCertificate funcCodeZeroValuation
      (compactAdditiveArithmeticFuncCodeValidExplicitFormula arity code)
  structuralPayloadBound_le :
    ∀ bitBound,
      Nat.size arity <= bitBound ->
      Nat.size code <= bitBound ->
      hybridFormulaStructuralPayloadBound certificate <=
        compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
          bitBound

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
