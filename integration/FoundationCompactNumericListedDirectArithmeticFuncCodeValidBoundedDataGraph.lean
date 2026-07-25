import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase00
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase01
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase20
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase21

/-! # Graph construction of bounded valid-function-code data -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataGraph

open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase00
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase01
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase20
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataCase21

private abbrev funcCodeZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation

theorem arithmeticFuncCodeValidBoundedData_nonempty
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    Nonempty (ArithmeticFuncCodeValidBoundedData arity code) := by
  unfold ArithmeticFuncCodeValid at hvalid
  rcases hvalid with h00 | h01 | h20 | h21
  · exact ⟨arithmeticFuncCodeValidBoundedDataCase00 arity code h00⟩
  · exact ⟨arithmeticFuncCodeValidBoundedDataCase01 arity code h01⟩
  · exact ⟨arithmeticFuncCodeValidBoundedDataCase20 arity code h20⟩
  · exact ⟨arithmeticFuncCodeValidBoundedDataCase21 arity code h21⟩

noncomputable def arithmeticFuncCodeValidBoundedDataOfGraph
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    ArithmeticFuncCodeValidBoundedData arity code :=
  Classical.choice
    (arithmeticFuncCodeValidBoundedData_nonempty arity code hvalid)

noncomputable def
    compactAdditiveArithmeticFuncCodeValidFixedCertificateOfGraph
    (arity code : Nat) (hvalid : ArithmeticFuncCodeValid arity code) :
    CheckedHybridValuationBoundedFormulaCertificate funcCodeZeroValuation
      (compactAdditiveArithmeticFuncCodeValidClosedFormula arity code) :=
  .cast
    (compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment arity
      code).symm
    (arithmeticFuncCodeValidBoundedDataOfGraph arity code hvalid).certificate

end FoundationCompactNumericListedDirectArithmeticFuncCodeValidBoundedDataGraph
