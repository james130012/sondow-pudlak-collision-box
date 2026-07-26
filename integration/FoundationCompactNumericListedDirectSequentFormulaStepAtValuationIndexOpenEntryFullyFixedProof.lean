import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFixedBounds
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Fixed proof object for one open-index table-entry leaf -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedProof

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFixedBounds

noncomputable def
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound
    (valuation : Nat -> Nat) (table width value : Nat)
    (indexTerm : ValuationTerm)
    (numericBound bitBound indexCodeBound : Nat)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hvaluation : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound)
    (hindexCode : (binaryTermCode indexTerm).length <= indexCodeBound)
    (hindex : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value) :
    ExplicitDirectFormulaBound valuation
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width) indexTerm
        (shortBinaryNumeralTerm value))
      (compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial numericBound
        bitBound indexCodeBound) := by
  let raw := compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound valuation
    table width value indexTerm hindex hentry
  have hresource :=
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound_resource_le_fixed
      valuation table width value indexTerm numericBound bitBound indexCodeBound
      hwidthValue hindexValue hvaluation htableSize hwidthSize hindexSize
      hvalueSize hindexCode hindex hentry
  refine { proof := raw.proof, payloadLength_le := ?_ }
  exact raw.payloadLength_le.trans hresource

#print axioms
  compactSequentFormulaStepFixedWidthEntryAtOpenIndexFullyFixedBound

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFullyFixedProof
