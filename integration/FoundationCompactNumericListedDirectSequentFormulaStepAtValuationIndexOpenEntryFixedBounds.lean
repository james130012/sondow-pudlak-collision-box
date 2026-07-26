import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompilerCore
import integration.FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds

/-!
# Fixed resource for the six open-index table-entry leaves

The row index remains an actual open term.  This module removes the concrete
table, width, value, and valuation data from the resource bound, retaining only
shared numeric, bit-width, and index-term-code coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryOpenIndexTermUniformCeilingBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

def compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial
    (numericBound bitBound indexCodeBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtTermCoordinate numericBound bitBound
        indexCodeBound))

theorem
    compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound_resource_le_fixed
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
    (compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound valuation table
      width value indexTerm hindex hentry).resource <=
      compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial
        numericBound bitBound indexCodeBound := by
  change
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
        valuation (shortBinaryNumeralTerm table)
          (shortBinaryNumeralTerm width) indexTerm
          (shortBinaryNumeralTerm value) <=
      compactSequentFormulaStepOpenEntryFullyFixedPayloadPolynomial
        numericBound bitBound indexCodeBound
  exact
    compactFixedWidthEntryAtValuationOpenIndexShortNumeralsAtTermStructuralPayloadPolynomial_le_uniform
      valuation table width value indexTerm numericBound bitBound
      indexCodeBound hwidthValue hindexValue hvaluation htableSize hwidthSize
      hindexSize hvalueSize hindexCode hindex

#print axioms
  compactSequentFormulaStepFixedWidthEntryAtOpenIndexBound_resource_le_fixed

end FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexOpenEntryFixedBounds
