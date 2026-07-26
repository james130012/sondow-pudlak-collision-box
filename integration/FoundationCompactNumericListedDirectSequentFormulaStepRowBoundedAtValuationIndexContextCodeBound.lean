import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFreeVariables
import integration.FoundationCompactPAValuationContextSingletonCodeBound

/-! # Singleton-context bound for one open-index bounded sequent row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationContextSingletonCodeBound
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFreeVariables

def compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
    (numericBound : Nat) : Nat :=
  valuationContextFormulaCodeSumEnvelope 1 numericBound
    (binaryTermCode (&0 : ValuationTerm)).length

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_context_le
    (body : ArithmeticSemiformula Nat 18)
    (rowIndex numericBound : Nat)
    (hbodyVariables : body.freeVariables ⊆ {0})
    (hrowIndex : rowIndex <= numericBound) :
    formulaCodeSum
        (valuationContext
          body.freeVariables
          (extendValuation rowIndex
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)) <=
      compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound := by
  let valuation :=
    extendValuation rowIndex
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation
  have hvaluation : valuation 0 <= numericBound := by
    simpa only [valuation, extendValuation_zero] using hrowIndex
  exact valuationContext_formulaCodeSum_le_singleton body.freeVariables valuation
    numericBound hbodyVariables hvaluation

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_context_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
