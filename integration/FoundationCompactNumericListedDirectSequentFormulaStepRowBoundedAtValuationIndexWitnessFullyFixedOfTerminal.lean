import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18

/-! # Certified fully fixed eighteen-witness assembly from a terminal bound -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFixedCodeBounds
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFreeVariables
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound

def compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
    (numericBound valueBound bitBound terminalResource : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 18
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound)
    valueBound
    (compactSequentFormulaStepRowBoundedAtValuationIndexRawBodyFixedCodeEnvelope
      bitBound)
    terminalResource

opaque
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedCompilationOfTerminal
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound terminalResource :
      Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenTable : Nat.size tokenTable <= bitBound)
    (hwidth : Nat.size width <= bitBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hsuffixCount : Nat.size suffixCount <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueCount : Nat.size valueCount <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound)
    (terminal : ExplicitDirectFormulaBound (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
            coordinate))
      terminalResource) :
    CertifiedPublicBoundedWitnessCompilationArity18
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
        numericBound)
      valueBound
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBodyFixedCodeEnvelope
        bitBound)
      (compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount)
      (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row)
      terminalResource := by
  let valuation := extendValuation rowIndex zeroValuation
  let body :=
    compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
  let values :=
    compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
  let contextCodeBound :=
    compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeEnvelope
      numericBound
  let bodyCodeBound :=
    compactSequentFormulaStepRowBoundedAtValuationIndexRawBodyFixedCodeEnvelope
      bitBound
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound := by
    dsimp only [body, bodyCodeBound]
    exact
      compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_code_length_le_fixed
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueBound bitBound htokenTable hwidth htokenCount
        hsuffixBoundary hsuffixCount hvalueBoundary hvalueCount hvalueBound
  have hbodyVariables : body.freeVariables ⊆ {0} := by
    dsimp only [body]
    exact
      compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_freeVariables_subset_singleton
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount
  have hcontextPublic :=
    compactSequentFormulaStepRowBoundedAtValuationIndexRawBody_context_le body
      rowIndex numericBound hbodyVariables hrowIndex
  have hcontext :
      formulaCodeSum (valuationContext body.freeVariables valuation) <=
        contextCodeBound := by
    simpa only [
      FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds.formulaCodeSum,
      FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum,
      valuation, contextCodeBound] using hcontextPublic
  exact compileExplicitBoundedWitnessDirectPublicCertifiedOpaqueArity18
    contextCodeBound valueBound bodyCodeBound body values data.values_le hbody
    hcontext terminalResource terminal

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedCompilationOfTerminal

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal
