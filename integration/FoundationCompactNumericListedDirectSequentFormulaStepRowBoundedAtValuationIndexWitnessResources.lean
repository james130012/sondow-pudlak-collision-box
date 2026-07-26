import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalBound
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18

/-! # Public resources for eighteen open-index row witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalBound

abbrev compactSequentFormulaStepRowBoundedAtValuationIndexRawBody
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount : Nat) : ArithmeticSemiformula Nat 18 :=
  compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal tokenTable
    width tokenCount suffixBoundary suffixCount valueBoundary valueCount
    (&0 : ValuationTerm)

def compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) : Nat :=
  formulaCodeSum
    (valuationContext
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount).freeVariables
      (extendValuation rowIndex
        FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation))

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 18
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex)
    valueBound
    (binaryFormulaCode
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount)).length
    (compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data)

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexContextCode_le_bound
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    formulaCodeSum
        (valuationContext
          (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody
            tokenTable width tokenCount suffixBoundary suffixCount
            valueBoundary valueCount).freeVariables
          (extendValuation rowIndex
            FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)) <=
      compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex := by
  rfl

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexContextCode_le_bound

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
