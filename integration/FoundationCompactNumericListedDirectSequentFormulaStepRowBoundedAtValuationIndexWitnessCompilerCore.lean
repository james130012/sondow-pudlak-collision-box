import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessResources

/-! # Certified compilation object for eighteen open-index row witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalBound

opaque
    compactSequentFormulaStepRowBoundedAtValuationIndexWitnessCompilationOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CertifiedPublicBoundedWitnessCompilationArity18
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex)
      valueBound
      (binaryFormulaCode
        (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount)).length
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount)
      (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row)
      (compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data) :=
  compileExplicitBoundedWitnessDirectPublicCertifiedOpaqueArity18
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCodeBound
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex)
    valueBound
    (binaryFormulaCode
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount)).length
    (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount)
    (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row)
    data.values_le (by rfl)
    (compactSequentFormulaStepRowBoundedAtValuationIndexContextCode_le_bound
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex)
    (compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data)
    (compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data)

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexWitnessCompilationOfData

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
