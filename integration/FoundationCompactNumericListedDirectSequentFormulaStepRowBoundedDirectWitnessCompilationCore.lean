import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalBound
import integration.FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18

/-! # Opaque compilation object for eighteen bounded sequent-step witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilationCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectFreeVariables
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectTerminalBound

def compactSequentFormulaStepRowBoundedDirectWitnessRawBody
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    ArithmeticSemiformula Nat 18 :=
  compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex

def compactSequentFormulaStepRowBoundedDirectWitnessTerminalResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) : Nat :=
  compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    data.row

theorem compactSequentFormulaStepRowBoundedDirectWitnessRawBody_context_le_zero
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat) :
    formulaCodeSum
        (valuationContext
          (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
            tokenCount suffixBoundary suffixCount valueBoundary valueCount
            rowIndex).freeVariables
          compactSequentFormulaStepRowBoundedDirectZeroValuation) <= 0 := by
  rw [
    compactSequentFormulaStepRowBoundedDirectRawTerminal_freeVariables_eq_empty]
  simp [valuationContext, formulaCodeSum]

opaque
    compactSequentFormulaStepRowBoundedDirectWitnessCompilationOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CertifiedPublicBoundedWitnessCompilationArity18
      compactSequentFormulaStepRowBoundedDirectZeroValuation
      0 valueBound
      (binaryFormulaCode
        (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount
          rowIndex)).length
      (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
      (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row)
      (compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
        data.row) :=
  compileExplicitBoundedWitnessDirectPublicCertifiedOpaqueArity18
    0 valueBound
    (binaryFormulaCode
      (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowIndex)).length
    (compactSequentFormulaStepRowBoundedDirectRawTerminal tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex)
    (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row)
    data.values_le (by rfl)
    (compactSequentFormulaStepRowBoundedDirectWitnessRawBody_context_le_zero
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex)
    (compactSequentFormulaStepDirectPublicPayloadEnvelope tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      data.row)
    (compactSequentFormulaStepRowBoundedInstalledTerminalBoundOfGraph tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowIndex data.row data.graph)

#print axioms
  compactSequentFormulaStepRowBoundedDirectWitnessRawBody_context_le_zero

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectWitnessCompilationCore
