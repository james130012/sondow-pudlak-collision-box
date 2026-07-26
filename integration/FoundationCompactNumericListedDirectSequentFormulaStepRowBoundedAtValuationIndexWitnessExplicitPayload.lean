import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessExplicitProof

/-! # Payload bound for the explicit open-index witness proof -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalBound

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessProof_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    (compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessProofOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data).payloadLength <=
      compactSequentFormulaStepRowBoundedAtValuationIndexWitnessPayloadEnvelope
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data := by
  let certified :=
    compactSequentFormulaStepRowBoundedAtValuationIndexWitnessCompilationOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  let target :=
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawBody tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount)
  change
    (castDirectCompilationProof certified.compilation target
      certified.formula_eq).payloadLength <= _
  apply
    castDirectCompilationProof_payloadLength_le certified.compilation target
      certified.formula_eq
  change certified.compilation.payloadResource =
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
  exact certified.resource_eq

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessProof_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
