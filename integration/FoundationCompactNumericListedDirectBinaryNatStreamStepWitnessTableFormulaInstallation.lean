import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge
import integration.FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation

/-!
# Installation of the bounded stream-step witness-table formula

The canonical proof-stream and formula-stream tables now satisfy the actual
handwritten Delta-zero formula, not merely the equivalent meta-level table
graph.  Their table-code size bounds are preserved unchanged.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaInstallation

open FoundationCompactAdditiveTokenCodec
open FoundationCompactBinaryNatStreamMachine
open FoundationCompactPackedTokenStreamDirectTrace
open FoundationCompactNumericListedDirectTrace
open FoundationCompactNumericListedDirectTraceCode
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectBinaryNatStreamStepInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTable
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableInstallation
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaBridge

theorem adjacentStepGraphRows_exists_boundedWitnessTableFormula
    {tokenTable width tokenCount stateBoundary : Nat}
    {states : List BinaryNatStreamState}
    (hadjacent : CompactBinaryNatStreamStateListAdjacentStepGraphRows
      tokenTable width tokenCount stateBoundary states) :
    ∃ table,
      Nat.size table ≤
        (states.length - 1) *
          compactBinaryNatStreamStepWitnessColumnCount *
          compactBinaryNatStreamStepWitnessPublicWidth tokenCount ∧
      compactBinaryNatStreamStepWitnessTableBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount,
          compactBinaryNatStreamStepWitnessPublicWidth tokenCount,
          table, states.length - 1,
          2 ^ compactBinaryNatStreamStepWitnessPublicWidth tokenCount] := by
  rcases adjacentStepGraphRows_exists_boundedWitnessTable hadjacent with
    ⟨table, htableSize, htableGraph⟩
  refine ⟨table, htableSize, ?_⟩
  apply (compactBinaryNatStreamStepWitnessTableBoundedGraphDef_eval_iff_tableGraph
    tokenTable width tokenCount
      (compactBinaryNatStreamStepWitnessPublicWidth tokenCount)
      table (states.length - 1)).mpr
  exact htableGraph

theorem compactNumericListedDirectTrace_packedStream_boundedWitnessTableFormulas
    (code formulaCode : Nat) (trace : CompactNumericListedDirectTrace)
    (hvalid : CompactNumericListedDirectTraceValid
      code formulaCode trace) :
    let tokens := compactNumericListedDirectTraceTokens trace
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let tableWidth :=
      compactBinaryNatStreamStepWitnessPublicWidth tokens.length
    let proofStates :=
      (compactNumericDirectTraceCertifiedStreamTrace trace).2
    let formulaStates :=
      (compactNumericDirectTraceFormulaStreamTrace trace).2
    ∃ proofStepTable formulaStepTable,
      Nat.size proofStepTable ≤
          (proofStates.length - 1) *
            compactBinaryNatStreamStepWitnessColumnCount * tableWidth ∧
      compactBinaryNatStreamStepWitnessTableBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokens.length, tableWidth,
          proofStepTable, proofStates.length - 1, 2 ^ tableWidth] ∧
      Nat.size formulaStepTable ≤
          (formulaStates.length - 1) *
            compactBinaryNatStreamStepWitnessColumnCount * tableWidth ∧
      compactBinaryNatStreamStepWitnessTableBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokens.length, tableWidth,
          formulaStepTable, formulaStates.length - 1, 2 ^ tableWidth] := by
  let tokens := compactNumericListedDirectTraceTokens trace
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let tableWidth :=
    compactBinaryNatStreamStepWitnessPublicWidth tokens.length
  let proofStates :=
    (compactNumericDirectTraceCertifiedStreamTrace trace).2
  let formulaStates :=
    (compactNumericDirectTraceFormulaStreamTrace trace).2
  rcases compactNumericListedDirectTrace_packedStream_boundedWitnessTables
      code formulaCode trace hvalid with
    ⟨proofStepTable, formulaStepTable,
      hproofSize, hproofGraph, hformulaSize, hformulaGraph⟩
  refine ⟨proofStepTable, formulaStepTable,
    hproofSize, ?_, hformulaSize, ?_⟩
  · apply (compactBinaryNatStreamStepWitnessTableBoundedGraphDef_eval_iff_tableGraph
      tokenTable width tokens.length tableWidth
        proofStepTable (proofStates.length - 1)).mpr
    exact hproofGraph
  · apply (compactBinaryNatStreamStepWitnessTableBoundedGraphDef_eval_iff_tableGraph
      tokenTable width tokens.length tableWidth
        formulaStepTable (formulaStates.length - 1)).mpr
    exact hformulaGraph

#print axioms adjacentStepGraphRows_exists_boundedWitnessTableFormula
#print axioms compactNumericListedDirectTrace_packedStream_boundedWitnessTableFormulas

end FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessTableFormulaInstallation
