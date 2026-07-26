import integration.FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Installed terminal bound for a bounded row at an open index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalBound

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalAlignment
open FoundationCompactNumericListedDirectSequentFormulaStepAtValuationIndexDirectCompiler

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) : Nat :=
  (compactSequentFormulaStepAtValuationIndexDirectBoundOfGraph tokenTable width
    tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
    data.row data.graph).resource

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalBoundOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    ExplicitDirectFormulaBound
      (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount (&0 : ValuationTerm) ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
            coordinate)))
      (compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowIndex valueBound data) := by
  let directBound :=
    compactSequentFormulaStepAtValuationIndexDirectBoundOfGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      data.row data.graph
  let directFormula :=
    compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      (&0 : ValuationTerm) data.row
  let installedFormula :=
    compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      (&0 : ValuationTerm) ⇜
        (fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
            coordinate))
  have hformula : directFormula = installedFormula := by
    simpa only [directFormula, installedFormula] using
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal_alignment
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount (&0 : ValuationTerm) data.row).symm
  let proof := castValuationContextProof hformula directBound.proof
  refine
    { proof := proof
      payloadLength_le := ?_ }
  change proof.payloadLength <=
    compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  rw [show proof.payloadLength = directBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula directBound.proof]
  simpa only [
    compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalResource,
    directBound] using directBound.payloadLength_le

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexInstalledTerminalBoundOfData

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexTerminalBound
