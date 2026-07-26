import integration.FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessResources

/-! # Installed row-independent terminal from the twenty-one-conjunct proof -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFull21UniformTerminalBound

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
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformResources
open FoundationCompactNumericListedDirectSequentFormulaStepFull21UniformBound

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexFull21UniformTerminalBoundOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound)
    (hrowIndex : rowIndex <= numericBound)
    (htokenCount : Nat.size tokenCount <= bitBound)
    (hsuffixBoundary : Nat.size suffixBoundary <= bitBound)
    (hvalueBoundary : Nat.size valueBoundary <= bitBound)
    (hvalueBound : Nat.size valueBound <= bitBound) :
    ExplicitDirectFormulaBound (extendValuation rowIndex zeroValuation)
      (compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
            coordinate))
      (compactSequentFormulaStepTail01UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount numericBound bitBound valueBound) := by
  let direct :=
    compactSequentFormulaStepDirectFormulaAtValuationIndexUniformResultOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound data hrowIndex
      htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let directFormula :=
    compactSequentFormulaStepDirectFormulaAtValuationIndex tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      (&0 : ValuationTerm) data.row
  let installedFormula :=
    compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount ⇜
      fun coordinate => shortBinaryNumeralTerm
        (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
          coordinate)
  have hformula : directFormula = installedFormula := by
    simpa only [directFormula, installedFormula,
      compactSequentFormulaStepRowBoundedAtOpenIndexRawBody] using
      (compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal_alignment
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount (&0 : ValuationTerm) data.row).symm
  let proof := castValuationContextProof hformula direct.bound.proof
  refine { proof := proof, payloadLength_le := ?_ }
  dsimp only [proof]
  rw [castValuationContextProof_payloadLength_eq]
  exact direct.bound.payloadLength_le

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexFull21UniformTerminalBoundOfData

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFull21UniformTerminalBound
