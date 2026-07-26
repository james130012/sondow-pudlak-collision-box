import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedProof

/-! # Payload bound for the fully fixed eighteen-witness proof -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedPayload

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedProof
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedProofOfTerminal_payloadLength_le
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
    (terminal : ExplicitDirectFormulaBound (extendValuation rowIndex
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)
      (compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
          tokenCount suffixBoundary suffixCount valueBoundary valueCount ⇜
        fun coordinate => shortBinaryNumeralTerm
          (compactSequentFormulaStepRowBoundedDirectWitnessValues data.row
            coordinate))
      terminalResource) :
    (compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedProofOfTerminal
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound terminalResource data
      hrowIndex htokenTable hwidth htokenCount hsuffixBoundary hsuffixCount
      hvalueBoundary hvalueCount hvalueBound terminal).payloadLength <=
      compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
        numericBound valueBound bitBound terminalResource := by
  let certified :=
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedCompilationOfTerminal
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound terminalResource data
      hrowIndex htokenTable hwidth htokenCount hsuffixBoundary hsuffixCount
      hvalueBoundary hvalueCount hvalueBound terminal
  let body :=
    compactSequentFormulaStepRowBoundedAtOpenIndexRawBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
  let sourceFormula :=
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18 body
  let rawProof := castDirectCompilationProof certified.compilation sourceFormula
    certified.formula_eq
  have hformula : sourceFormula =
      compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount valueBound
        (&0 : ValuationTerm) := by
    dsimp only [sourceFormula, body]
    unfold compactSequentFormulaStepRowBoundedAtOpenIndexRawBody
    exact
      FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler.compactSequentFormulaStepRowBoundedAtValuationIndexExplicitFormula_eq_public
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueBound
  unfold
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedProofOfTerminal
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le certified.compilation
    sourceFormula certified.formula_eq
  simpa only [
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedPayloadPolynomial]
    using certified.resource_eq

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedProofOfTerminal_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedPayload
