import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFull21TerminalBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedPayload

/-! # Eighteen-witness installation from the fixed twenty-one-conjunct terminal -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFull21FullyFixedBound

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedProof
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedPayload
open FoundationCompactNumericListedDirectSequentFormulaStepFull21FullyFixedResources
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexFull21TerminalBound

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexFull21FullyFixedBoundOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound : Nat)
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
    (hvalueBound : Nat.size valueBound <= bitBound) :
    ExplicitDirectFormulaBound (extendValuation rowIndex
      FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation)
      (compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound (&0 : ValuationTerm))
      (compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedPayloadPolynomial
        numericBound valueBound bitBound
        (compactSequentFormulaStepTail01FullyFixedPayloadPolynomial tokenTable
          width tokenCount suffixCount valueCount numericBound bitBound valueBound
          data.row)) := by
  let terminal :=
    compactSequentFormulaStepRowBoundedAtValuationIndexFull21TerminalBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound data hrowIndex
      htokenCount hsuffixBoundary hvalueBoundary hvalueBound
  let certified :=
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedCompilationOfTerminal
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound numericBound bitBound
      (compactSequentFormulaStepTail01FullyFixedPayloadPolynomial tokenTable
        width tokenCount suffixCount valueCount numericBound bitBound valueBound
        data.row)
      data hrowIndex htokenTable hwidth htokenCount hsuffixBoundary hsuffixCount
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
      compactSequentFormulaStepRowBoundedAtValuationIndexExplicitFormula_eq_public
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueBound
  let proof := castValuationContextProof hformula rawProof
  refine { proof := proof, payloadLength_le := ?_ }
  dsimp only [proof]
  rw [castValuationContextProof_payloadLength_eq]
  apply castDirectCompilationProof_payloadLength_le certified.compilation
    sourceFormula certified.formula_eq
  simpa only [
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedPayloadPolynomial]
    using certified.resource_eq

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexFull21FullyFixedBoundOfData

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFull21FullyFixedBound
