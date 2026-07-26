import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFormulaAlignment
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Public proof projected from the fully fixed eighteen-witness compilation -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedProof

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerOpaqueArity18
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedOfTerminal
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedProofOfTerminal
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
    CertifiedPAContextProof
      (valuationContext
        (compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueBound (&0 : ValuationTerm)).freeVariables
        (extendValuation rowIndex
          FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation))
      (compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound (&0 : ValuationTerm)) := by
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
      compactSequentFormulaStepRowBoundedAtValuationIndexExplicitFormula_eq_public
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount valueBound
  exact castValuationContextProof hformula rawProof

#print axioms
  compactSequentFormulaStepRowBoundedAtValuationIndexFullyFixedProofOfTerminal

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFullyFixedProof
