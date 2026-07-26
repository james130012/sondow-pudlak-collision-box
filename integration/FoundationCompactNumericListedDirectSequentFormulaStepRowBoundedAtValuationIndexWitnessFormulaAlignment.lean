import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessExplicitBound
import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

/-! # Public formula alignment for the open-index bounded row -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexSyntax

theorem
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitFormula_eq_public
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound : Nat) :
    explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 18
        (compactSequentFormulaStepRowBoundedAtValuationIndexRawTerminal
          tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
          valueCount (&0 : ValuationTerm)) =
      compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound (&0 : ValuationTerm) := by
  exact
    (compactSequentFormulaStepRowBoundedAtValuationIndexFormula_alignment
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound (&0 : ValuationTerm)).symm

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
