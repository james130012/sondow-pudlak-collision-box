import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessFormulaAlignment
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-! # Public open-index bounded-row proof projection -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactCertifiedContextProof
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedDirectCheckedData
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax

noncomputable def
    compactSequentFormulaStepRowBoundedAtValuationIndexProofOfData
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound : Nat)
    (data : CompactSequentFormulaStepRowBoundedDirectData tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowIndex
      valueBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
          width tokenCount suffixBoundary suffixCount valueBoundary valueCount
          valueBound (&0 : ValuationTerm)).freeVariables
        (extendValuation rowIndex zeroValuation))
      (compactSequentFormulaStepRowBoundedAtValuationIndexFormula tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        valueBound (&0 : ValuationTerm)) := by
  let sourceBound :=
    compactSequentFormulaStepRowBoundedAtValuationIndexExplicitWitnessBoundOfData
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex valueBound data
  exact castValuationContextProof
    (compactSequentFormulaStepRowBoundedAtValuationIndexExplicitFormula_eq_public
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount valueBound)
    sourceBound.proof

end FoundationCompactNumericListedDirectSequentFormulaStepRowBoundedAtValuationIndexWitnessCompiler
