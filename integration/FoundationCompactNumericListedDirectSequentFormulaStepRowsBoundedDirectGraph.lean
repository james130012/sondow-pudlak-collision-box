import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversal
import integration.FoundationCompactPAExponentialValuationContextCompilerBounds

/-! # Direct proof of the complete bounded sequent-row graph -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraph

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAExponentialValuationContextCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversal

private abbrev sequentRowsZeroValuation : Nat -> Nat :=
  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation

private noncomputable def
    compileCompactSequentFormulaStepRowsBoundedExponentialAtValuationDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (exponentialAtValuationFormula
        (shortBinaryNumeralTerm valueBound)
        (shortBinaryNumeralTerm tableWidth)) := by
  let raw := compileExponentialAtValuation sequentRowsZeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)
  have hvaluationContext :
      exponentialValuationContext sequentRowsZeroValuation
          (shortBinaryNumeralTerm valueBound)
          (shortBinaryNumeralTerm tableWidth) =
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          sequentRowsZeroValuation := by
    unfold exponentialValuationContext
    rw [exponentialAtValuationFormula_freeVariables]
  let atValuation := CertifiedPAContextProof.castContext
    hvaluationContext raw
  have hempty :
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          sequentRowsZeroValuation = ∅ := by
    rw [exponentialAtValuationFormula_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hempty atValuation

noncomputable def
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (compactSequentFormulaStepRowsBoundedExponentialClosedFormula tableWidth
        valueBound) := by
  let raw :=
    compileCompactSequentFormulaStepRowsBoundedExponentialAtValuationDirectContext
      tableWidth valueBound hvalueBound
  exact CertifiedPAContextProof.cast (by rfl) raw

def compactSequentFormulaStepRowsBoundedExponentialDirectResource
    (tableWidth valueBound : Nat) : Nat :=
  exponentialValuationCompilerPayloadPolynomial
    (compileExponentialAtValuationPayloadResource sequentRowsZeroValuation
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))

theorem
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext_payloadLength_le
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext
      tableWidth valueBound hvalueBound).payloadLength <=
      compactSequentFormulaStepRowsBoundedExponentialDirectResource tableWidth
        valueBound := by
  unfold
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold
    compileCompactSequentFormulaStepRowsBoundedExponentialAtValuationDirectContext
  unfold compactSequentFormulaStepRowsBoundedExponentialDirectResource
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.castContext_payloadLength]
  exact compileExponentialAtValuation_payloadLength_le_fixedPolynomial
    sequentRowsZeroValuation (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth) (by
        simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

def compactSequentFormulaStepRowsBoundedDirectClosedResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat)
    (hrows : ∀ rowIndex < rowCount,
      CompactSequentFormulaStepRowBounded tokenTable width tokenCount
        suffixBoundary suffixCount valueBoundary valueCount rowIndex
        valueBound) : Nat :=
  let exponentialFormula :=
    compactSequentFormulaStepRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).ballLT (shortBinaryNumeralTerm rowCount)
  compactSequentFormulaStepRowsBoundedExponentialDirectResource tableWidth
      valueBound +
    compactSequentFormulaStepRowsBoundedDirectUniversalResource tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowCount valueBound hrows +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

noncomputable def
    compileCompactSequentFormulaStepRowsBoundedDirectClosedContext
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat)
    (hgraph : CompactSequentFormulaStepRowsBoundedGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      tableWidth valueBound) :
    CertifiedPAContextProof ∅
      (compactSequentFormulaStepRowsBoundedDirectClosedFormula tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
        tableWidth valueBound) := by
  let exponentialProof :=
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactSequentFormulaStepRowsBoundedDirectClosedFormula_alignment
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound).symm
    raw

theorem
    compileCompactSequentFormulaStepRowsBoundedDirectClosedContext_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat)
    (hgraph : CompactSequentFormulaStepRowsBoundedGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      tableWidth valueBound) :
    (compileCompactSequentFormulaStepRowsBoundedDirectClosedContext tokenTable
      width tokenCount suffixBoundary suffixCount valueBoundary valueCount
      rowCount tableWidth valueBound hgraph).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectClosedResource tokenTable width
        tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
        tableWidth valueBound hgraph.2 := by
  let exponentialProof :=
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedExponentialDirectResource tableWidth
        valueBound :=
    compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectUniversalResource tokenTable
        width tokenCount suffixBoundary suffixCount valueBoundary valueCount
        rowCount valueBound hgraph.2 :=
    compileCompactSequentFormulaStepRowsBoundedDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold
    compileCompactSequentFormulaStepRowsBoundedDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold compactSequentFormulaStepRowsBoundedDirectClosedResource
    dsimp only
    omega)

#print axioms
  compileCompactSequentFormulaStepRowsBoundedExponentialDirectContext_payloadLength_le
#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectClosedContext
#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraph
