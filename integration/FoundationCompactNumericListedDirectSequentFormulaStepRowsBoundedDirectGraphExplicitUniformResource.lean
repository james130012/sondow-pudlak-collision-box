import integration.FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalExplicitUniformResource
import integration.FoundationCompactPAExponentialValuationContextCompilerBounds

/-! # Complete bounded sequent-row graph with an explicit uniform resource -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraphExplicitUniformResource

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAExponentialValuationContextCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepBoundedFormula
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectUniversalExplicitUniformResource

private abbrev sequentRowsExplicitUniformZeroValuation : Nat -> Nat :=
  FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler.zeroValuation

private noncomputable def
    compileCompactSequentFormulaStepRowsBoundedExponentialAtValuationExplicitUniformContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (exponentialAtValuationFormula
        (shortBinaryNumeralTerm valueBound)
        (shortBinaryNumeralTerm tableWidth)) := by
  let raw := compileExponentialAtValuation
    sequentRowsExplicitUniformZeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)
  have hvaluationContext :
      exponentialValuationContext sequentRowsExplicitUniformZeroValuation
          (shortBinaryNumeralTerm valueBound)
          (shortBinaryNumeralTerm tableWidth) =
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          sequentRowsExplicitUniformZeroValuation := by
    unfold exponentialValuationContext
    rw [exponentialAtValuationFormula_freeVariables]
  let atValuation := CertifiedPAContextProof.castContext
    hvaluationContext raw
  have hempty :
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          sequentRowsExplicitUniformZeroValuation = ∅ := by
    rw [exponentialAtValuationFormula_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hempty atValuation

noncomputable def
    compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (compactSequentFormulaStepRowsBoundedExponentialClosedFormula tableWidth
        valueBound) := by
  let raw :=
    compileCompactSequentFormulaStepRowsBoundedExponentialAtValuationExplicitUniformContext
      tableWidth valueBound hvalueBound
  exact CertifiedPAContextProof.cast (by rfl) raw

def compactSequentFormulaStepRowsBoundedExponentialExplicitUniformResource
    (tableWidth valueBound : Nat) : Nat :=
  exponentialValuationCompilerPayloadPolynomial
    (compileExponentialAtValuationPayloadResource
      sequentRowsExplicitUniformZeroValuation
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))

theorem
    compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext_payloadLength_le
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext
      tableWidth valueBound hvalueBound).payloadLength <=
      compactSequentFormulaStepRowsBoundedExponentialExplicitUniformResource
        tableWidth valueBound := by
  unfold
    compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold
    compileCompactSequentFormulaStepRowsBoundedExponentialAtValuationExplicitUniformContext
    compactSequentFormulaStepRowsBoundedExponentialExplicitUniformResource
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.castContext_payloadLength]
  exact compileExponentialAtValuation_payloadLength_le_fixedPolynomial
    sequentRowsExplicitUniformZeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

def compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat) : Nat :=
  let exponentialFormula :=
    compactSequentFormulaStepRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactSequentFormulaStepRowsBoundedUniversalBody tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount
      valueBound).ballLT (shortBinaryNumeralTerm rowCount)
  compactSequentFormulaStepRowsBoundedExponentialExplicitUniformResource
      tableWidth valueBound +
    compactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalResource
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

noncomputable def
    compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext
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
    compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactSequentFormulaStepRowsBoundedDirectClosedFormula_alignment
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound).symm
    raw

theorem
    compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext_payloadLength_le
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound : Nat)
    (hgraph : CompactSequentFormulaStepRowsBoundedGraph tokenTable width
      tokenCount suffixBoundary suffixCount valueBoundary valueCount rowCount
      tableWidth valueBound) :
    (compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount tableWidth valueBound hgraph).payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount tableWidth valueBound := by
  let exponentialProof :=
    compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedExponentialExplicitUniformResource
        tableWidth valueBound :=
    compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalResource
        tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
        valueCount rowCount valueBound :=
    compileCompactSequentFormulaStepRowsBoundedDirectExplicitUniformUniversalContext_payloadLength_le
      tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowCount valueBound hgraph.2
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold
    compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold
      compactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformResource
    dsimp only
    omega)

#print axioms
  compileCompactSequentFormulaStepRowsBoundedExponentialExplicitUniformContext_payloadLength_le
#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext
#print axioms
  compileCompactSequentFormulaStepRowsBoundedDirectClosedExplicitUniformContext_payloadLength_le

end FoundationCompactNumericListedDirectSequentFormulaStepRowsBoundedDirectGraphExplicitUniformResource
