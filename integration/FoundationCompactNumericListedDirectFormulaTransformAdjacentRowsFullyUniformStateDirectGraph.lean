import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectBounds
import integration.FoundationCompactPAExponentialValuationContextCompilerBounds

/-!
# Direct proof of the complete bounded formula-transform adjacent-row graph

The exponential value-bound leaf is compiled by the checked PA exponential
compiler.  Its proof is joined to the fully uniform direct proof of all genuine
adjacent rows.  The resulting public resource contains no graph proof or local
row data.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectGraph

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAExponentialValuationContextCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectBounds

private abbrev formulaTransformAdjacentRowsZeroValuation : Nat -> Nat :=
  fun _ => 0

private noncomputable def
    compileFormulaTransformAdjacentRowsExponentialAtValuationContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (exponentialAtValuationFormula
        (shortBinaryNumeralTerm valueBound)
        (shortBinaryNumeralTerm tableWidth)) := by
  let raw := compileExponentialAtValuation
    formulaTransformAdjacentRowsZeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)
  have hvaluationContext :
      exponentialValuationContext formulaTransformAdjacentRowsZeroValuation
          (shortBinaryNumeralTerm valueBound)
          (shortBinaryNumeralTerm tableWidth) =
        valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          formulaTransformAdjacentRowsZeroValuation := by
    unfold exponentialValuationContext
    rw [exponentialAtValuationFormula_freeVariables]
  let atValuation := CertifiedPAContextProof.castContext hvaluationContext raw
  have hempty :
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          formulaTransformAdjacentRowsZeroValuation = ∅ := by
    rw [exponentialAtValuationFormula_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hempty atValuation

noncomputable def
    compileFormulaTransformAdjacentRowsExponentialDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
        tableWidth valueBound) := by
  let raw :=
    compileFormulaTransformAdjacentRowsExponentialAtValuationContext
      tableWidth valueBound hvalueBound
  exact CertifiedPAContextProof.cast (by rfl) raw

def compactFormulaTransformAdjacentRowsExponentialDirectPublicResource
    (tableWidth valueBound : Nat) : Nat :=
  exponentialValuationCompilerPayloadPolynomial
    (compileExponentialAtValuationPayloadResource
      formulaTransformAdjacentRowsZeroValuation
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))

theorem
    compileFormulaTransformAdjacentRowsExponentialDirectContext_payloadLength_le
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (compileFormulaTransformAdjacentRowsExponentialDirectContext tableWidth
      valueBound hvalueBound).payloadLength <=
      compactFormulaTransformAdjacentRowsExponentialDirectPublicResource
        tableWidth valueBound := by
  unfold compileFormulaTransformAdjacentRowsExponentialDirectContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold
    compileFormulaTransformAdjacentRowsExponentialAtValuationContext
    compactFormulaTransformAdjacentRowsExponentialDirectPublicResource
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.castContext_payloadLength]
  exact compileExponentialAtValuation_payloadLength_le_fixedPolynomial
    formulaTransformAdjacentRowsZeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

noncomputable def
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound numericBound
      bitBound : Nat) : Nat :=
  let exponentialFormula :=
    compactFormulaTransformAdjacentRowsBoundedExponentialClosedFormula
      tableWidth valueBound
  let universalFormula :=
    (compactFormulaTransformAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount mode witnessStart witnessFinish
      witnessCount valueBound).ballLT (shortBinaryNumeralTerm rowCount)
  compactFormulaTransformAdjacentRowsExponentialDirectPublicResource tableWidth
      valueBound +
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicUniversalResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

noncomputable def
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound numericBound
      bitBound : Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount rowCount mode witnessStart
      witnessFinish witnessCount tableWidth valueBound) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformAdjacentRowsBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount rowCount mode witnessStart
        witnessFinish witnessCount tableWidth valueBound) := by
  let exponentialProof :=
    compileFormulaTransformAdjacentRowsExponentialDirectContext tableWidth
      valueBound hgraph.1
  let universalProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactFormulaTransformAdjacentRowsBoundedClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound).symm raw

theorem
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound numericBound
      bitBound : Nat)
    (hrowCount : rowCount <= numericBound)
    (hvalueBound : valueBound <= numericBound)
    (hwidthValue : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hgraph : CompactFormulaTransformAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount rowCount mode witnessStart
      witnessFinish witnessCount tableWidth valueBound) :
    (compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound numericBound
      bitBound hrowCount hvalueBound hwidthValue htokenCount hstateCount
      hareaNumeric hareaBit htokenTableSize hstateBoundarySize hnumericSize
      hnumericBit hbitPositive hgraph).payloadLength <=
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount tableWidth valueBound numericBound
      bitBound := by
  let exponentialProof :=
    compileFormulaTransformAdjacentRowsExponentialDirectContext tableWidth
      valueBound hgraph.1
  let universalProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hgraph.2
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactFormulaTransformAdjacentRowsExponentialDirectPublicResource
        tableWidth valueBound :=
    compileFormulaTransformAdjacentRowsExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectPublicUniversalResource
        tokenTable width tokenCount stateBoundary stateCount rowCount mode
        witnessStart witnessFinish witnessCount valueBound numericBound bitBound :=
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount rowCount mode
      witnessStart witnessFinish witnessCount valueBound numericBound bitBound
      hrowCount hvalueBound hwidthValue htokenCount hstateCount hareaNumeric
      hareaBit htokenTableSize hstateBoundarySize hnumericSize hnumericBit
      hbitPositive hgraph.2
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
    dsimp only
    omega)

#print axioms
  compileFormulaTransformAdjacentRowsExponentialDirectContext_payloadLength_le
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext
#print axioms
  compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectGraph
