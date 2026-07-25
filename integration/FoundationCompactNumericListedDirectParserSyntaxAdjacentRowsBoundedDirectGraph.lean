import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectUniversal
import integration.FoundationCompactPAExponentialValuationContextCompilerBounds

/-!
# Direct proof of the complete bounded adjacent-row graph

The closed exponential value-bound proof and the completed all-row bounded
universal are joined directly, then cast to the original eight-argument graph
formula.  The resource records both children and the full conjunction cost.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAExponentialValuationContextCompiler
open FoundationCompactPAExponentialValuationContextCompilerBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectBranches
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectUniversal

private noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialAtValuationDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (exponentialAtValuationFormula
        (shortBinaryNumeralTerm valueBound)
        (shortBinaryNumeralTerm tableWidth)) := by
  let raw := compileExponentialAtValuation zeroValuation
    (shortBinaryNumeralTerm valueBound)
    (shortBinaryNumeralTerm tableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)
  have hvaluationContext :
      exponentialValuationContext zeroValuation
          (shortBinaryNumeralTerm valueBound)
          (shortBinaryNumeralTerm tableWidth) =
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          zeroValuation := by
    unfold exponentialValuationContext
    rw [exponentialAtValuationFormula_freeVariables]
  let atValuation := CertifiedPAContextProof.castContext
    hvaluationContext raw
  have hempty :
      valuationContext
          (exponentialAtValuationFormula
            (shortBinaryNumeralTerm valueBound)
            (shortBinaryNumeralTerm tableWidth)).freeVariables
          zeroValuation = ∅ := by
    rw [exponentialAtValuationFormula_freeVariables,
      shortBinaryNumeralTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp [valuationContext]
  exact CertifiedPAContextProof.castContext hempty atValuation

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
        tableWidth valueBound) := by
  let raw :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialAtValuationDirectContext
      tableWidth valueBound hvalueBound
  exact CertifiedPAContextProof.cast (by rfl) raw

def compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource
    (tableWidth valueBound : Nat) : Nat :=
  exponentialValuationCompilerPayloadPolynomial
    (compileExponentialAtValuationPayloadResource zeroValuation
      (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth))

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext_payloadLength_le
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hvalueBound).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource
      tableWidth valueBound := by
  unfold compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialAtValuationDirectContext
  unfold compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.castContext_payloadLength]
  exact compileExponentialAtValuation_payloadLength_le_fixedPolynomial
    zeroValuation (shortBinaryNumeralTerm valueBound)
      (shortBinaryNumeralTerm tableWidth) (by
        simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)

def compactParserSyntaxAdjacentRowsBoundedDirectClosedResource
    (tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound numericBound bitBound : Nat) : Nat :=
  let exponentialFormula :=
    compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).ballLT
        (shortBinaryNumeralTerm rowCount)
  compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource tableWidth
      valueBound +
    compactParserSyntaxAdjacentRowsBoundedDirectUniversalPolynomialResource
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
        numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ exponentialFormula
      universalFormula

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext
    (tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount rowCount tableWidth valueBound)
    (hrowCount : rowCount <= numericBound)
    (hvalueNumeric : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CertifiedPAContextProof ∅
      (compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount rowCount tableWidth valueBound) := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound hgraph.2 hrowCount hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactParserSyntaxAdjacentRowsBoundedClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount rowCount tableWidth
        valueBound).symm
    raw

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount rowCount tableWidth valueBound)
    (hrowCount : rowCount <= numericBound)
    (hvalueNumeric : valueBound <= numericBound)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    (compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount rowCount tableWidth
      valueBound numericBound bitBound hgraph hrowCount hvalueNumeric hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hnumericSize hbitPositive).payloadLength <=
    compactParserSyntaxAdjacentRowsBoundedDirectClosedResource tokenTable width
      tokenCount stateBoundary stateCount rowCount tableWidth valueBound
        numericBound bitBound := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound hgraph.2 hrowCount hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  have hexponential : exponentialProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExponentialDirectResource
        tableWidth valueBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversal : universalProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedDirectUniversalPolynomialResource
        tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
          numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount rowCount valueBound
      numericBound bitBound hgraph.2 hrowCount hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  unfold compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  exact hraw.trans (by
    unfold compactParserSyntaxAdjacentRowsBoundedDirectClosedResource
    dsimp only
    omega)

#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExponentialDirectContext_payloadLength_le
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph
