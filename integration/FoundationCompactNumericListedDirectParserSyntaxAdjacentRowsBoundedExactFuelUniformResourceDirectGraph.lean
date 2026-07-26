import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourcePolynomial
import integration.FoundationCompactPAExponentialShortNumeralTransportMonotonicity

/-!
# Exact-fuel adjacent-row graph with a row-independent resource

The formula keeps its actual table width and value bound.  The exponential
leaf and every row branch are compiled at those actual values, while their
explicit payload ledgers are widened to one external uniform value bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectGraph

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPAExponentialShortNumeralTransportBounds
open FoundationCompactPAExponentialShortNumeralTransportMonotonicity
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectUniversal
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourcePolynomial
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

theorem
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial_mono
    {small large : Nat} (h : small <= large) :
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
        small <=
      compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
        large := by
  have hsource := exponentialPowerAtShortNumeralsPayloadPolynomial_mono h
  have hcontext :
      smallContextAssemblyEnvelope
          (exponentialPowerAtShortNumeralsPayloadPolynomial small) <=
        smallContextAssemblyEnvelope
          (exponentialPowerAtShortNumeralsPayloadPolynomial large) := by
    unfold smallContextAssemblyEnvelope smallSequentCodeEnvelope
    omega
  unfold
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
  dsimp only
  omega

def compactParserSyntaxAdjacentRowsBoundedExactFuelUniformFormulaResource
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
      uniformValueBound +
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformUniversalPolynomial
      tokenCount uniformValueBound numericBound bitBound + 8

def compactParserSyntaxAdjacentRowsBoundedExactFuelUniformPayloadPolynomial
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  let exponential :=
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
      uniformValueBound
  let universal :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformUniversalPolynomial
      tokenCount uniformValueBound numericBound bitBound
  exponential + universal +
    smallContextAssemblyEnvelope
      (compactParserSyntaxAdjacentRowsBoundedExactFuelUniformFormulaResource
        tokenCount uniformValueBound numericBound bitBound)

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      formulaValueBound uniformValueBound numericBound bitBound : Nat)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth formulaValueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueBound : formulaValueBound <= numericBound)
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
      (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        formulaValueBound) := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
      tableWidth formulaValueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound hformulaValue
      hgraph.2 hfuel hvalueBound hwidth hwidthBit htokenCount hstateCount
      htokenTableSize hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
        formulaValueBound).symm raw

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      formulaValueBound uniformValueBound numericBound bitBound : Nat)
    (htableWidth : tableWidth <= uniformValueBound)
    (hformulaValue : formulaValueBound <= uniformValueBound)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth formulaValueBound)
    (hinputCount : inputCount <= numericBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hvalueBound : formulaValueBound <= numericBound)
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
    (compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      formulaValueBound uniformValueBound numericBound bitBound hformulaValue
      hgraph hfuel hvalueBound hwidth hwidthBit htokenCount
      hstateCount htokenTableSize hstateBoundarySize hareaNumeric hareaBit
      hnumericSize hbitPositive).payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelUniformPayloadPolynomial
        tokenCount uniformValueBound numericBound bitBound := by
  let exponentialFormula :=
    compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula tableWidth
      formulaValueBound
  let universalFormula :=
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount formulaValueBound).ballLT
        (compactParserSyntaxExactFuelTerm inputCount)
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
      tableWidth formulaValueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound hformulaValue
      hgraph.2 hfuel hvalueBound hwidth hwidthBit htokenCount hstateCount
      htokenTableSize hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  let exponentialBound :=
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
      uniformValueBound
  let universalBound :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformUniversalPolynomial
      tokenCount uniformValueBound numericBound bitBound
  let formulaBound :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformFormulaResource
      tokenCount uniformValueBound numericBound bitBound
  have hexponentialActual : exponentialProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
        tableWidth :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext_payloadLength_le
      tableWidth formulaValueBound hgraph.1
  have hexponential : exponentialProof.payloadLength <= exponentialBound :=
    hexponentialActual.trans
      (compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial_mono
        htableWidth)
  have huniversalRaw : universalProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount inputCount
        formulaValueBound uniformValueBound numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound hformulaValue
      hgraph.2 hfuel hvalueBound hwidth hwidthBit htokenCount hstateCount
      htokenTableSize hstateBoundarySize hareaNumeric hareaBit hnumericSize
      hbitPositive
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hvalueBoundSize : Nat.size formulaValueBound <= bitBound :=
    (Nat.size_le_size hvalueBound).trans hnumericSize
  have huniversalFixed :
      compactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalResource
          tokenTable width tokenCount stateBoundary stateCount inputCount
          formulaValueBound uniformValueBound numericBound bitBound <=
        universalBound :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelUniformDirectUniversalResource_le_polynomial
      tokenTable width tokenCount stateBoundary stateCount inputCount
      formulaValueBound uniformValueBound numericBound bitBound hinputCount
      hfuel htokenTableSize hwidthSize htokenCountSize hstateBoundarySize
      hstateCountSize hvalueBoundSize
  have huniversal : universalProof.payloadLength <= universalBound :=
    huniversalRaw.trans huniversalFixed
  have hexponentialCode :
      (binaryFormulaCode exponentialFormula).length <= exponentialBound :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      exponentialProof).trans hexponential
  have huniversalCode :
      (binaryFormulaCode universalFormula).length <= universalBound :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      universalProof).trans huniversal
  have hconjunctionCode :
      (binaryFormulaCode (exponentialFormula ⋏ universalFormula)).length <=
        formulaBound := by
    have hrawCode := binaryFormulaCode_and_length_le exponentialFormula
      universalFormula
    dsimp only [formulaBound]
    unfold
      compactParserSyntaxAdjacentRowsBoundedExactFuelUniformFormulaResource
    omega
  have hassembly := conjunctionFullAssemblyCost_le_small ∅
    exponentialFormula universalFormula formulaBound (by simp) (by
      intro formula hmem
      simp at hmem) (by
      dsimp only [formulaBound]
      unfold
        compactParserSyntaxAdjacentRowsBoundedExactFuelUniformFormulaResource
      omega) (by
      dsimp only [formulaBound]
      unfold
        compactParserSyntaxAdjacentRowsBoundedExactFuelUniformFormulaResource
      omega) hconjunctionCode
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  have hchildren : exponentialProof.payloadLength +
      universalProof.payloadLength <= exponentialBound + universalBound :=
    Nat.add_le_add hexponential huniversal
  have hassembly' :
      CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
            tableWidth formulaValueBound)
          ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
            tokenCount stateBoundary stateCount formulaValueBound).ballLT
              (compactParserSyntaxExactFuelTerm inputCount)) <=
        smallContextAssemblyEnvelope formulaBound := by
    simpa only [exponentialFormula, universalFormula] using hassembly
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  calc
    raw.payloadLength <= exponentialProof.payloadLength +
        universalProof.payloadLength +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
              tableWidth formulaValueBound)
            ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
              width tokenCount stateBoundary stateCount formulaValueBound).ballLT
                (compactParserSyntaxExactFuelTerm inputCount)) := hraw
    _ <= exponentialBound + universalBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
            tableWidth formulaValueBound)
          ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
            tokenCount stateBoundary stateCount formulaValueBound).ballLT
              (compactParserSyntaxExactFuelTerm inputCount)) :=
      Nat.add_le_add_right hchildren _
    _ <= exponentialBound + universalBound +
        smallContextAssemblyEnvelope formulaBound :=
      Nat.add_le_add_left hassembly' _
    _ = compactParserSyntaxAdjacentRowsBoundedExactFuelUniformPayloadPolynomial
        tokenCount uniformValueBound numericBound bitBound := by
      rfl

#print axioms
  compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial_mono
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelUniformContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelUniformResourceDirectGraph
