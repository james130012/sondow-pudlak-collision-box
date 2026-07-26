import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectGraph
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
import integration.FoundationCompactPAExponentialShortNumeralTransportBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-!
# Fully fixed exact-fuel adjacent-row graph

The exponential child is compiled directly at short binary numerals.  Its
payload, empty-context weakening, the exact-fuel bounded universal, and the
final conjunction assembly are all bounded by explicit resources.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExponentialShortNumeralCompiler
open FoundationCompactPAExponentialShortNumeralTransportBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversal
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

private theorem certifiedPAProof_conclusionCodeLength_le_payloadLength
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    (binaryFormulaCode formula).length <= proof.payloadLength := by
  have hformula : formula ∈ ({formula} :
      Finset LO.FirstOrder.ArithmeticProposition) := by simp
  have hsequent :=
    binaryFormulaCode_length_le_binarySequentCode_length_of_mem
      {formula} formula hformula
  have hproof := binarySequentCode_length_le_binaryProofLength proof.derivation
  have hpayload : binaryProofLength proof.derivation <= proof.payloadLength := by
    rw [CertifiedPAProof.payloadLength_eq]
    omega
  exact hsequent.trans (hproof.trans hpayload)

def compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
    (tableWidth : Nat) : Nat :=
  let source := exponentialPowerAtShortNumeralsPayloadPolynomial tableWidth
  source + smallContextAssemblyEnvelope source

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    CertifiedPAContextProof ∅
      (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
        tableWidth valueBound) := by
  let raw := proveExponentialPowerAtShortNumerals tableWidth
  have hformula :
      exponentialShortNumeralFormula tableWidth =
        compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
          tableWidth valueBound := by
    unfold exponentialShortNumeralFormula
      compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
    rw [hvalueBound]
  let source := CertifiedPAProof.cast hformula raw
  exact CertifiedPAContextProof.weakenCertified ∅ source

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext_payloadLength_le
    (tableWidth valueBound : Nat)
    (hvalueBound : valueBound = 2 ^ tableWidth) :
    (compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
      tableWidth valueBound hvalueBound).payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
        tableWidth := by
  let raw := proveExponentialPowerAtShortNumerals tableWidth
  have hformula :
      exponentialShortNumeralFormula tableWidth =
        compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
          tableWidth valueBound := by
    unfold exponentialShortNumeralFormula
      compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
    rw [hvalueBound]
  let source := CertifiedPAProof.cast hformula raw
  let sourceBound :=
    exponentialPowerAtShortNumeralsPayloadPolynomial tableWidth
  have hsource : source.payloadLength <= sourceBound := by
    calc
      source.payloadLength = raw.payloadLength := by
        dsimp only [source]
        exact CertifiedPAProof.cast_payloadLength hformula raw
      _ <= sourceBound :=
        proveExponentialPowerAtShortNumerals_payloadLength_le_polynomial
          tableWidth
  have hformulaCode :
      (binaryFormulaCode
        (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
          tableWidth valueBound)).length <= sourceBound :=
    (certifiedPAProof_conclusionCodeLength_le_payloadLength source).trans hsource
  have hcontext : FormulaCodeBound
      (insert
      (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
          tableWidth valueBound) ∅) sourceBound := by
    intro formula hmem
    simp at hmem
    subst formula
    exact hformulaCode
  have hweak := weakeningFullAssemblyCost_le_small
    (insert
      (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
        tableWidth valueBound) ∅) sourceBound (by simp) hcontext
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
  change (CertifiedPAContextProof.weakenCertified ∅ source).payloadLength <= _
  calc
    (CertifiedPAContextProof.weakenCertified ∅ source).payloadLength <=
        source.payloadLength + weakeningFullAssemblyCost
          (insert
            (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
              tableWidth valueBound) ∅) :=
      CertifiedPAContextProof.weakenCertified_payloadLength_le ∅ source
    _ <= sourceBound + smallContextAssemblyEnvelope sourceBound :=
      Nat.add_le_add hsource hweak
    _ = compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
        tableWidth := by
      rfl

def compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedFormulaResource
    (tokenCount inputCount tableWidth valueBound numericBound bitBound : Nat) :
    Nat :=
  compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
      tableWidth +
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
      tokenCount valueBound numericBound bitBound + 8

def compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedPayloadPolynomial
    (tokenCount inputCount tableWidth valueBound numericBound bitBound : Nat) :
    Nat :=
  let exponential :=
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
      tableWidth
  let universal :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
      tokenCount valueBound numericBound bitBound
  exponential + universal +
    smallContextAssemblyEnvelope
      (compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedFormulaResource
        tokenCount inputCount tableWidth valueBound numericBound bitBound)

noncomputable def
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth valueBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
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
      (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound) := by
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  exact CertifiedPAContextProof.cast
    (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
        valueBound).symm raw

theorem
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentRowsBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
        (compactParserSyntaxExactFuel inputCount) tableWidth valueBound)
    (hinputCount : inputCount <= numericBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
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
    (compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound hgraph hfuel hvalueNumeric hwidth
      hwidthBit htokenCount hstateCount htokenTableSize hstateBoundarySize
      hareaNumeric hareaBit hnumericSize hbitPositive).payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedPayloadPolynomial
        tokenCount inputCount tableWidth valueBound numericBound bitBound := by
  let exponentialFormula :=
    compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula tableWidth
      valueBound
  let universalFormula :=
    (compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
      tokenCount stateBoundary stateCount valueBound).ballLT
        (compactParserSyntaxExactFuelTerm inputCount)
  let exponentialProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
      tableWidth valueBound hgraph.1
  let universalProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  let raw := CertifiedPAContextProof.conjunction exponentialProof universalProof
  let exponentialBound :=
    compactParserSyntaxAdjacentRowsBoundedExponentialFixedPayloadPolynomial
      tableWidth
  let universalBound :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedUniversalPolynomial
      tokenCount valueBound numericBound bitBound
  let formulaBound :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedFormulaResource
      tokenCount inputCount tableWidth valueBound numericBound bitBound
  have hexponential : exponentialProof.payloadLength <= exponentialBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext_payloadLength_le
      tableWidth valueBound hgraph.1
  have huniversalRaw : universalProof.payloadLength <=
      compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource
        tokenTable width tokenCount stateBoundary stateCount inputCount
          valueBound numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hgraph.2 hfuel hvalueNumeric hwidth hwidthBit
      htokenCount hstateCount htokenTableSize hstateBoundarySize hareaNumeric
      hareaBit hnumericSize hbitPositive
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hvalueBoundSize : Nat.size valueBound <= bitBound :=
    (Nat.size_le_size hvalueNumeric).trans hnumericSize
  have huniversalFixed :
      compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource
          tokenTable width tokenCount stateBoundary stateCount inputCount
            valueBound numericBound bitBound <= universalBound :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelTermCodeFixedDirectUniversalResource_le_polynomial
      tokenTable width tokenCount stateBoundary stateCount inputCount valueBound
      numericBound bitBound hinputCount hfuel htokenTableSize hwidthSize
      htokenCountSize hstateBoundarySize hstateCountSize hvalueBoundSize
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
      compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedFormulaResource
    omega
  have hassembly := conjunctionFullAssemblyCost_le_small ∅
    exponentialFormula universalFormula formulaBound (by simp) (by
      intro formula hmem
      simp at hmem) (by
      dsimp only [formulaBound]
      unfold
        compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedFormulaResource
      omega) (by
      dsimp only [formulaBound]
      unfold
        compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedFormulaResource
      omega) hconjunctionCode
  have hraw := CertifiedPAContextProof.conjunction_payloadLength_le
    exponentialProof universalProof
  have hchildren : exponentialProof.payloadLength +
      universalProof.payloadLength <= exponentialBound + universalBound :=
    Nat.add_le_add hexponential huniversal
  have hassembly' :
      CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
            tableWidth valueBound)
          ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
            tokenCount stateBoundary stateCount valueBound).ballLT
              (compactParserSyntaxExactFuelTerm inputCount)) <=
        smallContextAssemblyEnvelope formulaBound := by
    simpa only [exponentialFormula, universalFormula] using hassembly
  unfold
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext
  rw [CertifiedPAContextProof.cast_payloadLength]
  change raw.payloadLength <= _
  calc
    raw.payloadLength <= exponentialProof.payloadLength +
        universalProof.payloadLength +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
              tableWidth valueBound)
            ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable
              width tokenCount stateBoundary stateCount valueBound).ballLT
                (compactParserSyntaxExactFuelTerm inputCount)) := hraw
    _ <= exponentialBound + universalBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactParserSyntaxAdjacentRowsBoundedExponentialClosedFormula
            tableWidth valueBound)
          ((compactParserSyntaxAdjacentRowsBoundedUniversalBody tokenTable width
            tokenCount stateBoundary stateCount valueBound).ballLT
              (compactParserSyntaxExactFuelTerm inputCount)) :=
      Nat.add_le_add_right hchildren _
    _ <= exponentialBound + universalBound +
        smallContextAssemblyEnvelope formulaBound :=
      Nat.add_le_add_left hassembly' _
    _ = compactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedPayloadPolynomial
        tokenCount inputCount tableWidth valueBound numericBound bitBound := by
      rfl

#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExponentialFixedContext_payloadLength_le
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext
#print axioms
  compileCompactParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedContext_payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelFullyFixedDirectGraph
