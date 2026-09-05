import integration.FoundationCompactNumericListedDirectFormulaTransformTraceBoundedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectStructuralCompiler
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectGraph
import integration.FoundationCompactNumericListedDirectSequentFormulaStepSuccessorCountFixedBound

/-!
# Fully direct compiler for a bounded formula-transform trace

The state-count equality, bounded initial/final endpoints, and all bounded
adjacent rows are compiled independently and joined in the empty PA context.
The public resource is a function only of the nineteen trace coordinates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectFormulaTransformTraceBoundedFullyDirectCompiler

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepSuccessorCountFixedBound
open FoundationCompactNumericListedDirectFormulaTransformTraceFormula
open FoundationCompactNumericListedDirectFormulaTransformTraceBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectCompilation
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalBoundedDirectStructuralCompiler
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRowsFullyUniformStateDirectGraph

def compactFormulaTransformTraceBoundedFullyDirectNumericBound
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound : Nat) : Nat :=
  tokenTable + width + tokenCount + stateBoundary + stateCount + fuel + mode +
    witnessStart + witnessFinish + witnessCount + inputBoundary + inputCount +
    expectedOutputBoundary + expectedOutputCount + expectedSuffixBoundary +
    expectedSuffixCount + binderArity + tableWidth + valueBound +
    (tokenCount + 1) * tokenCount + 1

def compactFormulaTransformTraceBoundedFullyDirectBitBound
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound : Nat) : Nat :=
  let numericBound := compactFormulaTransformTraceBoundedFullyDirectNumericBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  numericBound + Nat.size numericBound + 1

noncomputable def
    compactFormulaTransformTraceBoundedFullyDirectPublicResource
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound : Nat) : Nat :=
  let numericBound := compactFormulaTransformTraceBoundedFullyDirectNumericBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  let bitBound := compactFormulaTransformTraceBoundedFullyDirectBitBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1”
  let initialFinalFormula :=
    compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound
  let adjacentFormula :=
    compactFormulaTransformAdjacentRowsBoundedClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel mode witnessStart witnessFinish
      witnessCount tableWidth valueBound
  compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial bitBound +
    compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound +
    compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
      tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
      witnessFinish witnessCount tableWidth valueBound numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ initialFinalFormula
      adjacentFormula +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
      (initialFinalFormula ⋏ adjacentFormula)

noncomputable def compileCompactFormulaTransformTraceBoundedFullyDirect
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount fuel mode witnessStart witnessFinish
      witnessCount inputBoundary inputCount expectedOutputBoundary
      expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound) :
    CertifiedPAContextProof ∅
      (compactFormulaTransformTraceBoundedGraphClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel mode witnessStart witnessFinish
        witnessCount inputBoundary inputCount expectedOutputBoundary
        expectedOutputCount expectedSuffixBoundary expectedSuffixCount
        binderArity tableWidth valueBound) := by
  let numericBound := compactFormulaTransformTraceBoundedFullyDirectNumericBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  let bitBound := compactFormulaTransformTraceBoundedFullyDirectBitBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  have hfuel : fuel <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hstateCount : stateCount <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hstateBoundary : stateBoundary <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hnumericBit : numericBound <= bitBound := by
    change numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hbitPositive : 1 <= bitBound := by
    change 1 <= numericBound + Nat.size numericBound + 1
    omega
  have hareaBit : (tokenCount + 1) * tokenCount <= bitBound :=
    hareaNumeric.trans hnumericBit
  have htokenTableSize : Nat.size tokenTable <= bitBound :=
    (Nat.size_le_size htokenTable).trans hnumericSize
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound :=
    (Nat.size_le_size hstateBoundary).trans hnumericSize
  let countProof :=
    (compactSequentFormulaStepSuccessorCountPublicBound stateCount fuel
      hgraph.1).proof
  let initialFinalBound :=
    compactFormulaTransformInitialFinalBoundedClosedDirectBoundOfBounded
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound hgraph.2.1
  let initialFinalProof := initialFinalBound.proof
  let adjacentProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
      witnessFinish witnessCount tableWidth valueBound numericBound bitBound
      hfuel hvalueBound hwidth htokenCount hstateCount hareaNumeric hareaBit
      htokenTableSize hstateBoundarySize hnumericSize hnumericBit hbitPositive
      hgraph.2.2
  let pairProof := CertifiedPAContextProof.conjunction initialFinalProof
    adjacentProof
  let outerProof := CertifiedPAContextProof.conjunction countProof pairProof
  exact CertifiedPAContextProof.cast
    (compactFormulaTransformTraceBoundedGraphClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount fuel mode witnessStart
      witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
      expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound).symm outerProof

theorem compileCompactFormulaTransformTraceBoundedFullyDirect_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount fuel mode
      witnessStart witnessFinish witnessCount inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity tableWidth valueBound : Nat)
    (hgraph : CompactFormulaTransformTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount fuel mode witnessStart witnessFinish
      witnessCount inputBoundary inputCount expectedOutputBoundary
      expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound) :
    (compileCompactFormulaTransformTraceBoundedFullyDirect tokenTable width
      tokenCount stateBoundary stateCount fuel mode witnessStart witnessFinish
      witnessCount inputBoundary inputCount expectedOutputBoundary
      expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound hgraph).payloadLength <=
    compactFormulaTransformTraceBoundedFullyDirectPublicResource tokenTable
      width tokenCount stateBoundary stateCount fuel mode witnessStart
      witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
      expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
      tableWidth valueBound := by
  let numericBound := compactFormulaTransformTraceBoundedFullyDirectNumericBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  let bitBound := compactFormulaTransformTraceBoundedFullyDirectBitBound
    tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
    witnessFinish witnessCount inputBoundary inputCount expectedOutputBoundary
    expectedOutputCount expectedSuffixBoundary expectedSuffixCount binderArity
    tableWidth valueBound
  have hfuel : fuel <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hstateCount : stateCount <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hstateBoundary : stateBoundary <= numericBound := by
    unfold numericBound
      compactFormulaTransformTraceBoundedFullyDirectNumericBound
    omega
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hnumericBit : numericBound <= bitBound := by
    change numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have hbitPositive : 1 <= bitBound := by
    change 1 <= numericBound + Nat.size numericBound + 1
    omega
  have hareaBit : (tokenCount + 1) * tokenCount <= bitBound :=
    hareaNumeric.trans hnumericBit
  have htokenTableSize : Nat.size tokenTable <= bitBound :=
    (Nat.size_le_size htokenTable).trans hnumericSize
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound :=
    (Nat.size_le_size hstateBoundary).trans hnumericSize
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hfuelSize : Nat.size fuel <= bitBound :=
    (Nat.size_le_size hfuel).trans hnumericSize
  let countBound :=
    compactSequentFormulaStepSuccessorCountPublicBound stateCount fuel hgraph.1
  let countProof := countBound.proof
  let initialFinalBound :=
    compactFormulaTransformInitialFinalBoundedClosedDirectBoundOfBounded
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity valueBound hgraph.2.1
  let initialFinalProof := initialFinalBound.proof
  let adjacentProof :=
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
      witnessFinish witnessCount tableWidth valueBound numericBound bitBound
      hfuel hvalueBound hwidth htokenCount hstateCount hareaNumeric hareaBit
      htokenTableSize hstateBoundarySize hnumericSize hnumericBit hbitPositive
      hgraph.2.2
  let pairProof := CertifiedPAContextProof.conjunction initialFinalProof
    adjacentProof
  let outerProof := CertifiedPAContextProof.conjunction countProof pairProof
  have hcount : countProof.payloadLength <=
      compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial bitBound :=
    countBound.payloadLength_le.trans
      (compactSequentFormulaStepSuccessorCountPublicBound_resource_le_fixed
        stateCount fuel bitBound hstateCountSize hfuelSize hgraph.1)
  have hinitialFinal : initialFinalProof.payloadLength <=
      compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
        inputCount expectedOutputBoundary expectedOutputCount
        expectedSuffixBoundary expectedSuffixCount binderArity valueBound :=
    initialFinalBound.payloadLength_le
  have hadjacent : adjacentProof.payloadLength <=
      compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
        tokenTable width tokenCount stateBoundary stateCount fuel mode
        witnessStart witnessFinish witnessCount tableWidth valueBound numericBound
        bitBound :=
    compileCompactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount fuel mode witnessStart
      witnessFinish witnessCount tableWidth valueBound numericBound bitBound
      hfuel hvalueBound hwidth htokenCount hstateCount hareaNumeric hareaBit
      htokenTableSize hstateBoundarySize hnumericSize hnumericBit hbitPositive
      hgraph.2.2
  have hpair := CertifiedPAContextProof.conjunction_payloadLength_le
    initialFinalProof adjacentProof
  have houter := CertifiedPAContextProof.conjunction_payloadLength_le countProof
    pairProof
  have hpairBound : pairProof.payloadLength <=
      compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
          tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound +
        compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount tableWidth valueBound
          numericBound bitBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable
            width tokenCount stateBoundary stateCount fuel inputBoundary
            inputCount expectedOutputBoundary expectedOutputCount
            expectedSuffixBoundary expectedSuffixCount binderArity valueBound)
          (compactFormulaTransformAdjacentRowsBoundedClosedFormula tokenTable
            width tokenCount stateBoundary stateCount fuel mode witnessStart
            witnessFinish witnessCount tableWidth valueBound) := by
    dsimp only [pairProof]
    exact hpair.trans (by omega)
  have houterBound : outerProof.payloadLength <=
      compactSequentFormulaStepSuccessorCountFixedPayloadPolynomial bitBound +
        compactFormulaTransformInitialFinalBoundedDirectStructuralPayloadEnvelope
          tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
          inputCount expectedOutputBoundary expectedOutputCount
          expectedSuffixBoundary expectedSuffixCount binderArity valueBound +
        compactFormulaTransformAdjacentRowsBoundedFullyUniformStateDirectClosedPublicResource
          tokenTable width tokenCount stateBoundary stateCount fuel mode
          witnessStart witnessFinish witnessCount tableWidth valueBound
          numericBound bitBound +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable
            width tokenCount stateBoundary stateCount fuel inputBoundary
            inputCount expectedOutputBoundary expectedOutputCount
            expectedSuffixBoundary expectedSuffixCount binderArity valueBound)
          (compactFormulaTransformAdjacentRowsBoundedClosedFormula tokenTable
            width tokenCount stateBoundary stateCount fuel mode witnessStart
            witnessFinish witnessCount tableWidth valueBound) +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
          (“!!(shortBinaryNumeralTerm stateCount) =
            !!(shortBinaryNumeralTerm fuel) + 1” : ValuationFormula)
          (compactFormulaTransformInitialFinalBoundedClosedFormula tokenTable
              width tokenCount stateBoundary stateCount fuel inputBoundary
              inputCount expectedOutputBoundary expectedOutputCount
              expectedSuffixBoundary expectedSuffixCount binderArity valueBound ⋏
            compactFormulaTransformAdjacentRowsBoundedClosedFormula tokenTable
              width tokenCount stateBoundary stateCount fuel mode witnessStart
              witnessFinish witnessCount tableWidth valueBound) := by
    dsimp only [outerProof]
    exact houter.trans (by omega)
  unfold compileCompactFormulaTransformTraceBoundedFullyDirect
  rw [CertifiedPAContextProof.cast_payloadLength]
  change outerProof.payloadLength <= _
  exact houterBound.trans (by
    unfold compactFormulaTransformTraceBoundedFullyDirectPublicResource
    dsimp only [numericBound, bitBound]
    omega)

#print axioms compileCompactFormulaTransformTraceBoundedFullyDirect
#print axioms
  compileCompactFormulaTransformTraceBoundedFullyDirect_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformTraceBoundedFullyDirectCompiler
