import integration.FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph

/-! # Fixed direct compiler for the exact bounded parser graph -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectGraph
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
open FoundationCompactNumericListedDirectAdditiveCodecGraph

def compactParserSyntaxExactBoundedDirectNumericBound
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  tokenTable + width + tokenCount + stateBoundary + stateCount +
    compactParserSyntaxExactFuel inputCount +
    inputBoundary + inputCount + expectedBoundary + expectedCount +
    taskKind + taskBinderArity + taskRepeatCount + tableWidth + valueBound +
    (tokenCount + 1) * tokenCount + 1

def compactParserSyntaxExactBoundedDirectBitBound
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  numericBound + Nat.size numericBound + 1

structure ParserSyntaxExactBoundedClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

def compactParserSyntaxExactBoundedDirectPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let bitBound :=
    compactParserSyntaxExactBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  let countFormula :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let initialFinalFormula :=
    compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound
  let adjacentFormula :=
    compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula tokenTable
      width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound
  compactParserInitialFinalExactFuelCountResource inputCount +
    compactParserInitialFinalBoundedExactFuelDirectStructuralPayloadEnvelope
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound +
    compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
      tokenTable width tokenCount stateBoundary stateCount inputCount
      tableWidth valueBound numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ initialFinalFormula
      adjacentFormula +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
      (initialFinalFormula ⋏ adjacentFormula)

noncomputable def compactParserSyntaxExactBoundedClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound)
      (compactParserSyntaxExactBoundedDirectPayloadEnvelope tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound) := by
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let bitBound :=
    compactParserSyntaxExactBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  have htrace : CompactParserSyntaxTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
      (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactParserSyntaxExactFuel] using hgraph
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hstateBoundary : stateBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hstateCount : stateCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hfuel : compactParserSyntaxExactFuel inputCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have harea : (tokenCount + 1) * tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hnumericBit : numericBound <= bitBound := by
    change numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have htokenTableSize : Nat.size tokenTable <= bitBound :=
    (natSize_le_of_le htokenTable).trans hnumericBit
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound :=
    (natSize_le_of_le hstateBoundary).trans hnumericBit
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <=
      numericBound + Nat.size numericBound + 1
    omega
  have hbitPositive : 1 <= bitBound := by
    change 1 <= numericBound + Nat.size numericBound + 1
    omega
  let countBound :=
    parserInitialFinalExactFuelCountClosedDirectBound stateCount inputCount
      htrace.1
  let initialFinalBound :=
    compactParserInitialFinalBoundedExactFuelClosedDirectBoundOfBounded
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound htrace.2.1
  let adjacentProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound htrace.2.2 hfuel hvalueBound hwidth
      (hwidth.trans hnumericBit) htokenCount hstateCount htokenTableSize
      hstateBoundarySize harea (harea.trans hnumericBit) hnumericSize
      hbitPositive
  let innerProof := CertifiedPAContextProof.conjunction
    initialFinalBound.proof adjacentProof
  let outerProof := CertifiedPAContextProof.conjunction
    countBound.proof innerProof
  let traceProof := CertifiedPAContextProof.cast
    (compactParserSyntaxTraceBoundedExactFuelDirectClosedFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound).symm
    outerProof
  let proof := CertifiedPAContextProof.cast
    (compactParserSyntaxExactBoundedDirectClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound).symm
    traceProof
  refine { proof := proof, payloadLength_le := ?_ }
  have hadjacent :
      adjacentProof.payloadLength <=
        compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
          tokenTable width tokenCount stateBoundary stateCount inputCount
          tableWidth valueBound numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputCount tableWidth
      valueBound numericBound bitBound htrace.2.2 hfuel hvalueBound hwidth
      (hwidth.trans hnumericBit) htokenCount hstateCount htokenTableSize
      hstateBoundarySize harea (harea.trans hnumericBit) hnumericSize
      hbitPositive
  have hcount := countBound.payloadLength_le
  have hinitialFinal := initialFinalBound.payloadLength_le
  have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
    initialFinalBound.proof adjacentProof
  have hinnerBound :
      innerProof.payloadLength <=
        compactParserInitialFinalBoundedExactFuelDirectStructuralPayloadEnvelope
            tokenTable width tokenCount stateBoundary stateCount inputBoundary
            inputCount expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound +
          compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
            tokenTable width tokenCount stateBoundary stateCount inputCount
            tableWidth valueBound numericBound bitBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserInitialFinalBoundedExactFuelDirectClosedFormula
              tokenTable width tokenCount stateBoundary stateCount
              inputBoundary inputCount expectedBoundary expectedCount taskKind
              taskBinderArity taskRepeatCount valueBound)
            (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula
              tokenTable width tokenCount stateBoundary stateCount inputCount
              tableWidth valueBound) := by
    change
      (CertifiedPAContextProof.conjunction initialFinalBound.proof
        adjacentProof).payloadLength <= _
    exact hinner.trans (by omega)
  have houter := CertifiedPAContextProof.conjunction_payloadLength_le
    countBound.proof innerProof
  have houterBound :
      outerProof.payloadLength <=
        compactParserInitialFinalExactFuelCountResource inputCount +
          compactParserInitialFinalBoundedExactFuelDirectStructuralPayloadEnvelope
            tokenTable width tokenCount stateBoundary stateCount inputBoundary
            inputCount expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound +
          compactParserSyntaxAdjacentRowsBoundedExactFuelDirectClosedResource
            tokenTable width tokenCount stateBoundary stateCount inputCount
            tableWidth valueBound numericBound bitBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserInitialFinalBoundedExactFuelDirectClosedFormula
              tokenTable width tokenCount stateBoundary stateCount
              inputBoundary inputCount expectedBoundary expectedCount taskKind
              taskBinderArity taskRepeatCount valueBound)
            (compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula
              tokenTable width tokenCount stateBoundary stateCount inputCount
              tableWidth valueBound) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserInitialFinalExactFuelCountFormula stateCount
              inputCount)
            (compactParserInitialFinalBoundedExactFuelDirectClosedFormula
                tokenTable width tokenCount stateBoundary stateCount
                inputBoundary inputCount expectedBoundary expectedCount
                taskKind taskBinderArity taskRepeatCount valueBound ⋏
              compactParserSyntaxAdjacentRowsBoundedExactFuelClosedFormula
                tokenTable width tokenCount stateBoundary stateCount inputCount
                tableWidth valueBound) := by
    change
      (CertifiedPAContextProof.conjunction countBound.proof
        innerProof).payloadLength <= _
    exact houter.trans (by omega)
  change (CertifiedPAContextProof.cast _
    (CertifiedPAContextProof.cast _ outerProof)).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]
  unfold compactParserSyntaxExactBoundedDirectPayloadEnvelope
  dsimp only [numericBound, bitBound, countBound, initialFinalBound,
    adjacentProof, innerProof, outerProof, traceProof, proof]
  exact houterBound

#print axioms compactParserSyntaxExactBoundedClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
