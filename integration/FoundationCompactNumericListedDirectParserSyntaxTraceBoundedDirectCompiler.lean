import integration.FoundationCompactNumericListedDirectParserSyntaxTraceFormula
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectStructuralCompiler
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph

/-! # Fixed direct compiler for a complete bounded parser trace -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxTraceBoundedDirectCompiler

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectOriginalSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedDirectGraph
open FoundationCompactNumericListedDirectAdditiveCodecGraph

def compactParserSyntaxTraceBoundedDirectClosedFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxTraceBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm stateBoundary,
      shortBinaryNumeralTerm stateCount,
      shortBinaryNumeralTerm fuel,
      shortBinaryNumeralTerm inputBoundary,
      shortBinaryNumeralTerm inputCount,
      shortBinaryNumeralTerm expectedBoundary,
      shortBinaryNumeralTerm expectedCount,
      shortBinaryNumeralTerm taskKind,
      shortBinaryNumeralTerm taskBinderArity,
      shortBinaryNumeralTerm taskRepeatCount,
      shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm valueBound]

def compactParserSyntaxTraceBoundedDirectExplicitFormula
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1” ⋏
    (compactParserInitialFinalBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound ⋏
      compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel tableWidth valueBound)

private theorem arithmeticRewritingApp_congr
    {sourceVariables targetVariables : Type*}
    {sourceArity targetArity : Nat}
    {left right : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity}
    (h : left = right) :
    (Rewriting.app left :
      ArithmeticSemiformula sourceVariables sourceArity →ˡᶜ
        ArithmeticSemiformula targetVariables targetArity) =
      Rewriting.app right := by
  cases h
  rfl

theorem compactParserSyntaxTraceBoundedDirectClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat) :
    compactParserSyntaxTraceBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound =
      compactParserSyntaxTraceBoundedDirectExplicitFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound := by
  unfold compactParserSyntaxTraceBoundedDirectClosedFormula
  unfold compactParserSyntaxTraceBoundedDirectExplicitFormula
  rw [compactParserInitialFinalBoundedDirectClosedFormula_eq_original]
  unfold compactParserSyntaxTraceBoundedGraphDef
  unfold compactParserSyntaxAdjacentRowsBoundedClosedFormula
  simp [← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    apply arithmeticRewritingApp_congr
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
      all_goals rfl
    · intro coordinate
      exact Empty.elim coordinate

def compactParserSyntaxTraceBoundedDirectNumericBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  tokenTable + width + tokenCount + stateBoundary + stateCount + fuel +
    inputBoundary + inputCount + expectedBoundary + expectedCount +
    taskKind + taskBinderArity + taskRepeatCount + tableWidth + valueBound +
    (tokenCount + 1) * tokenCount + 1

def compactParserSyntaxTraceBoundedDirectBitBound
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactParserSyntaxTraceBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  numericBound + Nat.size numericBound + 1

structure ParserSyntaxTraceBoundedClosedDirectBound
    (formula : ValuationFormula) (resource : Nat) where
  proof : CertifiedPAContextProof ∅ formula
  payloadLength_le : proof.payloadLength <= resource

def compactParserSyntaxTraceBoundedDirectPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactParserSyntaxTraceBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let bitBound :=
    compactParserSyntaxTraceBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm stateCount) =
      !!(shortBinaryNumeralTerm fuel) + 1”
  let initialFinalFormula :=
    compactParserInitialFinalBoundedDirectClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound
  let adjacentFormula :=
    compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel tableWidth valueBound
  parserInitialFinalStateCountPayloadPolynomial stateCount fuel numericBound +
    compactParserInitialFinalBoundedDirectStructuralPayloadEnvelope tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound +
    compactParserSyntaxAdjacentRowsBoundedDirectClosedResource tokenTable
      width tokenCount stateBoundary stateCount fuel tableWidth valueBound
      numericBound bitBound +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ initialFinalFormula
      adjacentFormula +
    CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ countFormula
      (initialFinalFormula ⋏ adjacentFormula)

noncomputable def compactParserSyntaxTraceBoundedClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount tableWidth valueBound : Nat)
    (hgraph : CompactParserSyntaxTraceBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound) :
    ParserSyntaxTraceBoundedClosedDirectBound
      (compactParserSyntaxTraceBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound)
      (compactParserSyntaxTraceBoundedDirectPayloadEnvelope tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound) := by
  let numericBound :=
    compactParserSyntaxTraceBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let bitBound :=
    compactParserSyntaxTraceBoundedDirectBitBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have hstateBoundary : stateBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have hstateCount : stateCount <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have hfuel : fuel <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have harea : (tokenCount + 1) * tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxTraceBoundedDirectNumericBound
    omega
  have hnumericBit : numericBound <= bitBound := by
    change numericBound <= numericBound + Nat.size numericBound + 1
    omega
  have htokenTableSize : Nat.size tokenTable <= bitBound :=
    (natSize_le_of_le htokenTable).trans (by
      exact hnumericBit)
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound :=
    (natSize_le_of_le hstateBoundary).trans (by
      exact hnumericBit)
  have hnumericSize : Nat.size numericBound <= bitBound := by
    change Nat.size numericBound <=
      numericBound + Nat.size numericBound + 1
    omega
  have hbitPositive : 1 <= bitBound := by
    change 1 <= numericBound + Nat.size numericBound + 1
    omega
  let countBound :=
    parserInitialFinalStateCountClosedDirectBound stateCount fuel numericBound
      hgraph.1
  let initialFinalBound :=
    compactParserInitialFinalBoundedClosedDirectBoundOfBounded tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound hgraph.2.1
  let adjacentProof :=
    compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext tokenTable
      width tokenCount stateBoundary stateCount fuel tableWidth valueBound
      numericBound bitBound hgraph.2.2 hfuel hvalueBound hwidth
      (hwidth.trans hnumericBit) htokenCount hstateCount htokenTableSize
      hstateBoundarySize harea (harea.trans hnumericBit) hnumericSize
      hbitPositive
  let innerProof := CertifiedPAContextProof.conjunction
    initialFinalBound.proof adjacentProof
  let outerProof :=
    CertifiedPAContextProof.conjunction countBound.proof innerProof
  let proof := CertifiedPAContextProof.cast
    (compactParserSyntaxTraceBoundedDirectClosedFormula_alignment tokenTable
      width tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound).symm
    outerProof
  refine { proof := proof, payloadLength_le := ?_ }
  have hadjacent :
      adjacentProof.payloadLength <=
        compactParserSyntaxAdjacentRowsBoundedDirectClosedResource tokenTable
          width tokenCount stateBoundary stateCount fuel tableWidth valueBound
          numericBound bitBound :=
    compileCompactParserSyntaxAdjacentRowsBoundedDirectClosedContext_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount fuel tableWidth
      valueBound numericBound bitBound hgraph.2.2 hfuel hvalueBound hwidth
      (hwidth.trans hnumericBit) htokenCount hstateCount htokenTableSize
      hstateBoundarySize harea (harea.trans hnumericBit) hnumericSize
      hbitPositive
  have hcount := countBound.payloadLength_le
  have hinitialFinal := initialFinalBound.payloadLength_le
  have hinner := CertifiedPAContextProof.conjunction_payloadLength_le
    initialFinalBound.proof adjacentProof
  have hinnerBound :
      innerProof.payloadLength <=
        compactParserInitialFinalBoundedDirectStructuralPayloadEnvelope
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedBoundary expectedCount taskKind
            taskBinderArity taskRepeatCount valueBound +
          compactParserSyntaxAdjacentRowsBoundedDirectClosedResource tokenTable
            width tokenCount stateBoundary stateCount fuel tableWidth valueBound
            numericBound bitBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserInitialFinalBoundedDirectClosedFormula tokenTable
              width tokenCount stateBoundary stateCount fuel inputBoundary
              inputCount expectedBoundary expectedCount taskKind
              taskBinderArity taskRepeatCount valueBound)
            (compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable
              width tokenCount stateBoundary stateCount fuel tableWidth
              valueBound) := by
    change
      (CertifiedPAContextProof.conjunction initialFinalBound.proof
        adjacentProof).payloadLength <= _
    exact hinner.trans (by omega)
  have houter := CertifiedPAContextProof.conjunction_payloadLength_le
    countBound.proof innerProof
  have houterBound :
      outerProof.payloadLength <=
        parserInitialFinalStateCountPayloadPolynomial stateCount fuel
            numericBound +
          compactParserInitialFinalBoundedDirectStructuralPayloadEnvelope
            tokenTable width tokenCount stateBoundary stateCount fuel
            inputBoundary inputCount expectedBoundary expectedCount taskKind
            taskBinderArity taskRepeatCount valueBound +
          compactParserSyntaxAdjacentRowsBoundedDirectClosedResource tokenTable
            width tokenCount stateBoundary stateCount fuel tableWidth valueBound
            numericBound bitBound +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            (compactParserInitialFinalBoundedDirectClosedFormula tokenTable
              width tokenCount stateBoundary stateCount fuel inputBoundary
              inputCount expectedBoundary expectedCount taskKind
              taskBinderArity taskRepeatCount valueBound)
            (compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable
              width tokenCount stateBoundary stateCount fuel tableWidth
              valueBound) +
          CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
            “!!(shortBinaryNumeralTerm stateCount) =
              !!(shortBinaryNumeralTerm fuel) + 1”
            (compactParserInitialFinalBoundedDirectClosedFormula tokenTable
                width tokenCount stateBoundary stateCount fuel inputBoundary
                inputCount expectedBoundary expectedCount taskKind
                taskBinderArity taskRepeatCount valueBound ⋏
              compactParserSyntaxAdjacentRowsBoundedClosedFormula tokenTable
                width tokenCount stateBoundary stateCount fuel tableWidth
                valueBound) := by
    change
      (CertifiedPAContextProof.conjunction countBound.proof
        innerProof).payloadLength <= _
    exact houter.trans (by omega)
  change (CertifiedPAContextProof.cast _ outerProof).payloadLength <= _
  rw [CertifiedPAContextProof.cast_payloadLength]
  unfold compactParserSyntaxTraceBoundedDirectPayloadEnvelope
  dsimp only [numericBound, bitBound, countBound, initialFinalBound,
    adjacentProof, innerProof, outerProof, proof]
  exact houterBound

#print axioms compactParserSyntaxTraceBoundedDirectClosedFormula_alignment
#print axioms compactParserSyntaxTraceBoundedClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxTraceBoundedDirectCompiler
