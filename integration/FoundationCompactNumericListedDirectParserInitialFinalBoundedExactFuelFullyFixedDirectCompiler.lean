import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFixedCodeBounds
import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBoundOfData

/-! # Fully fixed direct compiler for bounded exact-fuel endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPublicRecursiveBounds
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectPublicCompilerArity23
open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSourceAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectTerminalAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectInstalledFreeVariables
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectFixedCodeBounds
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBoundOfData
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

def compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial
    (tokenCount valueBound numericBound bitBound : Nat) : Nat :=
  explicitBoundedWitnessDirectPublicPayloadEnvelope 23 0 valueBound
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
      numericBound bitBound)
    (compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      tokenCount numericBound bitBound)

structure CompactParserInitialFinalBoundedExactFuelFullyFixedPrepared
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat) where
  data : CompactParserInitialFinalBoundedDirectData tokenTable width tokenCount
    stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
    inputBoundary inputCount expectedBoundary expectedCount taskKind
    taskBinderArity taskRepeatCount valueBound
  bodyCode_le :
    (binaryFormulaCode
      (compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount)).length <=
      compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
        numericBound bitBound
  terminal : CertifiedPAContextProof ∅
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminal tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount ⇜
      fun coordinate => shortBinaryNumeralTerm
        (compactParserInitialFinalBoundedDirectWitnessValues data.witness
          coordinate))
  terminal_payloadLength_le :
    terminal.payloadLength <=
      compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
        tokenCount numericBound bitBound

noncomputable def
    compactParserInitialFinalBoundedExactFuelFullyFixedPreparedOfBounded
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat)
    (hbounded : CompactParserInitialFinalBounded tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
      inputBoundary inputCount expectedBoundary expectedCount taskKind
      taskBinderArity taskRepeatCount valueBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (hvalueBoundSucc : valueBound + 1 <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hinputBoundarySize : Nat.size inputBoundary <= bitBound)
    (hexpectedBoundarySize : Nat.size expectedBoundary <= bitBound)
    (htaskKindSize : Nat.size taskKind <= bitBound)
    (htaskBinderAritySize : Nat.size taskBinderArity <= bitBound)
    (htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    CompactParserInitialFinalBoundedExactFuelFullyFixedPrepared tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      valueBound numericBound bitBound := by
  let data := compactParserInitialFinalBoundedDirectDataOfBounded tokenTable
    width tokenCount stateBoundary stateCount
    (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
    valueBound hbounded
  let body := compactParserInitialFinalBoundedExactFuelDirectRawTerminal
    tokenTable width tokenCount stateBoundary stateCount inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
  let values := compactParserInitialFinalBoundedDirectWitnessValues data.witness
  let bodyCodeBound :=
    compactParserInitialFinalBoundedExactFuelDirectRawTerminalFixedCodeEnvelope
      numericBound bitBound
  let terminalResource :=
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
      tokenCount numericBound bitBound
  have hvalueBound : valueBound <= numericBound := by omega
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hinputCountSize : Nat.size inputCount <= bitBound :=
    (Nat.size_le_size hinputCount).trans hnumericSize
  have hexpectedCountSize : Nat.size expectedCount <= bitBound :=
    (Nat.size_le_size hexpectedCount).trans hnumericSize
  have hvalueBoundSize : Nat.size valueBound <= bitBound :=
    (Nat.size_le_size hvalueBound).trans hnumericSize
  have hbody : (binaryFormulaCode body).length <= bodyCodeBound := by
    dsimp only [body, bodyCodeBound]
    exact
      compactParserInitialFinalBoundedExactFuelDirectRawTerminal_code_length_le_fixed
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound numericBound bitBound htokenTableSize
        hwidthSize htokenCountSize hstateBoundarySize hstateCountSize
        hinputBoundarySize hinputCountSize hinputCount hexpectedBoundarySize
        hexpectedCountSize htaskKindSize htaskBinderAritySize
        htaskRepeatCountSize hvalueBoundSize
  let endpointBound :=
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedClosedDirectBoundOfData
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound data hwidth htokenCount
      hstateCount hinputCount hexpectedCount hvalueBoundSucc htokenTableSize
      hstateBoundarySize hinputBoundarySize hexpectedBoundarySize htaskKindSize
      htaskBinderAritySize htaskRepeatCountSize hnumericSize hbitPositive
  let installedFormula :=
    body ⇜ fun coordinate => shortBinaryNumeralTerm (values coordinate)
  have hterminalFormula :
      compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount data.witness = installedFormula :=
    (compactParserInitialFinalBoundedExactFuelDirectRawTerminal_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount data.witness).symm
  let terminalAtEmpty :=
    CertifiedPAContextProof.cast hterminalFormula endpointBound.proof
  have hterminal : terminalAtEmpty.payloadLength <= terminalResource := by
    change (CertifiedPAContextProof.cast hterminalFormula
      endpointBound.proof).payloadLength <= _
    rw [CertifiedPAContextProof.cast_payloadLength]
    exact endpointBound.payloadLength_le
  exact
    { data := data
      bodyCode_le := hbody
      terminal := terminalAtEmpty
      terminal_payloadLength_le := hterminal }

#print axioms
  compactParserInitialFinalBoundedExactFuelFullyFixedPreparedOfBounded

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
