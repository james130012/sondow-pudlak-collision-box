import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBound
import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBoundsOfData

/-! # Clean fully fixed exact-fuel endpoint proof from checked data -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBoundOfData

open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectCheckedData
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBoundsOfData
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBound
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

noncomputable def
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedClosedDirectBoundOfData
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound : Nat)
    (data : CompactParserInitialFinalBoundedDirectData tokenTable width
      tokenCount stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
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
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialFinalRowsExactFuelClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
        data.witness)
      (compactUnifiedParserInitialFinalRowsExactFuelFullyFixedPayloadPolynomial
        tokenCount numericBound bitBound) := by
  let leaves := parserInitialFinalExactFuelFiveFixedLeafBoundsOfData tokenTable
    width tokenCount stateBoundary stateCount inputBoundary inputCount
    expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
    valueBound numericBound bitBound data hwidth htokenCount hstateCount
    hinputCount hexpectedCount hvalueBoundSucc htokenTableSize
    hstateBoundarySize hinputBoundarySize hexpectedBoundarySize htaskKindSize
    htaskBinderAritySize htaskRepeatCountSize hnumericSize hbitPositive
  exact
    compactUnifiedParserInitialFinalRowsExactFuelFullyFixedClosedDirectBoundOfLeaves
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound data.witness leaves

#print axioms
  compactUnifiedParserInitialFinalRowsExactFuelFullyFixedClosedDirectBoundOfData

end FoundationCompactNumericListedDirectParserInitialFinalExactFuelFullyFixedDirectBoundOfData
