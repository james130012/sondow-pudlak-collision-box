import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectAssembly

/-! # Fully fixed exact-fuel endpoint bound from checked bounded data -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectBound

open FoundationCompactNumericListedDirectParserInitialFinalBoundedFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelDirectStructuralCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectCompiler
open FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectAssembly

noncomputable def
    compactParserInitialFinalBoundedExactFuelFullyFixedClosedDirectBoundOfBounded
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
    CompactParserInitialFinalBoundedExactFuelClosedDirectBound
      (compactParserInitialFinalBoundedExactFuelDirectClosedFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound)
      (compactParserInitialFinalBoundedExactFuelFullyFixedPayloadPolynomial
        tokenCount valueBound numericBound bitBound) :=
  compactParserInitialFinalBoundedExactFuelFullyFixedClosedDirectBoundOfPrepared
    tokenTable width tokenCount stateBoundary stateCount inputBoundary
    inputCount expectedBoundary expectedCount taskKind taskBinderArity
    taskRepeatCount valueBound numericBound bitBound
    (compactParserInitialFinalBoundedExactFuelFullyFixedPreparedOfBounded
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount valueBound numericBound bitBound hbounded hwidth
      htokenCount hstateCount hinputCount hexpectedCount hvalueBoundSucc
      htokenTableSize hstateBoundarySize hinputBoundarySize
      hexpectedBoundarySize htaskKindSize htaskBinderAritySize
      htaskRepeatCountSize hnumericSize hbitPositive)

#print axioms
  compactParserInitialFinalBoundedExactFuelFullyFixedClosedDirectBoundOfBounded

end FoundationCompactNumericListedDirectParserInitialFinalBoundedExactFuelFullyFixedDirectBound
