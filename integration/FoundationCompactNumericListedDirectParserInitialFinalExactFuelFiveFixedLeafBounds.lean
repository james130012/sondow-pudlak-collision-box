import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelFinalAtFixedBound
import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound

/-! # Five fixed parser endpoint leaves at exact fuel -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 65536
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBounds

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelFinalAtFixedBound
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality

noncomputable def parserInitialFinalExactFuelCountFixedClosedDirectBound
    (stateCount inputCount numericBound : Nat)
    (hcount : stateCount = compactParserSyntaxExactFuel inputCount + 1)
    (hinputCount : inputCount <= numericBound) :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelCountFormula stateCount inputCount)
      (compactParserInitialFinalExactFuelCountFixedPayloadPolynomial
        numericBound) := by
  let old := parserInitialFinalExactFuelCountClosedDirectBound stateCount
    inputCount hcount
  refine ⟨old.proof, ?_⟩
  exact old.payloadLength_le.trans
    (compactParserInitialFinalExactFuelCountResource_le_fixed inputCount
      numericBound hinputCount)

structure ParserInitialFinalExactFuelFiveFixedLeafBounds
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      inputBoundary expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) where
  count :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelCountFormula stateCount inputCount)
      (compactParserInitialFinalExactFuelCountFixedPayloadPolynomial
        numericBound)
  initialAt :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount 0 witness.initialCoordinates
        witness.initialSizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm 0) numericBound bitBound)
  initial :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserInitialStateRowsClosedFormula tokenTable width
        tokenCount witness.initialCoordinates inputBoundary inputCount taskKind
        taskBinderArity taskRepeatCount)
      (parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound)
  finalAt :
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount witness.finalCoordinates
        witness.finalSizeWitness)
      (compactParserInitialFinalExactFuelFinalAtFixedPayloadPolynomial
        numericBound bitBound)
  final :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width tokenCount
        witness.finalCoordinates expectedBoundary expectedCount
        witness.outputStart witness.outputBoundary witness.outputBoundarySize)
      (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)

#print axioms parserInitialFinalExactFuelCountFixedClosedDirectBound

end FoundationCompactNumericListedDirectParserInitialFinalExactFuelFiveFixedLeafBounds
