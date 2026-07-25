import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

/-! # Fixed assembly envelopes for the combined parser endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsFixedSyntaxBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds

def parserInitialFinalRowsAssemblySyntaxResource
    (stateCount fuel tokenCount numericBound bitBound : Nat) : Nat :=
  parserInitialFinalStateCountPayloadPolynomial stateCount fuel numericBound +
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound +
    parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound +
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm fuel) numericBound bitBound +
    parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound +
    4 * (binaryNatCode 4).length + 1

def parserInitialFinalRowsFullyFixedPayloadPolynomial
    (stateCount fuel tokenCount numericBound bitBound : Nat) : Nat :=
  hybridFiveConjunctionGeneralPayloadEnvelope
    (parserInitialFinalRowsAssemblySyntaxResource stateCount fuel tokenCount
      numericBound bitBound)
    (parserInitialFinalStateCountPayloadPolynomial stateCount fuel
      numericBound)
    (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm 0) numericBound bitBound)
    (parserInitialStateFullyFixedPayloadPolynomial numericBound bitBound)
    (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      (shortBinaryNumeralTerm fuel) numericBound bitBound)
    (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

end FoundationCompactNumericListedDirectParserInitialFinalRowsFixedSyntaxBounds
