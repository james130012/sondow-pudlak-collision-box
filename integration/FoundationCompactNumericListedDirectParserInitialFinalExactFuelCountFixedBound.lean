import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle

/-! # Fully fixed count leaf for exact-fuel parser endpoints -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound

open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

def compactParserInitialFinalExactFuelCountFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  compactParserSyntaxExactStateCountEqualityFixedPayloadPolynomial numericBound

theorem compactParserInitialFinalExactFuelCountResource_le_fixed
    (inputCount numericBound : Nat)
    (hinputCount : inputCount <= numericBound) :
    compactParserInitialFinalExactFuelCountResource inputCount <=
      compactParserInitialFinalExactFuelCountFixedPayloadPolynomial
        numericBound := by
  simpa only [compactParserInitialFinalExactFuelCountResource,
    compactParserSyntaxExactStateCountTerm,
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial] using
      compactParserSyntaxExactStateCountEqualityPayloadResource_le_fixed
        inputCount numericBound hinputCount

#print axioms compactParserInitialFinalExactFuelCountResource_le_fixed

end FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
