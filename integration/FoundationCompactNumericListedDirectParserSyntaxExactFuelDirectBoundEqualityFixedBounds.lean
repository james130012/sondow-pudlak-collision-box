import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
import integration.FoundationCompactPAExponentialShortNumeralCompilerBounds
import integration.FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
import integration.FoundationCompactSyntaxTransformationCodeBounds

/-! # Fixed resource for the exact-fuel normalized-bound equality -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserSyntaxExactFuelDirectBoundEqualityFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAExponentialShortNumeralCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAFiniteCaseSyntax
open FoundationCompactPAFiniteExhaustionPolynomialBounds
open FoundationCompactPAFiniteExhaustionPayloadPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerBounds
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowsBoundedExactFuelDirectUniversal

def compactParserSyntaxExactFuelDirectBoundEqualityTermCodePolynomial
    (numericBound : Nat) : Nat :=
  iteratedSuccessorTermCodePolynomial 0 numericBound +
    6 * boundedWitnessNumeralTermCodeEnvelope numericBound +
    6 * compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound + 1

def compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
    (numericBound : Nat) : Nat :=
  contextualEqualityTransitivityUniformPayloadBound 0
    (compactParserSyntaxExactFuelDirectBoundEqualityTermCodePolynomial
      numericBound)
    (closedShortBoundEqualityPayloadPolynomial numericBound)
    (compactParserSyntaxExactFuelEqualityFixedPayloadPolynomial numericBound)

private theorem closedShortBoundEqualityPayloadPolynomial_mono_exactFuel
    {small large : Nat} (hbound : small <= large) :
    closedShortBoundEqualityPayloadPolynomial small <=
      closedShortBoundEqualityPayloadPolynomial large := by
  have hshort := shortToIteratedPayloadPolynomial_mono_public hbound
  have hterm := shortToIteratedStepTermCodePolynomial_mono hbound
  have hprimitive := paPrimitiveCostEnvelope_mono_short hterm
  unfold closedShortBoundEqualityPayloadPolynomial
  omega

theorem compactParserSyntaxExactFuelDirectBoundEqualityResource_le_fixed
    (inputCount numericBound : Nat)
    (hinputCount : inputCount <= numericBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound) :
    compactParserSyntaxExactFuelDirectBoundEqualityResource inputCount <=
      compactParserSyntaxExactFuelDirectBoundEqualityFixedPayloadPolynomial
        numericBound := by
  let fuel := compactParserSyntaxExactFuel inputCount
  let left := iteratedSuccessorTerm 0 fuel
  let short : ValuationTerm := shortBinaryNumeralTerm fuel
  let middle : ValuationTerm := Rew.free (Rew.bShift short)
  let exact : ValuationTerm := compactParserSyntaxExactFuelTerm inputCount
  let right : ValuationTerm := Rew.free (Rew.bShift exact)
  let termBound :=
    compactParserSyntaxExactFuelDirectBoundEqualityTermCodePolynomial
      numericBound
  have hleftRaw := iteratedSuccessorTerm_code_length_le_polynomial 0 fuel
  have hleftMono := iteratedSuccessorTermCodePolynomial_mono 0 hfuel
  have hleftCore : (binaryTermCode left).length <=
      iteratedSuccessorTermCodePolynomial 0 numericBound := by
    dsimp only [left]
    exact hleftRaw.trans hleftMono
  have hleft : (binaryTermCode left).length <= termBound := by
    exact hleftCore.trans (by
      dsimp only [termBound]
      unfold compactParserSyntaxExactFuelDirectBoundEqualityTermCodePolynomial
      omega)
  have hshort : (binaryTermCode short).length <=
      boundedWitnessNumeralTermCodeEnvelope numericBound := by
    dsimp only [short]
    exact shortBinaryNumeralTerm_code_length_le_bound fuel numericBound hfuel
  have hshortSymbols := termSymbolCount_le_binaryTermCode_length short
  have hmiddleShift := binaryTermCode_bShift_length_le_add_symbols short
  have hmiddleShiftTight :
      (binaryTermCode (Rew.bShift short)).length <=
        3 * (binaryTermCode short).length := by
    omega
  have hmiddleFree := binaryTermCode_free_length_le (Rew.bShift short)
  have hmiddle : (binaryTermCode middle).length <= termBound := by
    dsimp only [middle, termBound]
    unfold compactParserSyntaxExactFuelDirectBoundEqualityTermCodePolynomial
    omega
  have hexact : (binaryTermCode exact).length <=
      compactParserSyntaxExactFuelTermFixedCodePolynomial numericBound := by
    dsimp only [exact]
    exact compactParserSyntaxExactFuelTerm_code_length_le_fixed inputCount
      numericBound hinputCount
  have hexactSymbols := termSymbolCount_le_binaryTermCode_length exact
  have hrightShift := binaryTermCode_bShift_length_le_add_symbols exact
  have hrightShiftTight :
      (binaryTermCode (Rew.bShift exact)).length <=
        3 * (binaryTermCode exact).length := by
    omega
  have hrightFree := binaryTermCode_free_length_le (Rew.bShift exact)
  have hright : (binaryTermCode right).length <= termBound := by
    dsimp only [right, termBound]
    unfold compactParserSyntaxExactFuelDirectBoundEqualityTermCodePolynomial
    omega
  have hleftPayload :
      closedShortBoundEqualityPayloadPolynomial fuel <=
        closedShortBoundEqualityPayloadPolynomial numericBound :=
    closedShortBoundEqualityPayloadPolynomial_mono_exactFuel hfuel
  have hrightPayload :
      compactParserSyntaxExactFuelEqualityPayloadResource inputCount <=
        compactParserSyntaxExactFuelEqualityFixedPayloadPolynomial
          numericBound :=
    compactParserSyntaxExactFuelEqualityPayloadResource_le_fixed inputCount
      numericBound hinputCount
  have hmono := contextualEqualityTransitivityStructuralPayloadBound_mono
    ((∅ : Finset ValuationFormula).image Rewriting.shift)
    left middle right
    (closedShortBoundEqualityPayloadPolynomial fuel)
    (compactParserSyntaxExactFuelEqualityPayloadResource inputCount)
    (closedShortBoundEqualityPayloadPolynomial numericBound)
    (compactParserSyntaxExactFuelEqualityFixedPayloadPolynomial numericBound)
    hleftPayload hrightPayload
  have huniform := contextualEqualityTransitivityStructuralPayloadBound_le_uniform
    ((∅ : Finset ValuationFormula).image Rewriting.shift)
    left middle right
    (closedShortBoundEqualityPayloadPolynomial numericBound)
    (compactParserSyntaxExactFuelEqualityFixedPayloadPolynomial numericBound)
    0 termBound (by simp) (by simp [formulaCodeSum]) hleft hmiddle hright
  unfold compactParserSyntaxExactFuelDirectBoundEqualityResource
  dsimp only [fuel, left, short, middle, exact, right, termBound] at hmono huniform
  exact hmono.trans huniform

#print axioms
  compactParserSyntaxExactFuelDirectBoundEqualityResource_le_fixed

end FoundationCompactNumericListedDirectParserSyntaxExactFuelDirectBoundEqualityFixedBounds
