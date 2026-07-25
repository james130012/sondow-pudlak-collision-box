import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds

/-!
# Shared fixed syntax and payload envelopes for Term function decisions
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidFixedBoundsCore
open FoundationCompactNumericListedDirectArithmeticFuncCodeInvalidFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds

def syntaxTermFunctionDecisionFixedSyntaxPolynomial (bitBound : Nat) : Nat :=
  compactUnifiedParserSyntaxTermFormulaSyntaxFixedPolynomial bitBound + 1

theorem compactUnifiedParserSyntaxTermDecisionExplicitFormula_code_le_explicit
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness)).length <=
      (binaryFormulaCode
        (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width
          tokenCount current next binderArity witness)).length := by
  unfold compactUnifiedParserSyntaxTermExplicitFormula
    compactUnifiedParserSyntaxTermBranchExplicitFormula
  simp only [binaryFormulaCode, List.length_append]
  omega

theorem syntaxTermDecisionComponent_code_length_le_fixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (bitBound : Nat)
    (component : ValuationFormula)
    (hcomponent :
      (binaryFormulaCode component).length <=
        (binaryFormulaCode
          (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable
            width tokenCount current next binderArity witness)).length)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    (binaryFormulaCode component).length <=
      syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound := by
  exact hcomponent.trans
    ((compactUnifiedParserSyntaxTermDecisionExplicitFormula_code_le_explicit
      tokenTable width tokenCount current next binderArity witness).trans
      ((compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_fixed
        tokenTable width tokenCount current next binderArity witness bitBound
        hsize).trans (by
          unfold syntaxTermFunctionDecisionFixedSyntaxPolynomial
          omega)))

theorem syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive
    (bitBound : Nat) :
    1 <= syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound := by
  unfold syntaxTermFunctionDecisionFixedSyntaxPolynomial
  omega

def syntaxTermValidBranchFixedPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound)
    (compactAdditiveArithmeticFuncCodeValidFullyFixedPayloadPolynomial
      bitBound)
    (syntaxTermFunctionFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)

def syntaxTermInvalidBranchFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound)
    (compactAdditiveArithmeticFuncCodeInvalidFullyFixedPayloadPolynomial
      bitBound)
    (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)

def syntaxTermValidityChoiceFixedPayloadEnvelope
    (chosenResource bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound)
    chosenResource

def syntaxTermTwoSelectedFixedPayloadEnvelope
    (atFunctionResource validityChoiceResource bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let atFunctionTail :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource atFunctionResource
      validityChoiceResource
  let functionSelected :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaTermLeFixedPayloadPolynomial bitBound) atFunctionTail
  let shortFunctionChoice :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource functionSelected
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
    shortFunctionChoice

def syntaxTermTwoDecisionPathFixedPayloadEnvelope
    (selectedResource bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        selectedResource))

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
