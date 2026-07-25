import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodyTreeFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
import integration.FoundationCompactNumericListedDirectArithmeticRelCodeValidFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! Fixed payload envelopes for the valid and invalid long relation paths. -/

noncomputable section

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongEnvelopeFullyFixedBounds

open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectArithmeticRelCodeValidFullyFixedBounds

def relationValidPairFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (arithmeticRelCodeValidFullyFixedPayloadPolynomial bitBound)
    (syntaxTermFunctionFullyFixedPayloadEnvelope tokenCount numericBound
      bitBound)

def relationValidChoiceFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (relationValidPairFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

def relationValidCodeTailFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
      numericBound bitBound)
    (relationValidChoiceFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

def relationValidArityTailFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
      numericBound bitBound)
    (relationValidCodeTailFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

def relationValidLongBranchFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (parserFormulaTermLeFixedPayloadPolynomial bitBound)
    (relationValidArityTailFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

def relationValidBodyFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (relationValidLongBranchFullyFixedPayloadPolynomial tokenCount
      numericBound bitBound)

def relationInvalidPairFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (arithmeticRelCodeInvalidFullyFixedPayloadPolynomial bitBound)
    (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)

def relationInvalidChoiceFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (relationInvalidPairFullyFixedPayloadPolynomial numericBound bitBound)

def relationInvalidCodeTailFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
      numericBound bitBound)
    (relationInvalidChoiceFullyFixedPayloadPolynomial numericBound bitBound)

def relationInvalidArityTailFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
      numericBound bitBound)
    (relationInvalidCodeTailFullyFixedPayloadPolynomial numericBound bitBound)

def relationInvalidLongBranchFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (parserFormulaTermLeFixedPayloadPolynomial bitBound)
    (relationInvalidArityTailFullyFixedPayloadPolynomial numericBound bitBound)

def relationInvalidBodyFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (relationInvalidLongBranchFullyFixedPayloadPolynomial numericBound
      bitBound)

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationLongEnvelopeFullyFixedBounds
