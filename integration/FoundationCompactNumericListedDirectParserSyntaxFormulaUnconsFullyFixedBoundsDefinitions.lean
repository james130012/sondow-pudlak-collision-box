import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds

/-! # Fixed resource coordinates for the parser's exact Uncons syntax -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsAtomicFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropOneRowsFullyFixedBounds
open FoundationCompactNumericListedDirectAdditiveTripleBoundaryRowsHybridUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions

def parserSyntaxFormulaUnconsFormulaCodePolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound +
    taskConsParserFullyFixedPayloadEnvelope numericBound bitBound

def parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let parserSyntax :=
    parserSyntaxFormulaUnconsFormulaCodePolynomial tokenCount numericBound
      bitBound
  let tailSyntax :=
    unconsRowsWithSizeFormulaCodePolynomial tokenCount numericBound bitBound
  hybridConjunctionGeneralPayloadEnvelope parserSyntax
    (unconsPositiveFullyFixedPayloadPolynomial bitBound)
    (hybridConjunctionGeneralPayloadEnvelope parserSyntax
      (taskDropOneCompleteFullyFixedPayloadPolynomial numericBound bitBound)
      (hybridConjunctionGeneralPayloadEnvelope parserSyntax
        (tripleBoundaryRowsHybridUniversalFixedPayloadPolynomial numericBound
          bitBound)
        (hybridConjunctionGeneralPayloadEnvelope parserSyntax
          (taskConsParserFullyFixedPayloadEnvelope numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope tailSyntax
            (compactNatSizeFixedPayloadPolynomial bitBound)
            (parserAreaFixedPayloadPolynomial bitBound)))))

end FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
