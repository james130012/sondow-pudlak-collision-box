import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds

/-! # Type of the seven fixed formula-transform endpoint leaf bounds -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundleTypes

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsDirectSyntax
open FoundationCompactNumericListedDirectFormulaTransformInitialParserSourceFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectNatListSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListSameRowsFullyFixedBounds

structure FormulaTransformInitialFinalSevenLeafBounds
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound
      bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) where
  count :
    ParserInitialFinalClosedDirectBound
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1”
      (parserInitialFinalStateCountPayloadPolynomial stateCount fuel
        numericBound)
  initialAt :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformStateAtRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount 0 witness.initialCoordinates
        witness.initialSizeWitness)
      (compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm 0) numericBound bitBound)
  initialParser :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformInitialParserSourcePublicFormula tokenTable width
        tokenCount inputBoundary inputCount binderArity
        witness.initialCoordinates)
      (compactFormulaTransformInitialParserSourceFullyFixedPayloadPolynomial
        numericBound bitBound)
  initialOutputCount :
    ParserInitialFinalClosedDirectBound
      “!!(shortBinaryNumeralTerm witness.initialCoordinates.outputCount) = 0”
      (formulaTransformInitialOutputCountZeroPayloadPolynomial numericBound
        bitBound)
  finalAt :
    ParserInitialFinalClosedDirectBound
      (compactFormulaTransformStateAtRowsClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel witness.finalCoordinates
        witness.finalSizeWitness)
      (compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm fuel) numericBound bitBound)
  finalParser :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount witness.finalCoordinates.parser expectedSuffixBoundary
        expectedSuffixCount witness.finalParserOutputStart
        witness.finalParserOutputBoundary
        witness.finalParserOutputBoundarySize)
      (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)
  finalOutput :
    ParserInitialFinalClosedDirectBound
      (compactAdditiveNatListSameRowsClosedFormula tokenTable width tokenCount
        expectedOutputBoundary expectedOutputCount
        witness.finalCoordinates.outputBoundary
        witness.finalCoordinates.outputCount)
      (sameRowsCompleteFullyFixedPayloadPolynomial numericBound bitBound)

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundleTypes
