import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundleTypes
import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafFacts

/-! # Assembly of the seven fixed formula-transform endpoint leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundle

open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundleTypes
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafFacts
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds

noncomputable def formulaTransformInitialFinalSevenLeafBoundsOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound
      bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hgraph : CompactFormulaTransformInitialFinalRows tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity witness)
    (hvalue : FormulaTransformInitialFinalRowsValueBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness)
    (hsize : FormulaTransformInitialFinalRowsSizeBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound)
    (hfinalTasksFinishSuccValue :
      witness.finalCoordinates.parserTasksFinish + 1 <= numericBound)
    (hbitPositive : 1 <= bitBound) :
    FormulaTransformInitialFinalSevenLeafBounds tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound bitBound witness := by
  rcases hgraph with
    ⟨hcount, hinitialAt, hinitialParser, hinitialOutputCount, hfinalAt,
      hfinalParser, hfinalOutput⟩
  let facts := formulaTransformInitialFinalLeafFactsOfBounds tokenTable width
    tokenCount stateBoundary stateCount fuel inputBoundary inputCount
    expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
    expectedSuffixCount binderArity numericBound bitBound witness hvalue hsize
    hnumericSize hfinalTasksFinishSuccValue
  refine
    { count := parserInitialFinalStateCountClosedDirectBound stateCount fuel
        numericBound hcount
      initialAt :=
        formulaTransformInitialFinalStateAtRowsClosedDirectBoundOfGraph
          tokenTable width tokenCount stateBoundary stateCount 0
          witness.initialCoordinates witness.initialSizeWitness numericBound
          bitBound hinitialAt facts.widthValue facts.tokenCountValue
          facts.stateCountValue facts.initialParserTokensCountValue
          facts.initialParserTasksCountValue facts.initialOutputCountValue
          facts.tokenTableSize facts.stateBoundarySize
          facts.initialParserTokensBoundarySize
          facts.initialParserTasksBoundarySize facts.initialOutputBoundarySize
          hnumericSize hnumericBit
      initialParser :=
        formulaTransformInitialParserSourceClosedDirectBoundOfGraph tokenTable
          width tokenCount inputBoundary inputCount binderArity numericBound
          bitBound witness.initialCoordinates hinitialParser facts.widthValue
          facts.tokenCountValue facts.inputCountValue
          facts.initialParserTasksCountValue
          facts.initialParserTasksFinishValue facts.tokenTableSize
          facts.widthSize facts.tokenCountSize facts.initialStartSize
          facts.initialParserFinishSize facts.initialParserTokensFinishSize
          facts.initialParserTasksFinishSize
          facts.initialParserTokensBoundarySize
          facts.initialParserTokensCountSize
          facts.initialParserTasksBoundarySize
          facts.initialParserTasksCountSize facts.inputBoundarySize
          facts.inputCountSize facts.binderAritySize hnumericSize
      initialOutputCount :=
        formulaTransformInitialOutputCountZeroClosedDirectBound
          witness.initialCoordinates.outputCount numericBound bitBound
          hinitialOutputCount facts.initialOutputCountSize
      finalAt :=
        formulaTransformInitialFinalStateAtRowsClosedDirectBoundOfGraph
          tokenTable width tokenCount stateBoundary stateCount fuel
          witness.finalCoordinates witness.finalSizeWitness numericBound
          bitBound hfinalAt facts.widthValue facts.tokenCountValue
          facts.stateCountValue facts.finalParserTokensCountValue
          facts.finalParserTasksCountValue facts.finalOutputCountValue
          facts.tokenTableSize facts.stateBoundarySize
          facts.finalParserTokensBoundarySize
          facts.finalParserTasksBoundarySize facts.finalOutputBoundarySize
          hnumericSize hnumericBit
      finalParser :=
        parserFinalStateClosedDirectBoundOfGraph tokenTable width tokenCount
          witness.finalCoordinates.parser expectedSuffixBoundary
          expectedSuffixCount witness.finalParserOutputStart
          witness.finalParserOutputBoundary witness.finalParserOutputBoundarySize
          numericBound bitBound hfinalParser facts.widthValue
          facts.tokenCountValue facts.expectedSuffixCountValue
          facts.finalParserTasksFinishValue hfinalTasksFinishSuccValue
          facts.tokenTableSize facts.widthSize facts.tokenCountSize
          (facts.finalParserSize (0 : Fin 8))
          (facts.finalParserSize (1 : Fin 8))
          (facts.finalParserSize (2 : Fin 8))
          (facts.finalParserSize (3 : Fin 8))
          (facts.finalParserSize (4 : Fin 8))
          (facts.finalParserSize (5 : Fin 8))
          (facts.finalParserSize (6 : Fin 8))
          (facts.finalParserSize (7 : Fin 8))
          facts.expectedSuffixBoundarySize facts.expectedSuffixCountSize
          facts.finalParserOutputStartSize
          facts.finalParserOutputBoundarySize
          facts.finalParserOutputBoundarySizeSize
          facts.finalTasksFinishSuccSize hnumericSize hbitPositive
      finalOutput :=
        formulaTransformInitialFinalSameRowsClosedDirectBoundOfGraph tokenTable
          width tokenCount expectedOutputBoundary expectedOutputCount
          witness.finalCoordinates.outputBoundary
          witness.finalCoordinates.outputCount numericBound bitBound
          hfinalOutput facts.widthValue facts.tokenCountValue
          facts.expectedOutputCountValue facts.tokenTableSize
          facts.expectedOutputBoundarySize facts.finalOutputBoundarySize
          hnumericSize }

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafBundle
