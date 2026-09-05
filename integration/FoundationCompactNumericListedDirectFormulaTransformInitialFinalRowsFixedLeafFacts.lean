import integration.FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds

/-! # Scalar facts projected from the 44 formula-transform endpoint coordinates -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafFacts

open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalFormula
open FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

structure FormulaTransformInitialFinalLeafFacts
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound
      bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates) where
  widthValue : width <= numericBound
  tokenCountValue : tokenCount <= numericBound
  stateCountValue : stateCount <= numericBound
  inputCountValue : inputCount <= numericBound
  expectedOutputCountValue : expectedOutputCount <= numericBound
  expectedSuffixCountValue : expectedSuffixCount <= numericBound
  initialParserTokensCountValue :
    witness.initialCoordinates.parserTokensCount <= numericBound
  initialParserTasksCountValue :
    witness.initialCoordinates.parserTasksCount <= numericBound
  initialParserTasksFinishValue :
    witness.initialCoordinates.parserTasksFinish <= numericBound
  initialOutputCountValue :
    witness.initialCoordinates.outputCount <= numericBound
  finalParserTokensCountValue :
    witness.finalCoordinates.parserTokensCount <= numericBound
  finalParserTasksCountValue :
    witness.finalCoordinates.parserTasksCount <= numericBound
  finalParserTasksFinishValue :
    witness.finalCoordinates.parserTasksFinish <= numericBound
  finalOutputCountValue : witness.finalCoordinates.outputCount <= numericBound
  tokenTableSize : Nat.size tokenTable <= bitBound
  widthSize : Nat.size width <= bitBound
  tokenCountSize : Nat.size tokenCount <= bitBound
  stateBoundarySize : Nat.size stateBoundary <= bitBound
  inputBoundarySize : Nat.size inputBoundary <= bitBound
  inputCountSize : Nat.size inputCount <= bitBound
  expectedOutputBoundarySize :
    Nat.size expectedOutputBoundary <= bitBound
  expectedSuffixBoundarySize :
    Nat.size expectedSuffixBoundary <= bitBound
  expectedSuffixCountSize : Nat.size expectedSuffixCount <= bitBound
  binderAritySize : Nat.size binderArity <= bitBound
  initialStartSize : Nat.size witness.initialCoordinates.start <= bitBound
  initialParserFinishSize :
    Nat.size witness.initialCoordinates.parserFinish <= bitBound
  initialParserTokensFinishSize :
    Nat.size witness.initialCoordinates.parserTokensFinish <= bitBound
  initialParserTasksFinishSize :
    Nat.size witness.initialCoordinates.parserTasksFinish <= bitBound
  initialParserTokensBoundarySize :
    Nat.size witness.initialCoordinates.parserTokensBoundary <= bitBound
  initialParserTokensCountSize :
    Nat.size witness.initialCoordinates.parserTokensCount <= bitBound
  initialParserTasksBoundarySize :
    Nat.size witness.initialCoordinates.parserTasksBoundary <= bitBound
  initialParserTasksCountSize :
    Nat.size witness.initialCoordinates.parserTasksCount <= bitBound
  initialOutputBoundarySize :
    Nat.size witness.initialCoordinates.outputBoundary <= bitBound
  initialOutputCountSize :
    Nat.size witness.initialCoordinates.outputCount <= bitBound
  finalParserSize : CompactUnifiedParserStateCoordinateSizeBound
    witness.finalCoordinates.parser bitBound
  finalParserTokensBoundarySize :
    Nat.size witness.finalCoordinates.parserTokensBoundary <= bitBound
  finalParserTasksBoundarySize :
    Nat.size witness.finalCoordinates.parserTasksBoundary <= bitBound
  finalOutputBoundarySize :
    Nat.size witness.finalCoordinates.outputBoundary <= bitBound
  finalParserOutputStartSize :
    Nat.size witness.finalParserOutputStart <= bitBound
  finalParserOutputBoundarySize :
    Nat.size witness.finalParserOutputBoundary <= bitBound
  finalParserOutputBoundarySizeSize :
    Nat.size witness.finalParserOutputBoundarySize <= bitBound
  finalTasksFinishSuccSize :
    Nat.size (witness.finalCoordinates.parserTasksFinish + 1) <= bitBound

def formulaTransformInitialFinalLeafFactsOfBounds
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedOutputBoundary expectedOutputCount
      expectedSuffixBoundary expectedSuffixCount binderArity numericBound
      bitBound : Nat)
    (witness : CompactFormulaTransformInitialFinalWitnessCoordinates)
    (hvalue : FormulaTransformInitialFinalRowsValueBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness)
    (hsize : FormulaTransformInitialFinalRowsSizeBound tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hfinalTasksFinishSuccValue :
      witness.finalCoordinates.parserTasksFinish + 1 <= numericBound) :
    FormulaTransformInitialFinalLeafFacts tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound bitBound witness := by
  have hinitialParserValue :=
    initialParserValueBound_of_transformInitialFinal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness hvalue
  have hfinalParserValue :=
    finalParserValueBound_of_transformInitialFinal tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity numericBound witness hvalue
  have hinitialParserSize :=
    initialParserSizeBound_of_transformInitialFinal tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness hsize
  have hfinalParserSize :=
    finalParserSizeBound_of_transformInitialFinal tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount
      expectedOutputBoundary expectedOutputCount expectedSuffixBoundary
      expectedSuffixCount binderArity bitBound witness hsize
  refine
    { widthValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 1
      tokenCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 2
      stateCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 4
      inputCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 7
      expectedOutputCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 9
      expectedSuffixCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 11
      initialParserTokensCountValue := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserValue (5 : Fin 8)
      initialParserTasksCountValue := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserValue (7 : Fin 8)
      initialParserTasksFinishValue := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserValue (3 : Fin 8)
      initialOutputCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 23
      finalParserTokensCountValue := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hfinalParserValue (5 : Fin 8)
      finalParserTasksCountValue := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hfinalParserValue (7 : Fin 8)
      finalParserTasksFinishValue := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hfinalParserValue (3 : Fin 8)
      finalOutputCountValue := by
        simpa [FormulaTransformInitialFinalRowsValueBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hvalue 37
      tokenTableSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 0
      widthSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 1
      tokenCountSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 2
      stateBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 3
      inputBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 6
      inputCountSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 7
      expectedOutputBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 8
      expectedSuffixBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 10
      expectedSuffixCountSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 11
      binderAritySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 12
      initialStartSize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (0 : Fin 8)
      initialParserFinishSize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (1 : Fin 8)
      initialParserTokensFinishSize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (2 : Fin 8)
      initialParserTasksFinishSize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (3 : Fin 8)
      initialParserTokensBoundarySize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (4 : Fin 8)
      initialParserTokensCountSize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (5 : Fin 8)
      initialParserTasksBoundarySize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (6 : Fin 8)
      initialParserTasksCountSize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hinitialParserSize (7 : Fin 8)
      initialOutputBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 22
      initialOutputCountSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 23
      finalParserSize := hfinalParserSize
      finalParserTokensBoundarySize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hfinalParserSize (4 : Fin 8)
      finalParserTasksBoundarySize := by
        simpa [CompactFormulaTransformStateRowCoordinates.parser,
          compactUnifiedParserStateCoordinateValues] using
            hfinalParserSize (6 : Fin 8)
      finalOutputBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 36
      finalParserOutputStartSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 41
      finalParserOutputBoundarySize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 42
      finalParserOutputBoundarySizeSize := by
        simpa [FormulaTransformInitialFinalRowsSizeBound,
          compactFormulaTransformInitialFinalRowsEnvironment] using hsize 43
      finalTasksFinishSuccSize :=
        (Nat.size_le_size hfinalTasksFinishSuccValue).trans hnumericSize }

end FoundationCompactNumericListedDirectFormulaTransformInitialFinalRowsFixedLeafFacts
