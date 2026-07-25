import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsFixedSyntaxBounds

/-! # Five fixed direct leaves extracted from the combined parser graph -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserInitialExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserInitialStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserFinalStateFullyFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsCoordinateBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedSyntaxBounds

structure ParserInitialFinalFiveLeafBounds
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) where
  count :
    ParserInitialFinalClosedDirectBound
      “!!(shortBinaryNumeralTerm stateCount) =
        !!(shortBinaryNumeralTerm fuel) + 1”
      (parserInitialFinalStateCountPayloadPolynomial stateCount fuel
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
      (compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
        stateBoundary stateCount fuel witness.finalCoordinates
        witness.finalSizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        (shortBinaryNumeralTerm fuel) numericBound bitBound)
  final :
    ParserInitialFinalClosedDirectBound
      (compactUnifiedParserFinalStateRowsClosedFormula tokenTable width
        tokenCount witness.finalCoordinates expectedBoundary expectedCount
        witness.outputStart witness.outputBoundary witness.outputBoundarySize)
      (parserFinalStateFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)

noncomputable def parserInitialFinalFiveLeafBoundsOfGraph
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound bitBound : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates)
    (hgraph : CompactUnifiedParserInitialFinalRows tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount witness)
    (hvalue : ParserInitialFinalRowsValueBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness)
    (hsize : ParserInitialFinalRowsSizeBound tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound witness)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserInitialFinalFiveLeafBounds tokenTable width tokenCount stateBoundary
      stateCount fuel inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount numericBound bitBound
      witness := by
  rcases hgraph with
    ⟨hcount, hinitialAt, hinitial, hfinalAt, hfinal⟩
  have hfinalGraph := hfinal
  rcases hfinal with
    ⟨⟨hprefix, hlayout, hsame⟩, houtputSize, houtputArea⟩
  have hwidthValue : width <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 1
  have htokenCountValue : tokenCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 2
  have hstateCountValue : stateCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 4
  have hinputCountValue : inputCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 7
  have hexpectedCountValue : expectedCount <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 9
  have houtputStartValue : witness.outputStart <= numericBound := by
    simpa [ParserInitialFinalRowsValueBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hvalue 33
  have hinitialCoordinatesValue :=
    initialCoordinatesValueBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness hvalue
  have hfinalCoordinatesValue :=
    finalCoordinatesValueBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount numericBound
      witness hvalue
  have htokenTableSize : Nat.size tokenTable <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 0
  have hwidthSize : Nat.size width <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 1
  have htokenCountSize : Nat.size tokenCount <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 2
  have hstateBoundarySize : Nat.size stateBoundary <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 3
  have hinputBoundarySize : Nat.size inputBoundary <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 6
  have hinputCountSize : Nat.size inputCount <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 7
  have hexpectedBoundarySize : Nat.size expectedBoundary <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 8
  have hexpectedCountSize : Nat.size expectedCount <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 9
  have htaskKindSize : Nat.size taskKind <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 10
  have htaskBinderAritySize : Nat.size taskBinderArity <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 11
  have htaskRepeatCountSize : Nat.size taskRepeatCount <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 12
  have hinitialCoordinatesSize :=
    initialCoordinatesSizeBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound witness
      hsize
  have hfinalCoordinatesSize :=
    finalCoordinatesSizeBound_of_combined tokenTable width tokenCount
      stateBoundary stateCount fuel inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount bitBound witness
      hsize
  have houtputStartSize : Nat.size witness.outputStart <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 33
  have houtputBoundarySize :
      Nat.size witness.outputBoundary <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 34
  have houtputBoundarySizeSize :
      Nat.size witness.outputBoundarySize <= bitBound := by
    simpa [ParserInitialFinalRowsSizeBound,
      compactUnifiedParserInitialFinalRowsEnvironment] using hsize 35
  have hinitialTasksCountValue :
      witness.initialCoordinates.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesValue (7 : Fin 8)
  have hinitialTasksFinishValue :
      witness.initialCoordinates.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesValue (3 : Fin 8)
  have hfinalTasksFinishValue :
      witness.finalCoordinates.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesValue (3 : Fin 8)
  have htasksFinishSuccLeOutput :
      witness.finalCoordinates.tasksFinish + 1 <= witness.outputStart := by
    rcases hprefix with
      ⟨innerStart, hinnerBound, hfirstCell, hsecondCell⟩
    have hinnerEq := hfirstCell.2.1
    have houtputEq := hsecondCell.2.1
    omega
  have hfinalTasksFinishSuccValue :
      witness.finalCoordinates.tasksFinish + 1 <= numericBound :=
    htasksFinishSuccLeOutput.trans houtputStartValue
  have hfinalTasksFinishSuccSize :
      Nat.size (witness.finalCoordinates.tasksFinish + 1) <= bitBound :=
    (Nat.size_le_size htasksFinishSuccLeOutput).trans houtputStartSize
  have hinitialStartSize : Nat.size witness.initialCoordinates.start <=
      bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (0 : Fin 8)
  have hinitialFinishSize : Nat.size witness.initialCoordinates.finish <=
      bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (1 : Fin 8)
  have hinitialTokensFinishSize :
      Nat.size witness.initialCoordinates.tokensFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (2 : Fin 8)
  have hinitialTasksFinishSize :
      Nat.size witness.initialCoordinates.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (3 : Fin 8)
  have hinitialTokensBoundarySize :
      Nat.size witness.initialCoordinates.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (4 : Fin 8)
  have hinitialTokensCountSize :
      Nat.size witness.initialCoordinates.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (5 : Fin 8)
  have hinitialTasksBoundarySize :
      Nat.size witness.initialCoordinates.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (6 : Fin 8)
  have hinitialTasksCountSize :
      Nat.size witness.initialCoordinates.tasksCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hinitialCoordinatesSize (7 : Fin 8)
  have hfinalStartSize : Nat.size witness.finalCoordinates.start <=
      bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (0 : Fin 8)
  have hfinalFinishSize : Nat.size witness.finalCoordinates.finish <=
      bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (1 : Fin 8)
  have hfinalTokensFinishSize :
      Nat.size witness.finalCoordinates.tokensFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (2 : Fin 8)
  have hfinalTasksFinishSize :
      Nat.size witness.finalCoordinates.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (3 : Fin 8)
  have hfinalTokensBoundarySize :
      Nat.size witness.finalCoordinates.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (4 : Fin 8)
  have hfinalTokensCountSize :
      Nat.size witness.finalCoordinates.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (5 : Fin 8)
  have hfinalTasksBoundarySize :
      Nat.size witness.finalCoordinates.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (6 : Fin 8)
  have hfinalTasksCountSize :
      Nat.size witness.finalCoordinates.tasksCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hfinalCoordinatesSize (7 : Fin 8)
  let count :=
    parserInitialFinalStateCountClosedDirectBound stateCount fuel numericBound
      hcount
  let initialAt :=
    parserInitialFinalStateAtRowsClosedDirectBoundOfGraph tokenTable width
      tokenCount stateBoundary stateCount 0 witness.initialCoordinates
      witness.initialSizeWitness numericBound bitBound hinitialAt hwidthValue
      htokenCountValue hstateCountValue hinitialCoordinatesValue
      htokenTableSize hstateBoundarySize hinitialCoordinatesSize hnumericSize
  let initial :=
    parserInitialStateClosedDirectBoundOfGraph tokenTable width tokenCount
      witness.initialCoordinates inputBoundary inputCount taskKind
      taskBinderArity taskRepeatCount numericBound bitBound hinitial
      hwidthValue htokenCountValue hinputCountValue
      hinitialTasksCountValue hinitialTasksFinishValue htokenTableSize
      hwidthSize htokenCountSize hinitialStartSize hinitialFinishSize
      hinitialTokensFinishSize hinitialTasksFinishSize
      hinitialTokensBoundarySize hinitialTokensCountSize
      hinitialTasksBoundarySize hinitialTasksCountSize hinputBoundarySize
      hinputCountSize htaskKindSize htaskBinderAritySize
      htaskRepeatCountSize hnumericSize
  let finalAt :=
    parserInitialFinalStateAtRowsClosedDirectBoundOfGraph tokenTable width
      tokenCount stateBoundary stateCount fuel witness.finalCoordinates
      witness.finalSizeWitness numericBound bitBound hfinalAt hwidthValue
      htokenCountValue hstateCountValue hfinalCoordinatesValue
      htokenTableSize hstateBoundarySize hfinalCoordinatesSize hnumericSize
  let final :=
    parserFinalStateClosedDirectBoundOfGraph tokenTable width tokenCount
      witness.finalCoordinates expectedBoundary expectedCount
      witness.outputStart witness.outputBoundary witness.outputBoundarySize
      numericBound bitBound hfinalGraph hwidthValue htokenCountValue
      hexpectedCountValue hfinalTasksFinishValue
      hfinalTasksFinishSuccValue htokenTableSize hwidthSize htokenCountSize
      hfinalStartSize hfinalFinishSize hfinalTokensFinishSize
      hfinalTasksFinishSize hfinalTokensBoundarySize hfinalTokensCountSize
      hfinalTasksBoundarySize hfinalTasksCountSize hexpectedBoundarySize
      hexpectedCountSize houtputStartSize houtputBoundarySize
      houtputBoundarySizeSize hfinalTasksFinishSuccSize hnumericSize
      hbitPositive
  exact
    { count := count
      initialAt := initialAt
      initial := initial
      finalAt := finalAt
      final := final }

#print axioms parserInitialFinalFiveLeafBoundsOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBundle
