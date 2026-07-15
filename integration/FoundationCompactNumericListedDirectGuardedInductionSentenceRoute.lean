import integration.FoundationCompactNumericListedDirectSuccIndSentenceRoute
import integration.FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
import integration.FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
import integration.FoundationCompactNumericGuardedInductionSentence

/-!
# Direct checked route for the guarded induction sentence

The route constructs the complete successor-induction formula, computes its
exact free-variable supremum, fixes those variables, and prefixes the exact
number of universal quantifiers.  The final slot is the public PA induction
certificate sentence.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectGuardedInductionSentenceRoute

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericGuardedInductionSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndSentenceRoute
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint

structure CompactGuardedInductionSentenceRouteCoordinates where
  sentence : CompactSuccIndSentenceRouteCoordinates
  fvSup : CompactFormulaFvSupTotalEndpointCoordinates
  closure : CompactFixedAllClosureTotalEndpointCoordinates

def CompactGuardedInductionSentenceRoute
    (tokenTable width tokenCount depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed candidate :
      CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) : Prop :=
  CompactSuccIndSentenceRoute tokenTable width tokenCount
      body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence coordinates.sentence /\
    CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount 0 depth
      empty sentence fvarList coordinates.fvSup /\
    CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount depth
      empty depthCapture sentence fixed candidate coordinates.closure

def compactGuardedInductionSentenceRouteDef : 𝚺₀.Semisentence 177 := .mkSigma
  “tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      zeroWitnessStart zeroWitnessFinish zeroWitnessBoundary zeroWitnessCount
        zeroWitnessBoundarySize
      openZeroWitnessStart openZeroWitnessFinish openZeroWitnessBoundary
        openZeroWitnessCount openZeroWitnessBoundarySize
      openSuccessorWitnessStart openSuccessorWitnessFinish
        openSuccessorWitnessBoundary openSuccessorWitnessCount
        openSuccessorWitnessBoundarySize
      captureOneStart captureOneFinish captureOneBoundary captureOneCount
        captureOneBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      baseStart baseFinish baseBoundary baseCount baseBoundarySize
      negatedBaseStart negatedBaseFinish negatedBaseBoundary negatedBaseCount
        negatedBaseBoundarySize
      stepZeroStart stepZeroFinish stepZeroBoundary stepZeroCount
        stepZeroBoundarySize
      stepSuccessorStart stepSuccessorFinish stepSuccessorBoundary
        stepSuccessorCount stepSuccessorBoundarySize
      negatedStepZeroStart negatedStepZeroFinish negatedStepZeroBoundary
        negatedStepZeroCount negatedStepZeroBoundarySize
      stepDisjunctionStart stepDisjunctionFinish stepDisjunctionBoundary
        stepDisjunctionCount stepDisjunctionBoundarySize
      quantifiedStepStart quantifiedStepFinish quantifiedStepBoundary
        quantifiedStepCount quantifiedStepBoundarySize
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepBoundary negatedQuantifiedStepCount
        negatedQuantifiedStepBoundarySize
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalBoundary
        quantifiedFinalCount quantifiedFinalBoundarySize
      innerStart innerFinish innerBoundary innerCount innerBoundarySize
      sentenceStart sentenceFinish sentenceBoundary sentenceCount
        sentenceBoundarySize
      baseStateBoundary baseStateCount baseTableWidth baseValueBound
      baseNegationStateBoundary baseNegationStateCount baseNegationTableWidth
        baseNegationValueBound
      openZeroShiftedStart openZeroShiftedFinish openZeroShiftedBoundary
        openZeroShiftedCount openZeroShiftedBoundarySize
      openZeroSubstitutedStart openZeroSubstitutedFinish
        openZeroSubstitutedBoundary openZeroSubstitutedCount
        openZeroSubstitutedBoundarySize
      openZeroShiftStateBoundary openZeroShiftStateCount
        openZeroShiftTableWidth openZeroShiftValueBound
      openZeroSubstitutionStateBoundary openZeroSubstitutionStateCount
        openZeroSubstitutionTableWidth openZeroSubstitutionValueBound
      openZeroFixitrStateBoundary openZeroFixitrStateCount
        openZeroFixitrTableWidth openZeroFixitrValueBound
      openSuccessorShiftedStart openSuccessorShiftedFinish
        openSuccessorShiftedBoundary openSuccessorShiftedCount
        openSuccessorShiftedBoundarySize
      openSuccessorSubstitutedStart openSuccessorSubstitutedFinish
        openSuccessorSubstitutedBoundary openSuccessorSubstitutedCount
        openSuccessorSubstitutedBoundarySize
      openSuccessorShiftStateBoundary openSuccessorShiftStateCount
        openSuccessorShiftTableWidth openSuccessorShiftValueBound
      openSuccessorSubstitutionStateBoundary
        openSuccessorSubstitutionStateCount openSuccessorSubstitutionTableWidth
        openSuccessorSubstitutionValueBound
      openSuccessorFixitrStateBoundary openSuccessorFixitrStateCount
        openSuccessorFixitrTableWidth openSuccessorFixitrValueBound
      stepNegationStateBoundary stepNegationStateCount stepNegationTableWidth
        stepNegationValueBound
      quantifiedStepNegationStateBoundary quantifiedStepNegationStateCount
        quantifiedStepNegationTableWidth quantifiedStepNegationValueBound
      depth
      fvarListStart fvarListFinish fvarListBoundary fvarListCount
        fvarListBoundarySize
      depthCaptureStart depthCaptureFinish depthCaptureBoundary
        depthCaptureCount depthCaptureBoundarySize
      fixedStart fixedFinish fixedBoundary fixedCount fixedBoundarySize
      candidateStart candidateFinish candidateBoundary candidateCount
        candidateBoundarySize
      fvSupStateBoundary fvSupStateCount fvSupTableWidth fvSupValueBound
      closureStateBoundary closureStateCount closureTableWidth
        closureValueBound.
    !(compactSuccIndSentenceRouteDef)
      tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      zeroWitnessStart zeroWitnessFinish zeroWitnessBoundary zeroWitnessCount
        zeroWitnessBoundarySize
      openZeroWitnessStart openZeroWitnessFinish openZeroWitnessBoundary
        openZeroWitnessCount openZeroWitnessBoundarySize
      openSuccessorWitnessStart openSuccessorWitnessFinish
        openSuccessorWitnessBoundary openSuccessorWitnessCount
        openSuccessorWitnessBoundarySize
      captureOneStart captureOneFinish captureOneBoundary captureOneCount
        captureOneBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      baseStart baseFinish baseBoundary baseCount baseBoundarySize
      negatedBaseStart negatedBaseFinish negatedBaseBoundary negatedBaseCount
        negatedBaseBoundarySize
      stepZeroStart stepZeroFinish stepZeroBoundary stepZeroCount
        stepZeroBoundarySize
      stepSuccessorStart stepSuccessorFinish stepSuccessorBoundary
        stepSuccessorCount stepSuccessorBoundarySize
      negatedStepZeroStart negatedStepZeroFinish negatedStepZeroBoundary
        negatedStepZeroCount negatedStepZeroBoundarySize
      stepDisjunctionStart stepDisjunctionFinish stepDisjunctionBoundary
        stepDisjunctionCount stepDisjunctionBoundarySize
      quantifiedStepStart quantifiedStepFinish quantifiedStepBoundary
        quantifiedStepCount quantifiedStepBoundarySize
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepBoundary negatedQuantifiedStepCount
        negatedQuantifiedStepBoundarySize
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalBoundary
        quantifiedFinalCount quantifiedFinalBoundarySize
      innerStart innerFinish innerBoundary innerCount innerBoundarySize
      sentenceStart sentenceFinish sentenceBoundary sentenceCount
        sentenceBoundarySize
      baseStateBoundary baseStateCount baseTableWidth baseValueBound
      baseNegationStateBoundary baseNegationStateCount baseNegationTableWidth
        baseNegationValueBound
      openZeroShiftedStart openZeroShiftedFinish openZeroShiftedBoundary
        openZeroShiftedCount openZeroShiftedBoundarySize
      openZeroSubstitutedStart openZeroSubstitutedFinish
        openZeroSubstitutedBoundary openZeroSubstitutedCount
        openZeroSubstitutedBoundarySize
      openZeroShiftStateBoundary openZeroShiftStateCount
        openZeroShiftTableWidth openZeroShiftValueBound
      openZeroSubstitutionStateBoundary openZeroSubstitutionStateCount
        openZeroSubstitutionTableWidth openZeroSubstitutionValueBound
      openZeroFixitrStateBoundary openZeroFixitrStateCount
        openZeroFixitrTableWidth openZeroFixitrValueBound
      openSuccessorShiftedStart openSuccessorShiftedFinish
        openSuccessorShiftedBoundary openSuccessorShiftedCount
        openSuccessorShiftedBoundarySize
      openSuccessorSubstitutedStart openSuccessorSubstitutedFinish
        openSuccessorSubstitutedBoundary openSuccessorSubstitutedCount
        openSuccessorSubstitutedBoundarySize
      openSuccessorShiftStateBoundary openSuccessorShiftStateCount
        openSuccessorShiftTableWidth openSuccessorShiftValueBound
      openSuccessorSubstitutionStateBoundary
        openSuccessorSubstitutionStateCount openSuccessorSubstitutionTableWidth
        openSuccessorSubstitutionValueBound
      openSuccessorFixitrStateBoundary openSuccessorFixitrStateCount
        openSuccessorFixitrTableWidth openSuccessorFixitrValueBound
      stepNegationStateBoundary stepNegationStateCount stepNegationTableWidth
        stepNegationValueBound
      quantifiedStepNegationStateBoundary quantifiedStepNegationStateCount
        quantifiedStepNegationTableWidth quantifiedStepNegationValueBound ∧
    !(compactFormulaFvSupTotalEndpointDef)
      tokenTable width tokenCount 0 depth
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      sentenceStart sentenceFinish sentenceBoundary sentenceCount
        sentenceBoundarySize
      fvarListStart fvarListFinish fvarListBoundary fvarListCount
        fvarListBoundarySize
      fvSupStateBoundary fvSupStateCount fvSupTableWidth fvSupValueBound ∧
    !(compactFixedAllClosureTotalEndpointDef)
      tokenTable width tokenCount depth
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      depthCaptureStart depthCaptureFinish depthCaptureBoundary
        depthCaptureCount depthCaptureBoundarySize
      sentenceStart sentenceFinish sentenceBoundary sentenceCount
        sentenceBoundarySize
      fixedStart fixedFinish fixedBoundary fixedCount fixedBoundarySize
      candidateStart candidateFinish candidateBoundary candidateCount
        candidateBoundarySize
      closureStateBoundary closureStateCount closureTableWidth
        closureValueBound”

def compactGuardedInductionSentenceRouteEnvironment
    (tokenTable width tokenCount depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed candidate :
      CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) :
    Fin 177 -> Nat :=
  ![tokenTable, width, tokenCount,
    body.start, body.finish, body.boundary, body.count, body.boundarySize,
    zeroWitness.start, zeroWitness.finish, zeroWitness.boundary,
      zeroWitness.count, zeroWitness.boundarySize,
    openZeroWitness.start, openZeroWitness.finish, openZeroWitness.boundary,
      openZeroWitness.count, openZeroWitness.boundarySize,
    openSuccessorWitness.start, openSuccessorWitness.finish,
      openSuccessorWitness.boundary, openSuccessorWitness.count,
      openSuccessorWitness.boundarySize,
    captureOne.start, captureOne.finish, captureOne.boundary, captureOne.count,
      captureOne.boundarySize,
    empty.start, empty.finish, empty.boundary, empty.count,
      empty.boundarySize,
    base.start, base.finish, base.boundary, base.count, base.boundarySize,
    negatedBase.start, negatedBase.finish, negatedBase.boundary,
      negatedBase.count, negatedBase.boundarySize,
    stepZero.start, stepZero.finish, stepZero.boundary, stepZero.count,
      stepZero.boundarySize,
    stepSuccessor.start, stepSuccessor.finish, stepSuccessor.boundary,
      stepSuccessor.count, stepSuccessor.boundarySize,
    negatedStepZero.start, negatedStepZero.finish,
      negatedStepZero.boundary, negatedStepZero.count,
      negatedStepZero.boundarySize,
    stepDisjunction.start, stepDisjunction.finish,
      stepDisjunction.boundary, stepDisjunction.count,
      stepDisjunction.boundarySize,
    quantifiedStep.start, quantifiedStep.finish, quantifiedStep.boundary,
      quantifiedStep.count, quantifiedStep.boundarySize,
    negatedQuantifiedStep.start, negatedQuantifiedStep.finish,
      negatedQuantifiedStep.boundary, negatedQuantifiedStep.count,
      negatedQuantifiedStep.boundarySize,
    quantifiedFinal.start, quantifiedFinal.finish, quantifiedFinal.boundary,
      quantifiedFinal.count, quantifiedFinal.boundarySize,
    innerDisjunction.start, innerDisjunction.finish,
      innerDisjunction.boundary, innerDisjunction.count,
      innerDisjunction.boundarySize,
    sentence.start, sentence.finish, sentence.boundary, sentence.count,
      sentence.boundarySize,
    coordinates.sentence.base.baseTrace.stateBoundary,
      coordinates.sentence.base.baseTrace.stateCount,
      coordinates.sentence.base.baseTrace.tableWidth,
      coordinates.sentence.base.baseTrace.valueBound,
    coordinates.sentence.base.negationTrace.stateBoundary,
      coordinates.sentence.base.negationTrace.stateCount,
      coordinates.sentence.base.negationTrace.tableWidth,
      coordinates.sentence.base.negationTrace.valueBound,
    coordinates.sentence.openZero.shifted.start,
      coordinates.sentence.openZero.shifted.finish,
      coordinates.sentence.openZero.shifted.boundary,
      coordinates.sentence.openZero.shifted.count,
      coordinates.sentence.openZero.shifted.boundarySize,
    coordinates.sentence.openZero.substituted.start,
      coordinates.sentence.openZero.substituted.finish,
      coordinates.sentence.openZero.substituted.boundary,
      coordinates.sentence.openZero.substituted.count,
      coordinates.sentence.openZero.substituted.boundarySize,
    coordinates.sentence.openZero.shiftTrace.stateBoundary,
      coordinates.sentence.openZero.shiftTrace.stateCount,
      coordinates.sentence.openZero.shiftTrace.tableWidth,
      coordinates.sentence.openZero.shiftTrace.valueBound,
    coordinates.sentence.openZero.substitutionTrace.stateBoundary,
      coordinates.sentence.openZero.substitutionTrace.stateCount,
      coordinates.sentence.openZero.substitutionTrace.tableWidth,
      coordinates.sentence.openZero.substitutionTrace.valueBound,
    coordinates.sentence.openZero.fixitrTrace.stateBoundary,
      coordinates.sentence.openZero.fixitrTrace.stateCount,
      coordinates.sentence.openZero.fixitrTrace.tableWidth,
      coordinates.sentence.openZero.fixitrTrace.valueBound,
    coordinates.sentence.openSuccessor.shifted.start,
      coordinates.sentence.openSuccessor.shifted.finish,
      coordinates.sentence.openSuccessor.shifted.boundary,
      coordinates.sentence.openSuccessor.shifted.count,
      coordinates.sentence.openSuccessor.shifted.boundarySize,
    coordinates.sentence.openSuccessor.substituted.start,
      coordinates.sentence.openSuccessor.substituted.finish,
      coordinates.sentence.openSuccessor.substituted.boundary,
      coordinates.sentence.openSuccessor.substituted.count,
      coordinates.sentence.openSuccessor.substituted.boundarySize,
    coordinates.sentence.openSuccessor.shiftTrace.stateBoundary,
      coordinates.sentence.openSuccessor.shiftTrace.stateCount,
      coordinates.sentence.openSuccessor.shiftTrace.tableWidth,
      coordinates.sentence.openSuccessor.shiftTrace.valueBound,
    coordinates.sentence.openSuccessor.substitutionTrace.stateBoundary,
      coordinates.sentence.openSuccessor.substitutionTrace.stateCount,
      coordinates.sentence.openSuccessor.substitutionTrace.tableWidth,
      coordinates.sentence.openSuccessor.substitutionTrace.valueBound,
    coordinates.sentence.openSuccessor.fixitrTrace.stateBoundary,
      coordinates.sentence.openSuccessor.fixitrTrace.stateCount,
      coordinates.sentence.openSuccessor.fixitrTrace.tableWidth,
      coordinates.sentence.openSuccessor.fixitrTrace.valueBound,
    coordinates.sentence.step.negatedStepZeroTrace.stateBoundary,
      coordinates.sentence.step.negatedStepZeroTrace.stateCount,
      coordinates.sentence.step.negatedStepZeroTrace.tableWidth,
      coordinates.sentence.step.negatedStepZeroTrace.valueBound,
    coordinates.sentence.step.negatedQuantifiedStepTrace.stateBoundary,
      coordinates.sentence.step.negatedQuantifiedStepTrace.stateCount,
      coordinates.sentence.step.negatedQuantifiedStepTrace.tableWidth,
      coordinates.sentence.step.negatedQuantifiedStepTrace.valueBound,
    depth,
    fvarList.start, fvarList.finish, fvarList.boundary, fvarList.count,
      fvarList.boundarySize,
    depthCapture.start, depthCapture.finish, depthCapture.boundary,
      depthCapture.count, depthCapture.boundarySize,
    fixed.start, fixed.finish, fixed.boundary, fixed.count,
      fixed.boundarySize,
    candidate.start, candidate.finish, candidate.boundary, candidate.count,
      candidate.boundarySize,
    coordinates.fvSup.trace.stateBoundary,
      coordinates.fvSup.trace.stateCount,
      coordinates.fvSup.trace.tableWidth,
      coordinates.fvSup.trace.valueBound,
    coordinates.closure.trace.stateBoundary,
      coordinates.closure.trace.stateCount,
      coordinates.closure.trace.tableWidth,
      coordinates.closure.trace.valueBound]

set_option maxHeartbeats 3200000 in
-- The three complete direct subgraphs need one local normalization budget.
set_option maxRecDepth 4096 in
@[simp] theorem compactGuardedInductionSentenceRouteDef_spec
    (tokenTable width tokenCount depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed candidate :
      CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) :
    compactGuardedInductionSentenceRouteDef.val.Evalb
        (compactGuardedInductionSentenceRouteEnvironment
          tokenTable width tokenCount depth body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed candidate coordinates) ↔
      CompactGuardedInductionSentenceRoute tokenTable width tokenCount depth
        body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
        base negatedBase stepZero stepSuccessor negatedStepZero
        stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
        innerDisjunction sentence fvarList depthCapture fixed candidate
        coordinates := by
  let env := compactGuardedInductionSentenceRouteEnvironment
    tokenTable width tokenCount depth body zeroWitness openZeroWitness
    openSuccessorWitness captureOne empty base negatedBase stepZero
    stepSuccessor negatedStepZero stepDisjunction quantifiedStep
    negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
    fvarList depthCapture fixed candidate coordinates
  change compactGuardedInductionSentenceRouteDef.val.Evalb env ↔ _
  have hsentenceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 177), #1, #2, #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12, #13, #14, #15, #16, #17,
          #18, #19, #20, #21, #22, #23, #24, #25, #26, #27,
          #28, #29, #30, #31, #32, #33, #34, #35, #36, #37,
          #38, #39, #40, #41, #42, #43, #44, #45, #46, #47,
          #48, #49, #50, #51, #52, #53, #54, #55, #56, #57,
          #58, #59, #60, #61, #62, #63, #64, #65, #66, #67,
          #68, #69, #70, #71, #72, #73, #74, #75, #76, #77,
          #78, #79, #80, #81, #82, #83, #84, #85, #86, #87,
          #88, #89, #90, #91, #92, #93, #94, #95, #96, #97,
          #98, #99, #100, #101, #102, #103, #104, #105, #106,
          #107, #108, #109, #110, #111, #112, #113, #114, #115,
          #116, #117, #118, #119, #120, #121, #122, #123, #124,
          #125, #126, #127, #128, #129, #130, #131, #132, #133,
          #134, #135, #136, #137, #138, #139, #140, #141, #142,
          #143, #144, #145, #146, #147]) =
        compactSuccIndSentenceRouteEnvironment tokenTable width tokenCount
          body zeroWitness openZeroWitness openSuccessorWitness captureOne
          empty base negatedBase stepZero stepSuccessor negatedStepZero
          stepDisjunction quantifiedStep negatedQuantifiedStep
          quantifiedFinal innerDisjunction sentence coordinates.sentence := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfvSupEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 177), #1, #2, ‘0’, #148,
          #28, #29, #30, #31, #32,
          #83, #84, #85, #86, #87,
          #149, #150, #151, #152, #153,
          #169, #170, #171, #172]) =
        compactFormulaFvSupTotalEndpointEnvironment
          tokenTable width tokenCount 0 depth empty sentence fvarList
          coordinates.fvSup := by
    funext coordinate
    fin_cases coordinate <;> simp [env,
      compactGuardedInductionSentenceRouteEnvironment,
      compactFormulaFvSupTotalEndpointEnvironment]
  have hclosureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 177), #1, #2, #148,
          #28, #29, #30, #31, #32,
          #154, #155, #156, #157, #158,
          #83, #84, #85, #86, #87,
          #159, #160, #161, #162, #163,
          #164, #165, #166, #167, #168,
          #173, #174, #175, #176]) =
        compactFixedAllClosureTotalEndpointEnvironment
          tokenTable width tokenCount depth empty depthCapture sentence fixed
          candidate coordinates.closure := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hsentenceSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 177), #1, #2, #3, #4, #5, #6, #7,
              #8, #9, #10, #11, #12, #13, #14, #15, #16, #17,
              #18, #19, #20, #21, #22, #23, #24, #25, #26, #27,
              #28, #29, #30, #31, #32, #33, #34, #35, #36, #37,
              #38, #39, #40, #41, #42, #43, #44, #45, #46, #47,
              #48, #49, #50, #51, #52, #53, #54, #55, #56, #57,
              #58, #59, #60, #61, #62, #63, #64, #65, #66, #67,
              #68, #69, #70, #71, #72, #73, #74, #75, #76, #77,
              #78, #79, #80, #81, #82, #83, #84, #85, #86, #87,
              #88, #89, #90, #91, #92, #93, #94, #95, #96, #97,
              #98, #99, #100, #101, #102, #103, #104, #105, #106,
              #107, #108, #109, #110, #111, #112, #113, #114, #115,
              #116, #117, #118, #119, #120, #121, #122, #123, #124,
              #125, #126, #127, #128, #129, #130, #131, #132, #133,
              #134, #135, #136, #137, #138, #139, #140, #141, #142,
              #143, #144, #145, #146, #147])
          Empty.elim) compactSuccIndSentenceRouteDef.val ↔
        CompactSuccIndSentenceRoute tokenTable width tokenCount
          body zeroWitness openZeroWitness openSuccessorWitness captureOne
          empty base negatedBase stepZero stepSuccessor negatedStepZero
          stepDisjunction quantifiedStep negatedQuantifiedStep
          quantifiedFinal innerDisjunction sentence coordinates.sentence := by
    rw [hsentenceEnv]
    exact compactSuccIndSentenceRouteDef_spec tokenTable width tokenCount
      body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero stepDisjunction
      quantifiedStep negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence coordinates.sentence
  have hfvSupSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 177), #1, #2, ‘0’, #148,
              #28, #29, #30, #31, #32,
              #83, #84, #85, #86, #87,
              #149, #150, #151, #152, #153,
              #169, #170, #171, #172])
          Empty.elim) compactFormulaFvSupTotalEndpointDef.val ↔
        CompactFormulaFvSupTotalEndpoint tokenTable width tokenCount 0 depth
          empty sentence fvarList coordinates.fvSup := by
    rw [hfvSupEnv]
    exact compactFormulaFvSupTotalEndpointDef_spec tokenTable width tokenCount
      0 depth empty sentence fvarList coordinates.fvSup
  have hclosureSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 177), #1, #2, #148,
              #28, #29, #30, #31, #32,
              #154, #155, #156, #157, #158,
              #83, #84, #85, #86, #87,
              #159, #160, #161, #162, #163,
              #164, #165, #166, #167, #168,
              #173, #174, #175, #176])
          Empty.elim) compactFixedAllClosureTotalEndpointDef.val ↔
        CompactFixedAllClosureTotalEndpoint tokenTable width tokenCount depth
          empty depthCapture sentence fixed candidate coordinates.closure := by
    rw [hclosureEnv]
    exact compactFixedAllClosureTotalEndpointDef_spec
      tokenTable width tokenCount depth empty depthCapture sentence fixed
      candidate coordinates.closure
  simp [compactGuardedInductionSentenceRouteDef,
    CompactGuardedInductionSentenceRoute,
    hsentenceSpec, hfvSupSpec, hclosureSpec]

theorem compactGuardedInductionSentenceRouteDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactGuardedInductionSentenceRouteDef.val := by
  simp [compactGuardedInductionSentenceRouteDef]

theorem CompactGuardedInductionSentenceRoute.sound_canonical
    {tokenTable width tokenCount depth : Nat}
    {bodySlot zeroWitnessSlot openZeroWitnessSlot openSuccessorWitnessSlot
      captureOneSlot emptySlot baseSlot negatedBaseSlot stepZeroSlot
      stepSuccessorSlot negatedStepZeroSlot stepDisjunctionSlot
      quantifiedStepSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot fvarListSlot depthCaptureSlot
      fixedSlot candidateSlot : CompactNatListRowSlot}
    {coordinates : CompactGuardedInductionSentenceRouteCoordinates}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactGuardedInductionSentenceRoute
      tokenTable width tokenCount depth
      bodySlot zeroWitnessSlot openZeroWitnessSlot openSuccessorWitnessSlot
      captureOneSlot emptySlot baseSlot negatedBaseSlot stepZeroSlot
      stepSuccessorSlot negatedStepZeroSlot stepDisjunctionSlot
      quantifiedStepSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot fvarListSlot depthCaptureSlot
      fixedSlot candidateSlot coordinates)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body)) :
    ∃ candidateTokens : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        candidateSlot.start candidateSlot.finish candidateTokens /\
      candidateTokens = compactArithmeticFormulaTokens
        (Rewriting.emb
          (FoundationCompactPAAxiomCertificate.PAAxiomCertificate.induction
            body).sentence : LO.FirstOrder.ArithmeticProposition) := by
  rcases hroute with ⟨hsentenceRoute, hfvSupEndpoint, hclosureEndpoint⟩
  rcases hsentenceRoute.sound_canonical body hbody with
    ⟨sentenceTokens, hsentenceLayout, hsentenceCanonical⟩
  subst sentenceTokens
  have hdepth := hfvSupEndpoint.sound_canonical (succInd body)
    hsentenceLayout
  rcases hclosureEndpoint.sound_canonical (succInd body) hsentenceLayout with
    ⟨candidateTokens, hcandidateLayout, hcandidateCanonical⟩
  subst depth
  refine ⟨candidateTokens, hcandidateLayout, ?_⟩
  change candidateTokens = compactArithmeticFormulaTokens
    (compactInductionClosureFormula body) at hcandidateCanonical
  rw [compactInductionClosureFormula_eq_sentence] at hcandidateCanonical
  exact hcandidateCanonical

#print axioms CompactGuardedInductionSentenceRoute.sound_canonical
#print axioms compactGuardedInductionSentenceRouteDef_spec
#print axioms compactGuardedInductionSentenceRouteDef_sigmaZero

end FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
