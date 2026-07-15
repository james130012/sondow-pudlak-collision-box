import integration.FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
import integration.FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute

/-!
# Direct checked route for the complete successor-induction sentence

The route joins the fixed base branch, both open substitutions, the quantified
step assembly, and the two outer disjunctions.  Every intermediate formula is
shared through one concrete list slot in one token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSuccIndSentenceRoute

open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTransformationTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectLiteralNatListFormula
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
open FoundationCompactNumericListedDirectSuccIndOuterAssemblyRoute

structure CompactSuccIndSentenceRouteCoordinates where
  base : CompactSuccIndBaseNegationRouteCoordinates
  openZero : CompactSuccIndOpenSubstitutionRouteCoordinates
  openSuccessor : CompactSuccIndOpenSubstitutionRouteCoordinates
  step : CompactSuccIndStepAssemblyRouteCoordinates

def CompactSuccIndSentenceRoute
    (tokenTable width tokenCount : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness capture empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence : CompactNatListRowSlot)
    (coordinates : CompactSuccIndSentenceRouteCoordinates) : Prop :=
  CompactSuccIndBaseNegationRoute tokenTable width tokenCount
      body zeroWitness base negatedBase empty coordinates.base /\
    CompactAdditiveLiteralNatListRows tokenTable width tokenCount
      openZeroWitness.start openZeroWitness.count
      compactSuccIndOpenZeroWitnessTokens /\
    CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
      body openZeroWitness capture stepZero empty coordinates.openZero /\
    CompactAdditiveLiteralNatListRows tokenTable width tokenCount
      openSuccessorWitness.start openSuccessorWitness.count
      compactSuccIndOpenSuccessorWitnessTokens /\
    CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
      body openSuccessorWitness capture stepSuccessor empty
      coordinates.openSuccessor /\
    CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
      stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal empty coordinates.step /\
    CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
      negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence

def compactSuccIndSentenceRouteDef : 𝚺₀.Semisentence 148 := .mkSigma
  “tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      zeroWitnessStart zeroWitnessFinish zeroWitnessBoundary zeroWitnessCount
        zeroWitnessBoundarySize
      openZeroWitnessStart openZeroWitnessFinish openZeroWitnessBoundary
        openZeroWitnessCount openZeroWitnessBoundarySize
      openSuccessorWitnessStart openSuccessorWitnessFinish
        openSuccessorWitnessBoundary openSuccessorWitnessCount
        openSuccessorWitnessBoundarySize
      captureStart captureFinish captureBoundary captureCount
        captureBoundarySize
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
        quantifiedStepNegationTableWidth quantifiedStepNegationValueBound.
    !(compactSuccIndBaseNegationRouteDef)
      tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      zeroWitnessStart zeroWitnessFinish zeroWitnessBoundary zeroWitnessCount
        zeroWitnessBoundarySize
      baseStart baseFinish baseBoundary baseCount baseBoundarySize
      negatedBaseStart negatedBaseFinish negatedBaseBoundary negatedBaseCount
        negatedBaseBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      baseStateBoundary baseStateCount baseTableWidth baseValueBound
      baseNegationStateBoundary baseNegationStateCount baseNegationTableWidth
        baseNegationValueBound ∧
    !((compactAdditiveLiteralNatListRowsDef
        compactSuccIndOpenZeroWitnessTokens))
      tokenTable width tokenCount openZeroWitnessStart openZeroWitnessCount ∧
    !(compactSuccIndOpenSubstitutionRouteDef)
      tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      openZeroWitnessStart openZeroWitnessFinish openZeroWitnessBoundary
        openZeroWitnessCount openZeroWitnessBoundarySize
      captureStart captureFinish captureBoundary captureCount
        captureBoundarySize
      stepZeroStart stepZeroFinish stepZeroBoundary stepZeroCount
        stepZeroBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
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
        openZeroFixitrTableWidth openZeroFixitrValueBound ∧
    !((compactAdditiveLiteralNatListRowsDef
        compactSuccIndOpenSuccessorWitnessTokens))
      tokenTable width tokenCount openSuccessorWitnessStart
        openSuccessorWitnessCount ∧
    !(compactSuccIndOpenSubstitutionRouteDef)
      tokenTable width tokenCount
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize
      openSuccessorWitnessStart openSuccessorWitnessFinish
        openSuccessorWitnessBoundary openSuccessorWitnessCount
        openSuccessorWitnessBoundarySize
      captureStart captureFinish captureBoundary captureCount
        captureBoundarySize
      stepSuccessorStart stepSuccessorFinish stepSuccessorBoundary
        stepSuccessorCount stepSuccessorBoundarySize
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
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
        openSuccessorFixitrTableWidth openSuccessorFixitrValueBound ∧
    !(compactSuccIndStepAssemblyRouteDef)
      tokenTable width tokenCount
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
      emptyStart emptyFinish emptyBoundary emptyCount emptyBoundarySize
      stepNegationStateBoundary stepNegationStateCount stepNegationTableWidth
        stepNegationValueBound
      quantifiedStepNegationStateBoundary quantifiedStepNegationStateCount
        quantifiedStepNegationTableWidth quantifiedStepNegationValueBound ∧
    !(compactSuccIndOuterAssemblyRouteDef)
      tokenTable width tokenCount
      negatedBaseStart negatedBaseFinish negatedBaseBoundary negatedBaseCount
        negatedBaseBoundarySize
      negatedQuantifiedStepStart negatedQuantifiedStepFinish
        negatedQuantifiedStepBoundary negatedQuantifiedStepCount
        negatedQuantifiedStepBoundarySize
      quantifiedFinalStart quantifiedFinalFinish quantifiedFinalBoundary
        quantifiedFinalCount quantifiedFinalBoundarySize
      innerStart innerFinish innerBoundary innerCount innerBoundarySize
      sentenceStart sentenceFinish sentenceBoundary sentenceCount
        sentenceBoundarySize”

def compactSuccIndSentenceRouteEnvironment
    (tokenTable width tokenCount : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness capture empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence : CompactNatListRowSlot)
    (coordinates : CompactSuccIndSentenceRouteCoordinates) : Fin 148 -> Nat :=
  ![tokenTable, width, tokenCount,
    body.start, body.finish, body.boundary, body.count, body.boundarySize,
    zeroWitness.start, zeroWitness.finish, zeroWitness.boundary,
      zeroWitness.count, zeroWitness.boundarySize,
    openZeroWitness.start, openZeroWitness.finish, openZeroWitness.boundary,
      openZeroWitness.count, openZeroWitness.boundarySize,
    openSuccessorWitness.start, openSuccessorWitness.finish,
      openSuccessorWitness.boundary, openSuccessorWitness.count,
      openSuccessorWitness.boundarySize,
    capture.start, capture.finish, capture.boundary, capture.count,
      capture.boundarySize,
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
    coordinates.base.baseTrace.stateBoundary,
      coordinates.base.baseTrace.stateCount,
      coordinates.base.baseTrace.tableWidth,
      coordinates.base.baseTrace.valueBound,
    coordinates.base.negationTrace.stateBoundary,
      coordinates.base.negationTrace.stateCount,
      coordinates.base.negationTrace.tableWidth,
      coordinates.base.negationTrace.valueBound,
    coordinates.openZero.shifted.start,
      coordinates.openZero.shifted.finish,
      coordinates.openZero.shifted.boundary,
      coordinates.openZero.shifted.count,
      coordinates.openZero.shifted.boundarySize,
    coordinates.openZero.substituted.start,
      coordinates.openZero.substituted.finish,
      coordinates.openZero.substituted.boundary,
      coordinates.openZero.substituted.count,
      coordinates.openZero.substituted.boundarySize,
    coordinates.openZero.shiftTrace.stateBoundary,
      coordinates.openZero.shiftTrace.stateCount,
      coordinates.openZero.shiftTrace.tableWidth,
      coordinates.openZero.shiftTrace.valueBound,
    coordinates.openZero.substitutionTrace.stateBoundary,
      coordinates.openZero.substitutionTrace.stateCount,
      coordinates.openZero.substitutionTrace.tableWidth,
      coordinates.openZero.substitutionTrace.valueBound,
    coordinates.openZero.fixitrTrace.stateBoundary,
      coordinates.openZero.fixitrTrace.stateCount,
      coordinates.openZero.fixitrTrace.tableWidth,
      coordinates.openZero.fixitrTrace.valueBound,
    coordinates.openSuccessor.shifted.start,
      coordinates.openSuccessor.shifted.finish,
      coordinates.openSuccessor.shifted.boundary,
      coordinates.openSuccessor.shifted.count,
      coordinates.openSuccessor.shifted.boundarySize,
    coordinates.openSuccessor.substituted.start,
      coordinates.openSuccessor.substituted.finish,
      coordinates.openSuccessor.substituted.boundary,
      coordinates.openSuccessor.substituted.count,
      coordinates.openSuccessor.substituted.boundarySize,
    coordinates.openSuccessor.shiftTrace.stateBoundary,
      coordinates.openSuccessor.shiftTrace.stateCount,
      coordinates.openSuccessor.shiftTrace.tableWidth,
      coordinates.openSuccessor.shiftTrace.valueBound,
    coordinates.openSuccessor.substitutionTrace.stateBoundary,
      coordinates.openSuccessor.substitutionTrace.stateCount,
      coordinates.openSuccessor.substitutionTrace.tableWidth,
      coordinates.openSuccessor.substitutionTrace.valueBound,
    coordinates.openSuccessor.fixitrTrace.stateBoundary,
      coordinates.openSuccessor.fixitrTrace.stateCount,
      coordinates.openSuccessor.fixitrTrace.tableWidth,
      coordinates.openSuccessor.fixitrTrace.valueBound,
    coordinates.step.negatedStepZeroTrace.stateBoundary,
      coordinates.step.negatedStepZeroTrace.stateCount,
      coordinates.step.negatedStepZeroTrace.tableWidth,
      coordinates.step.negatedStepZeroTrace.valueBound,
    coordinates.step.negatedQuantifiedStepTrace.stateBoundary,
      coordinates.step.negatedQuantifiedStepTrace.stateCount,
    coordinates.step.negatedQuantifiedStepTrace.tableWidth,
      coordinates.step.negatedQuantifiedStepTrace.valueBound]

set_option maxHeartbeats 2400000 in
-- Five large route formulas and two literal witnesses need local normalization.
set_option maxRecDepth 4096 in
@[simp] theorem compactSuccIndSentenceRouteDef_spec
    (tokenTable width tokenCount : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness capture empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence : CompactNatListRowSlot)
    (coordinates : CompactSuccIndSentenceRouteCoordinates) :
    compactSuccIndSentenceRouteDef.val.Evalb
        (compactSuccIndSentenceRouteEnvironment tokenTable width tokenCount
          body zeroWitness openZeroWitness openSuccessorWitness capture empty
          base negatedBase stepZero stepSuccessor negatedStepZero
          stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
          innerDisjunction sentence coordinates) ↔
      CompactSuccIndSentenceRoute tokenTable width tokenCount
        body zeroWitness openZeroWitness openSuccessorWitness capture empty
        base negatedBase stepZero stepSuccessor negatedStepZero
        stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
        innerDisjunction sentence coordinates := by
  let env := compactSuccIndSentenceRouteEnvironment tokenTable width tokenCount
    body zeroWitness openZeroWitness openSuccessorWitness capture empty
    base negatedBase stepZero stepSuccessor negatedStepZero
    stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
    innerDisjunction sentence coordinates
  change compactSuccIndSentenceRouteDef.val.Evalb env ↔ _
  have hbaseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
          #3, #4, #5, #6, #7,
          #8, #9, #10, #11, #12,
          #33, #34, #35, #36, #37,
          #38, #39, #40, #41, #42,
          #28, #29, #30, #31, #32,
          #88, #89, #90, #91, #92, #93, #94, #95]) =
        compactSuccIndBaseNegationRouteEnvironment tokenTable width tokenCount
          body zeroWitness base negatedBase empty coordinates.base := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hopenZeroLiteralEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2, #13, #16]) =
        ![tokenTable, width, tokenCount,
          openZeroWitness.start, openZeroWitness.count] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hopenZeroEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
          #3, #4, #5, #6, #7,
          #13, #14, #15, #16, #17,
          #23, #24, #25, #26, #27,
          #43, #44, #45, #46, #47,
          #28, #29, #30, #31, #32,
          #96, #97, #98, #99, #100,
          #101, #102, #103, #104, #105,
          #106, #107, #108, #109,
          #110, #111, #112, #113,
          #114, #115, #116, #117]) =
        compactSuccIndOpenSubstitutionRouteEnvironment
          tokenTable width tokenCount body openZeroWitness capture stepZero
          empty coordinates.openZero := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hopenSuccessorLiteralEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2, #18, #21]) =
        ![tokenTable, width, tokenCount,
          openSuccessorWitness.start, openSuccessorWitness.count] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hopenSuccessorEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
          #3, #4, #5, #6, #7,
          #18, #19, #20, #21, #22,
          #23, #24, #25, #26, #27,
          #48, #49, #50, #51, #52,
          #28, #29, #30, #31, #32,
          #118, #119, #120, #121, #122,
          #123, #124, #125, #126, #127,
          #128, #129, #130, #131,
          #132, #133, #134, #135,
          #136, #137, #138, #139]) =
        compactSuccIndOpenSubstitutionRouteEnvironment
          tokenTable width tokenCount body openSuccessorWitness capture
          stepSuccessor empty coordinates.openSuccessor := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstepEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
          #43, #44, #45, #46, #47,
          #48, #49, #50, #51, #52,
          #53, #54, #55, #56, #57,
          #58, #59, #60, #61, #62,
          #63, #64, #65, #66, #67,
          #68, #69, #70, #71, #72,
          #73, #74, #75, #76, #77,
          #28, #29, #30, #31, #32,
          #140, #141, #142, #143,
          #144, #145, #146, #147]) =
        compactSuccIndStepAssemblyRouteEnvironment tokenTable width tokenCount
          stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal empty coordinates.step := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have houterEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
          #38, #39, #40, #41, #42,
          #68, #69, #70, #71, #72,
          #73, #74, #75, #76, #77,
          #78, #79, #80, #81, #82,
          #83, #84, #85, #86, #87]) =
        compactSuccIndOuterAssemblyRouteEnvironment tokenTable width tokenCount
          negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
          sentence := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbaseSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
              #3, #4, #5, #6, #7,
              #8, #9, #10, #11, #12,
              #33, #34, #35, #36, #37,
              #38, #39, #40, #41, #42,
              #28, #29, #30, #31, #32,
              #88, #89, #90, #91, #92, #93, #94, #95])
          Empty.elim) compactSuccIndBaseNegationRouteDef.val ↔
        CompactSuccIndBaseNegationRoute tokenTable width tokenCount
          body zeroWitness base negatedBase empty coordinates.base := by
    rw [hbaseEnv]
    exact compactSuccIndBaseNegationRouteDef_spec
      tokenTable width tokenCount body zeroWitness base negatedBase empty
      coordinates.base
  have hopenZeroLiteralSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2, #13, #16])
          Empty.elim)
          (compactAdditiveLiteralNatListRowsDef
            (compactArithmeticTermTokens succIndOpenZeroWitness)).val ↔
        CompactAdditiveLiteralNatListRows tokenTable width tokenCount
          openZeroWitness.start openZeroWitness.count
            (compactArithmeticTermTokens succIndOpenZeroWitness) := by
    rw [hopenZeroLiteralEnv]
    exact compactAdditiveLiteralNatListRowsDef_spec
      (compactArithmeticTermTokens succIndOpenZeroWitness)
      tokenTable width tokenCount openZeroWitness.start
      openZeroWitness.count
  have hopenZeroSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
              #3, #4, #5, #6, #7,
              #13, #14, #15, #16, #17,
              #23, #24, #25, #26, #27,
              #43, #44, #45, #46, #47,
              #28, #29, #30, #31, #32,
              #96, #97, #98, #99, #100,
              #101, #102, #103, #104, #105,
              #106, #107, #108, #109,
              #110, #111, #112, #113,
              #114, #115, #116, #117])
          Empty.elim) compactSuccIndOpenSubstitutionRouteDef.val ↔
        CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
          body openZeroWitness capture stepZero empty
          coordinates.openZero := by
    rw [hopenZeroEnv]
    exact compactSuccIndOpenSubstitutionRouteDef_spec
      tokenTable width tokenCount body openZeroWitness capture stepZero empty
      coordinates.openZero
  have hopenSuccessorLiteralSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2, #18, #21])
          Empty.elim)
          (compactAdditiveLiteralNatListRowsDef
            (compactArithmeticTermTokens succIndOpenSuccessorWitness)).val ↔
        CompactAdditiveLiteralNatListRows tokenTable width tokenCount
          openSuccessorWitness.start openSuccessorWitness.count
            (compactArithmeticTermTokens succIndOpenSuccessorWitness) := by
    rw [hopenSuccessorLiteralEnv]
    exact compactAdditiveLiteralNatListRowsDef_spec
      (compactArithmeticTermTokens succIndOpenSuccessorWitness)
      tokenTable width tokenCount openSuccessorWitness.start
      openSuccessorWitness.count
  have hopenSuccessorSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
              #3, #4, #5, #6, #7,
              #18, #19, #20, #21, #22,
              #23, #24, #25, #26, #27,
              #48, #49, #50, #51, #52,
              #28, #29, #30, #31, #32,
              #118, #119, #120, #121, #122,
              #123, #124, #125, #126, #127,
              #128, #129, #130, #131,
              #132, #133, #134, #135,
              #136, #137, #138, #139])
          Empty.elim) compactSuccIndOpenSubstitutionRouteDef.val ↔
        CompactSuccIndOpenSubstitutionRoute tokenTable width tokenCount
          body openSuccessorWitness capture stepSuccessor empty
          coordinates.openSuccessor := by
    rw [hopenSuccessorEnv]
    exact compactSuccIndOpenSubstitutionRouteDef_spec
      tokenTable width tokenCount body openSuccessorWitness capture
      stepSuccessor empty coordinates.openSuccessor
  have hstepSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
              #43, #44, #45, #46, #47,
              #48, #49, #50, #51, #52,
              #53, #54, #55, #56, #57,
              #58, #59, #60, #61, #62,
              #63, #64, #65, #66, #67,
              #68, #69, #70, #71, #72,
              #73, #74, #75, #76, #77,
              #28, #29, #30, #31, #32,
              #140, #141, #142, #143,
              #144, #145, #146, #147])
          Empty.elim) compactSuccIndStepAssemblyRouteDef.val ↔
        CompactSuccIndStepAssemblyRoute tokenTable width tokenCount
          stepZero stepSuccessor negatedStepZero stepDisjunction
          quantifiedStep negatedQuantifiedStep quantifiedFinal empty
          coordinates.step := by
    rw [hstepEnv]
    exact compactSuccIndStepAssemblyRouteDef_spec
      tokenTable width tokenCount stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      empty coordinates.step
  have houterSpec :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 148), #1, #2,
              #38, #39, #40, #41, #42,
              #68, #69, #70, #71, #72,
              #73, #74, #75, #76, #77,
              #78, #79, #80, #81, #82,
              #83, #84, #85, #86, #87])
          Empty.elim) compactSuccIndOuterAssemblyRouteDef.val ↔
        CompactSuccIndOuterAssemblyRoute tokenTable width tokenCount
          negatedBase negatedQuantifiedStep quantifiedFinal innerDisjunction
          sentence := by
    rw [houterEnv]
    exact compactSuccIndOuterAssemblyRouteDef_spec
      tokenTable width tokenCount negatedBase negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence
  simp [compactSuccIndSentenceRouteDef, CompactSuccIndSentenceRoute,
    hbaseSpec, hopenZeroLiteralSpec, hopenZeroSpec,
    hopenSuccessorLiteralSpec, hopenSuccessorSpec, hstepSpec, houterSpec]

theorem compactSuccIndSentenceRouteDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSuccIndSentenceRouteDef.val := by
  simp [compactSuccIndSentenceRouteDef]

theorem CompactSuccIndSentenceRoute.sound_canonical
    {tokenTable width tokenCount : Nat}
    {bodySlot zeroWitnessSlot openZeroWitnessSlot openSuccessorWitnessSlot
      captureSlot emptySlot baseSlot negatedBaseSlot stepZeroSlot
      stepSuccessorSlot negatedStepZeroSlot stepDisjunctionSlot
      quantifiedStepSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot : CompactNatListRowSlot}
    {coordinates : CompactSuccIndSentenceRouteCoordinates}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (hroute : CompactSuccIndSentenceRoute tokenTable width tokenCount
      bodySlot zeroWitnessSlot openZeroWitnessSlot openSuccessorWitnessSlot
      captureSlot emptySlot baseSlot negatedBaseSlot stepZeroSlot
      stepSuccessorSlot negatedStepZeroSlot stepDisjunctionSlot
      quantifiedStepSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot coordinates)
    (hbody : CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      bodySlot.start bodySlot.finish (compactArithmeticFormulaTokens body)) :
    ∃ sentenceTokens : List Nat,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        sentenceSlot.start sentenceSlot.finish sentenceTokens /\
      sentenceTokens = compactArithmeticFormulaTokens (succInd body) := by
  rcases hroute with
    ⟨hbaseRoute, hopenZeroLiteral, hopenZeroRoute,
      hopenSuccessorLiteral, hopenSuccessorRoute, hstepRoute, houterRoute⟩
  rcases hbaseRoute.2.2.2.2.2.1.realize with
    ⟨negatedBaseTokens, _hnegatedBaseCount,
      hnegatedBaseLayout, _hnegatedBaseRows⟩
  have hnegatedBaseCanonical := hbaseRoute.sound_canonical
    body hbody hnegatedBaseLayout
  subst negatedBaseTokens
  rcases hopenZeroRoute with
    ⟨hopenZeroEmptyCount, hopenZeroCaptureCount,
      hopenZeroShiftEndpoint, hopenZeroSubstitutionEndpoint,
      hopenZeroFixitrEndpoint⟩
  rcases hopenZeroSubstitutionEndpoint.1.realize with
    ⟨openZeroWitnessTokens, hopenZeroWitnessCount,
      hopenZeroWitnessLayout, _hopenZeroWitnessRows⟩
  have hopenZeroWitnessCountValue : openZeroWitnessSlot.count =
      openZeroWitnessTokens.length := hopenZeroWitnessCount.symm
  have hopenZeroWitnessCanonical : openZeroWitnessTokens =
      compactSuccIndOpenZeroWitnessTokens :=
    (compactAdditiveLiteralNatListRows_iff_eq
      hopenZeroWitnessLayout hopenZeroWitnessCountValue).mp
        hopenZeroLiteral
  subst openZeroWitnessTokens
  rcases hopenZeroFixitrEndpoint.2.2.1.realize with
    ⟨stepZeroTokens, _hstepZeroCount,
      hstepZeroLayout, _hstepZeroRows⟩
  have hopenZeroRoute' : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokenCount bodySlot openZeroWitnessSlot captureSlot
        stepZeroSlot emptySlot coordinates.openZero :=
    ⟨hopenZeroEmptyCount, hopenZeroCaptureCount,
      hopenZeroShiftEndpoint, hopenZeroSubstitutionEndpoint,
      hopenZeroFixitrEndpoint⟩
  have hstepZeroCanonical := hopenZeroRoute'.sound_openZero
    body hbody hopenZeroWitnessLayout hstepZeroLayout
  subst stepZeroTokens
  rcases hopenSuccessorRoute with
    ⟨hopenSuccessorEmptyCount, hopenSuccessorCaptureCount,
      hopenSuccessorShiftEndpoint, hopenSuccessorSubstitutionEndpoint,
      hopenSuccessorFixitrEndpoint⟩
  rcases hopenSuccessorSubstitutionEndpoint.1.realize with
    ⟨openSuccessorWitnessTokens, hopenSuccessorWitnessCount,
      hopenSuccessorWitnessLayout, _hopenSuccessorWitnessRows⟩
  have hopenSuccessorWitnessCountValue : openSuccessorWitnessSlot.count =
      openSuccessorWitnessTokens.length := hopenSuccessorWitnessCount.symm
  have hopenSuccessorWitnessCanonical : openSuccessorWitnessTokens =
      compactSuccIndOpenSuccessorWitnessTokens :=
    (compactAdditiveLiteralNatListRows_iff_eq
      hopenSuccessorWitnessLayout hopenSuccessorWitnessCountValue).mp
        hopenSuccessorLiteral
  subst openSuccessorWitnessTokens
  rcases hopenSuccessorFixitrEndpoint.2.2.1.realize with
    ⟨stepSuccessorTokens, _hstepSuccessorCount,
      hstepSuccessorLayout, _hstepSuccessorRows⟩
  have hopenSuccessorRoute' : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokenCount bodySlot openSuccessorWitnessSlot captureSlot
        stepSuccessorSlot emptySlot coordinates.openSuccessor :=
    ⟨hopenSuccessorEmptyCount, hopenSuccessorCaptureCount,
      hopenSuccessorShiftEndpoint, hopenSuccessorSubstitutionEndpoint,
      hopenSuccessorFixitrEndpoint⟩
  have hstepSuccessorCanonical :=
    hopenSuccessorRoute'.sound_openSuccessor body hbody
      hopenSuccessorWitnessLayout hstepSuccessorLayout
  subst stepSuccessorTokens
  rcases hstepRoute.sound_canonical body hstepZeroLayout
      hstepSuccessorLayout with
    ⟨negatedQuantifiedStepTokens, quantifiedFinalTokens,
      hnegatedQuantifiedStepLayout, hquantifiedFinalLayout,
      hnegatedQuantifiedStepCanonical, hquantifiedFinalCanonical⟩
  subst negatedQuantifiedStepTokens
  subst quantifiedFinalTokens
  exact houterRoute.sound_canonical body hnegatedBaseLayout
    hnegatedQuantifiedStepLayout hquantifiedFinalLayout

#print axioms CompactSuccIndSentenceRoute.sound_canonical
#print axioms compactSuccIndSentenceRouteDef_spec
#print axioms compactSuccIndSentenceRouteDef_sigmaZero

end FoundationCompactNumericListedDirectSuccIndSentenceRoute
