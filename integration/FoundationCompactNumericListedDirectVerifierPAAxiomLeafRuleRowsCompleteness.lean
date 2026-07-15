import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRows
import integration.FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness
import integration.FoundationCompactNumericListedDirectPackedRouteTable

/-!
# Canonical completeness for unified PA-axiom verifier leaves

The fixed and induction certificate branches expose one canonical fixed-width
table containing the ambient sequent, certificate tokens, and candidate tokens.
The induction branch uses the public guarded-induction chunk construction.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRowsCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
open FoundationCompactNumericListedDirectSuccIndSentenceRoute
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRows

def compactFixedPAAxiomLeafRuleRowsCanonicalChunks
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) : List (List Nat) :=
  [compactAdditiveEncode Gamma,
    compactAdditiveEncode (compactPAAxiomCertificateTokens certificate),
    compactAdditiveEncode (compactSentenceTokens candidate)]

def compactPAAxiomLeafRuleRowsCanonicalChunks
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) : List (List Nat) :=
  match certificate with
  | .induction body => compactInductionPAAxiomRuleCheckChunks
      (compactArithmeticFormulaTokens body)
      (compactSentenceTokens candidate) Gamma
  | fixed => compactFixedPAAxiomLeafRuleRowsCanonicalChunks
      Gamma candidate fixed

theorem compactPAAxiomLeafRuleRowsCanonicalChunks_eq_fixed
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    compactPAAxiomLeafRuleRowsCanonicalChunks Gamma candidate certificate =
      compactFixedPAAxiomLeafRuleRowsCanonicalChunks
        Gamma candidate certificate := by
  cases certificate <;>
    simp_all [compactPAAxiomLeafRuleRowsCanonicalChunks,
      FixedPAAxiomCertificate]

def compactPAAxiomLeafInactiveNatListRowSlot : CompactNatListRowSlot where
  start := 0
  finish := 0
  boundary := 0
  count := 0
  boundarySize := 0

def compactPAAxiomLeafInactiveFormulaTransformTraceSlot :
    CompactFormulaTransformTraceSlot where
  stateBoundary := 0
  stateCount := 0
  tableWidth := 0
  valueBound := 0

def compactPAAxiomLeafInactiveRouteCoordinates :
    CompactGuardedInductionSentenceRouteCoordinates where
  sentence :=
    { base :=
        { baseTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot
          negationTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot }
      openZero :=
        { shifted := compactPAAxiomLeafInactiveNatListRowSlot
          substituted := compactPAAxiomLeafInactiveNatListRowSlot
          shiftTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot
          substitutionTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot
          fixitrTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot }
      openSuccessor :=
        { shifted := compactPAAxiomLeafInactiveNatListRowSlot
          substituted := compactPAAxiomLeafInactiveNatListRowSlot
          shiftTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot
          substitutionTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot
          fixitrTrace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot }
      step :=
        { negatedStepZeroTrace :=
            compactPAAxiomLeafInactiveFormulaTransformTraceSlot
          negatedQuantifiedStepTrace :=
            compactPAAxiomLeafInactiveFormulaTransformTraceSlot } }
  fvSup :=
    { trace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot }
  closure :=
    { trace := compactPAAxiomLeafInactiveFormulaTransformTraceSlot }

def CompactCanonicalNumericVerifierPAAxiomLeafRuleRows
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (chunks : List (List Nat))
    (tokenTable width tokenCount gammaStart gammaFinish gammaBoundary
      gammaBoundarySize gammaCount depth : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidateSlot : CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) : Prop :=
  let tokens := chunks.flatten
  let canonicalWidth := (compactBinaryNatPayloadBits tokens).length
  let canonicalTokenTable := compactFixedWidthTableCode canonicalWidth tokens
  tokenTable = canonicalTokenTable /\
    width = canonicalWidth /\
    tokenCount = tokens.length /\
    gammaBoundarySize = Nat.size gammaBoundary /\
    gammaCount = Gamma.length /\
    CompactAdditiveNatListListDirectLayout
      tokenTable width tokenCount gammaStart gammaFinish Gamma /\
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount gammaStart gammaCount gammaFinish
        gammaBoundary /\
    CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma /\
    gammaBoundarySize <= (gammaCount + 1) * tokenCount /\
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount axiomTokens.start axiomTokens.finish
        (compactPAAxiomCertificateTokens certificate) /\
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateSlot.start candidateSlot.finish
        (compactSentenceTokens candidate) /\
    CompactNumericVerifierPAAxiomLeafRuleRows
      tokenTable width tokenCount gammaBoundary gammaCount
      (compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (compactSentenceTokens candidate,
            compactPAAxiomCertificateTokens certificate))))
      depth axiomTokens body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
      fvarList depthCapture fixed generated candidateSlot coordinates 1 1

private theorem exists_compactCanonicalFixedPAAxiomLeafRuleRows
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    let chunks := compactFixedPAAxiomLeafRuleRowsCanonicalChunks
      Gamma candidate certificate
    exists tokenTable width tokenCount gammaStart gammaFinish gammaBoundary
        gammaBoundarySize gammaCount depth,
      exists axiomTokens body zeroWitness openZeroWitness
        openSuccessorWitness captureOne empty base negatedBase stepZero
        stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
        fvarList depthCapture fixed generated candidateSlot :
          CompactNatListRowSlot,
      exists coordinates : CompactGuardedInductionSentenceRouteCoordinates,
        CompactCanonicalNumericVerifierPAAxiomLeafRuleRows
          Gamma candidate certificate chunks tokenTable width tokenCount
          gammaStart gammaFinish gammaBoundary gammaBoundarySize gammaCount
          depth axiomTokens body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed generated candidateSlot coordinates := by
  dsimp only
  let candidateTokens := compactSentenceTokens candidate
  let certificateTokens := compactPAAxiomCertificateTokens certificate
  let chunks := compactFixedPAAxiomLeafRuleRowsCanonicalChunks
    Gamma candidate certificate
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let gammaStart := (compactPackedChunkPrefix chunks 0).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let axiomSlot := compactPackedNatListSlot chunks 1 certificateTokens
  let candidateSlot := compactPackedNatListSlot chunks 2 candidateTokens
  let bodySlot : CompactNatListRowSlot :=
    { start := compactTokenAt 0 certificateTokens
      finish := compactTokenAt 1 certificateTokens
      boundary := compactTokenAt 2 certificateTokens
      count := candidateTokens.length
      boundarySize := 0 }
  let inactive := compactPAAxiomLeafInactiveNatListRowSlot
  let coordinates := compactPAAxiomLeafInactiveRouteCoordinates
  have hGammaLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length gammaStart gammaFinish Gamma := by
    simpa [tokenTable, width, tokens, gammaStart, gammaFinish] using
      compactPackedNatListListLayout_canonical chunks 0 Gamma
        (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
        (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
  rcases hGammaLayout with
    ⟨gammaBoundary, hGammaStructure, hGammaRows, hGammaSize⟩
  have hGammaLayout' : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hGammaStructure, hGammaRows, hGammaSize⟩
  have hAxiomSlot := compactPackedNatListSlot_canonical
    chunks 1 certificateTokens
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
      certificateTokens])
  have hCandidateSlot := compactPackedNatListSlot_canonical
    chunks 2 candidateTokens
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
      candidateTokens])
  dsimp only at hAxiomSlot hCandidateSlot
  have hfixedRule : CompactAdditiveFixedPAAxiomRuleCheck
      tokenTable width tokens.length gammaBoundary Gamma.length
      candidateSlot.start candidateSlot.finish candidateTokens.length
      bodySlot.start bodySlot.finish bodySlot.boundary
      (compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (candidateTokens, certificateTokens)))) := by
    apply (compactAdditiveFixedPAAxiomRuleCheck_canonical_iff
      candidate certificate hfixed hGammaRows hCandidateSlot.layout).2
    rfl
  have hleaf : CompactNumericVerifierPAAxiomLeafRuleRows
      tokenTable width tokens.length gammaBoundary Gamma.length
      (compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (candidateTokens, certificateTokens))))
      0 axiomSlot bodySlot inactive inactive inactive inactive inactive
      inactive inactive inactive inactive inactive
      inactive inactive inactive inactive inactive
      inactive inactive inactive inactive inactive candidateSlot
      coordinates 1 1 := by
    refine ⟨rfl, rfl, Or.inl ?_⟩
    simpa [bodySlot, candidateTokens, certificateTokens] using hfixedRule
  refine ⟨tokenTable, width, tokens.length, gammaStart, gammaFinish,
    gammaBoundary, Nat.size gammaBoundary, Gamma.length, 0,
    axiomSlot, bodySlot, inactive, inactive, inactive, inactive, inactive,
    inactive, inactive, inactive, inactive, inactive,
    inactive, inactive, inactive, inactive, inactive,
    inactive, inactive, inactive, inactive, inactive,
    candidateSlot, coordinates, ?_⟩
  dsimp [CompactCanonicalNumericVerifierPAAxiomLeafRuleRows]
  refine ⟨rfl, rfl, rfl, rfl, rfl, hGammaLayout', hGammaStructure,
    hGammaRows, ?_, hAxiomSlot.layout, hCandidateSlot.layout, ?_⟩
  · simpa using hGammaSize
  · simpa [candidateTokens, certificateTokens] using hleaf

set_option maxHeartbeats 1000000 in
private theorem exists_compactCanonicalInductionPAAxiomLeafRuleRows
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (inductionBody : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    let bodyTokens := compactArithmeticFormulaTokens inductionBody
    let chunks := compactInductionPAAxiomRuleCheckChunks
      bodyTokens (compactSentenceTokens candidate) Gamma
    exists tokenTable width tokenCount gammaStart gammaFinish gammaBoundary
        gammaBoundarySize gammaCount depth,
      exists axiomTokens body zeroWitness openZeroWitness
        openSuccessorWitness captureOne empty base negatedBase stepZero
        stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
        fvarList depthCapture fixed generated candidateSlot :
          CompactNatListRowSlot,
      exists coordinates : CompactGuardedInductionSentenceRouteCoordinates,
        CompactCanonicalNumericVerifierPAAxiomLeafRuleRows
          Gamma candidate (.induction inductionBody) chunks tokenTable width
          tokenCount gammaStart gammaFinish gammaBoundary gammaBoundarySize
          gammaCount depth axiomTokens body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed generated candidateSlot coordinates := by
  dsimp only
  let bodyTokens := compactArithmeticFormulaTokens inductionBody
  let candidateTokens := compactSentenceTokens candidate
  let certificateTokens := 22 :: bodyTokens
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactInductionPAAxiomRuleCheckChunks
    bodyTokens candidateTokens Gamma
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let resultBoolValue := compactAdditiveBoolTag
    (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
  let gammaStart := (compactPackedChunkPrefix chunks 39).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let axiomSlot := compactPackedNatListSlot chunks 37 certificateTokens
  let bodySlot := compactPackedNatListSlot chunks 0 data.body
  let zeroWitnessSlot := compactPackedNatListSlot chunks 1 data.zeroWitness
  let openZeroWitnessSlot :=
    compactPackedNatListSlot chunks 2 data.openZeroWitness
  let openSuccessorWitnessSlot :=
    compactPackedNatListSlot chunks 3 data.openSuccessorWitness
  let captureOneSlot := compactPackedNatListSlot chunks 4 data.captureOne
  let emptySlot := compactPackedNatListSlot chunks 5 data.empty
  let baseSlot := compactPackedNatListSlot chunks 6 data.base
  let negatedBaseSlot := compactPackedNatListSlot chunks 7 data.negatedBase
  let stepZeroSlot := compactPackedNatListSlot chunks 10 data.stepZero
  let stepSuccessorSlot :=
    compactPackedNatListSlot chunks 13 data.stepSuccessor
  let negatedStepZeroSlot :=
    compactPackedNatListSlot chunks 14 data.negatedStepZero
  let stepDisjunctionSlot :=
    compactPackedNatListSlot chunks 15 data.stepDisjunction
  let quantifiedStepSlot :=
    compactPackedNatListSlot chunks 16 data.quantifiedStep
  let negatedQuantifiedStepSlot :=
    compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep
  let quantifiedFinalSlot :=
    compactPackedNatListSlot chunks 18 data.quantifiedFinal
  let innerDisjunctionSlot :=
    compactPackedNatListSlot chunks 19 data.innerDisjunction
  let sentenceSlot := compactPackedNatListSlot chunks 20 data.sentence
  let fvarListSlot := compactPackedNatListSlot chunks 21 data.fvarList
  let depthCaptureSlot :=
    compactPackedNatListSlot chunks 22 data.depthCapture
  let fixedSlot := compactPackedNatListSlot chunks 23 data.fixed
  let generatedSlot := compactPackedNatListSlot chunks 24 data.generated
  let candidateSlot := compactPackedNatListSlot chunks 38 candidateTokens
  have hchunksLength : chunks.length = 40 := by
    simp [chunks]
  have hGammaLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length gammaStart gammaFinish Gamma := by
    simpa [tokenTable, width, tokens, gammaStart, gammaFinish] using
      compactPackedNatListListLayout_canonical chunks 39 Gamma
        (by
          omega)
        (by
          rw [← List.getI_eq_getElem chunks (by omega)]
          simp [chunks])
  rcases hGammaLayout with
    ⟨gammaBoundary, hGammaStructure, hGammaRows, hGammaSize⟩
  have hGammaLayout' : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hGammaStructure, hGammaRows, hGammaSize⟩
  have slotCanonical (index : Nat) (values : List Nat)
      (hindex : index < chunks.length)
      (hchunk : chunks[index] = compactAdditiveEncode values) :
      CompactPackedNatListSlotCanonical tokenTable width tokens.length
        (compactPackedNatListSlot chunks index values) values := by
    simpa [tokenTable, width, tokens] using
      compactPackedNatListSlot_canonical chunks index values hindex hchunk
  have hbodySlot : CompactPackedNatListSlotCanonical
      tokenTable width tokens.length bodySlot bodyTokens := by
    apply slotCanonical 0 bodyTokens (by omega)
    rw [show chunks[0] = chunks.getI 0 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks]
  have haxiomSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokens.length axiomSlot certificateTokens := by
    apply slotCanonical 37 certificateTokens (by omega)
    rw [show chunks[37] = chunks.getI 37 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, certificateTokens]
  have hcandidateSlot : CompactPackedNatListSlotCanonical
      tokenTable width tokens.length candidateSlot candidateTokens := by
    apply slotCanonical 38 candidateTokens (by omega)
    rw [show chunks[38] = chunks.getI 38 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks]
  rcases exists_compactCanonicalInductionPAAxiomRuleCheck
      inductionBody candidate Gamma with
    ⟨canonicalGammaBoundary, coordinates, hcanonicalRule⟩
  have hcanonicalRule' : CompactAdditiveInductionPAAxiomRuleCheck
      tokenTable width tokens.length canonicalGammaBoundary Gamma.length
      resultBoolValue axiomSlot bodySlot zeroWitnessSlot openZeroWitnessSlot
      openSuccessorWitnessSlot captureOneSlot emptySlot baseSlot
      negatedBaseSlot stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot innerDisjunctionSlot sentenceSlot fvarListSlot
      depthCaptureSlot fixedSlot generatedSlot candidateSlot data.depth
      coordinates := by
    simpa [CompactCanonicalInductionPAAxiomRuleCheck, bodyTokens,
      candidateTokens, certificateTokens, data, chunks, tokens, width,
      tokenTable, resultBoolValue, axiomSlot, bodySlot, zeroWitnessSlot,
      openZeroWitnessSlot, openSuccessorWitnessSlot, captureOneSlot,
      emptySlot, baseSlot, negatedBaseSlot, stepZeroSlot, stepSuccessorSlot,
      negatedStepZeroSlot, stepDisjunctionSlot, quantifiedStepSlot,
      negatedQuantifiedStepSlot, quantifiedFinalSlot, innerDisjunctionSlot,
      sentenceSlot, fvarListSlot, depthCaptureSlot, fixedSlot, generatedSlot,
      candidateSlot] using hcanonicalRule
  have hinductionRule : CompactAdditiveInductionPAAxiomRuleCheck
      tokenTable width tokens.length gammaBoundary Gamma.length
      resultBoolValue axiomSlot bodySlot zeroWitnessSlot openZeroWitnessSlot
      openSuccessorWitnessSlot captureOneSlot emptySlot baseSlot
      negatedBaseSlot stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot innerDisjunctionSlot sentenceSlot fvarListSlot
      depthCaptureSlot fixedSlot generatedSlot candidateSlot data.depth
      coordinates :=
    (compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
      (resultBoolValue := resultBoolValue) inductionBody candidate
      hcanonicalRule'.2.1 hcanonicalRule'.1 hGammaRows hbodySlot.layout
      hcandidateSlot.layout).2 (by
        simp [resultBoolValue, bodyTokens, candidateTokens,
          certificateTokens, compactPAAxiomCertificateTokens])
  have hleaf : CompactNumericVerifierPAAxiomLeafRuleRows
      tokenTable width tokens.length gammaBoundary Gamma.length
      resultBoolValue data.depth axiomSlot bodySlot zeroWitnessSlot
      openZeroWitnessSlot openSuccessorWitnessSlot captureOneSlot emptySlot
      baseSlot negatedBaseSlot stepZeroSlot stepSuccessorSlot
      negatedStepZeroSlot stepDisjunctionSlot quantifiedStepSlot
      negatedQuantifiedStepSlot quantifiedFinalSlot innerDisjunctionSlot
      sentenceSlot fvarListSlot depthCaptureSlot fixedSlot generatedSlot
      candidateSlot coordinates 1 1 :=
    ⟨rfl, rfl, Or.inr hinductionRule⟩
  refine ⟨tokenTable, width, tokens.length, gammaStart, gammaFinish,
    gammaBoundary, Nat.size gammaBoundary, Gamma.length, data.depth,
    axiomSlot, bodySlot, zeroWitnessSlot, openZeroWitnessSlot,
    openSuccessorWitnessSlot, captureOneSlot, emptySlot, baseSlot,
    negatedBaseSlot, stepZeroSlot, stepSuccessorSlot, negatedStepZeroSlot,
    stepDisjunctionSlot, quantifiedStepSlot, negatedQuantifiedStepSlot,
    quantifiedFinalSlot, innerDisjunctionSlot, sentenceSlot, fvarListSlot,
    depthCaptureSlot, fixedSlot, generatedSlot, candidateSlot, coordinates, ?_⟩
  dsimp [CompactCanonicalNumericVerifierPAAxiomLeafRuleRows]
  refine ⟨rfl, rfl, rfl, rfl, rfl, hGammaLayout', hGammaStructure,
    hGammaRows, ?_, haxiomSlot.layout, hcandidateSlot.layout, ?_⟩
  · simpa using hGammaSize
  · simpa [resultBoolValue, bodyTokens, candidateTokens, certificateTokens,
      compactPAAxiomCertificateTokens] using hleaf

set_option maxHeartbeats 1000000 in
theorem CompactNumericVerifierPAAxiomLeafRuleRows.exists_canonical
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    let chunks := compactPAAxiomLeafRuleRowsCanonicalChunks
      Gamma candidate certificate
    exists tokenTable width tokenCount gammaStart gammaFinish gammaBoundary
        gammaBoundarySize gammaCount depth,
      exists axiomTokens body zeroWitness openZeroWitness
        openSuccessorWitness captureOne empty base negatedBase stepZero
        stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
        fvarList depthCapture fixed generated candidateSlot :
          CompactNatListRowSlot,
      exists coordinates : CompactGuardedInductionSentenceRouteCoordinates,
        CompactCanonicalNumericVerifierPAAxiomLeafRuleRows
          Gamma candidate certificate chunks tokenTable width tokenCount
          gammaStart gammaFinish gammaBoundary gammaBoundarySize gammaCount
          depth axiomTokens body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed generated candidateSlot coordinates := by
  rcases fixedPAAxiomCertificate_or_induction certificate with
    hfixed | ⟨inductionBody, rfl⟩
  · rw [compactPAAxiomLeafRuleRowsCanonicalChunks_eq_fixed
      Gamma candidate certificate hfixed]
    exact exists_compactCanonicalFixedPAAxiomLeafRuleRows
      Gamma candidate certificate hfixed
  · simpa [compactPAAxiomLeafRuleRowsCanonicalChunks] using
      exists_compactCanonicalInductionPAAxiomLeafRuleRows
        Gamma candidate inductionBody

#print axioms CompactNumericVerifierPAAxiomLeafRuleRows.exists_canonical

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRowsCompleteness
