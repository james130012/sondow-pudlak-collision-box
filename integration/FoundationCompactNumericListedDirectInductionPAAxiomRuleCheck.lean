import integration.FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
import integration.FoundationCompactNumericListedDirectNatListConsRows
import integration.FoundationCompactNumericListedDirectFormulaMembership
import integration.FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck

/-!
# Direct result graph for the induction PA-axiom rule check

The generated guarded induction sentence is kept separate from the candidate
formula carried by the proof node.  Exact token-slice equality and membership
in the same sequent determine the public Boolean result.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck

open FoundationCompactSyntaxTokenMachine
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaMembership
open FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute

def CompactAdditiveInductionPAAxiomRuleCheckShell
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      axiomBoundary axiomCount bodyBoundary bodyCount
      generatedStart generatedFinish candidateStart candidateFinish : Nat) :
    Prop :=
  CompactAdditiveNatListConsRows tokenTable width tokenCount
      bodyBoundary bodyCount axiomBoundary axiomCount 22 /\
    resultBoolValue <= 1 /\
    (resultBoolValue = 1 ↔
      CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
        generatedStart generatedFinish candidateStart candidateFinish /\
      CompactAdditiveFormulaMemberRows tokenTable width tokenCount
        gammaBoundary gammaCount candidateStart candidateFinish)

def CompactAdditiveInductionPAAxiomRuleCheck
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness captureOne
      empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate : CompactNatListRowSlot)
    (depth : Nat)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) : Prop :=
  CompactGuardedInductionSentenceRoute tokenTable width tokenCount depth
      body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      coordinates /\
    CompactAdditiveInductionPAAxiomRuleCheckShell
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      axiomTokens.boundary axiomTokens.count body.boundary body.count
      generated.start generated.finish candidate.start candidate.finish

def compactAdditiveInductionPAAxiomRuleCheckShellDef :
    𝚺₀.Semisentence 14 := .mkSigma
  “tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      axiomBoundary axiomCount bodyBoundary bodyCount
      generatedStart generatedFinish candidateStart candidateFinish.
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount bodyBoundary bodyCount
        axiomBoundary axiomCount 22 ∧
    resultBoolValue ≤ 1 ∧
    (resultBoolValue = 1 ↔
      !(compactFixedWidthTokenSlicesEqDef)
        tokenTable width tokenCount generatedStart generatedFinish
          candidateStart candidateFinish ∧
      !(compactAdditiveFormulaMemberRowsDef)
        tokenTable width tokenCount gammaBoundary gammaCount
          candidateStart candidateFinish)”

@[simp] theorem compactAdditiveInductionPAAxiomRuleCheckShellDef_spec
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      axiomBoundary axiomCount bodyBoundary bodyCount
      generatedStart generatedFinish candidateStart candidateFinish : Nat) :
    compactAdditiveInductionPAAxiomRuleCheckShellDef.val.Evalb
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          resultBoolValue, axiomBoundary, axiomCount, bodyBoundary, bodyCount,
          generatedStart, generatedFinish, candidateStart, candidateFinish] ↔
      CompactAdditiveInductionPAAxiomRuleCheckShell
        tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
        axiomBoundary axiomCount bodyBoundary bodyCount
        generatedStart generatedFinish candidateStart candidateFinish := by
  let env : Fin 14 -> Nat :=
    ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
      resultBoolValue, axiomBoundary, axiomCount, bodyBoundary, bodyCount,
      generatedStart, generatedFinish, candidateStart, candidateFinish]
  change compactAdditiveInductionPAAxiomRuleCheckShellDef.val.Evalb env ↔ _
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #8, #9, #6, #7, ‘22’]) =
        ![tokenTable, width, tokenCount, bodyBoundary, bodyCount,
          axiomBoundary, axiomCount, 22] := by
    funext coordinate
    fin_cases coordinate <;> simp [env]
  have hslicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2,
          #10, #11, #12, #13]) =
        ![tokenTable, width, tokenCount, generatedStart, generatedFinish,
          candidateStart, candidateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hmemberEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2,
          #3, #4, #12, #13]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          candidateStart, candidateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hresultValue : env 5 = resultBoolValue := rfl
  simp [compactAdditiveInductionPAAxiomRuleCheckShellDef,
    CompactAdditiveInductionPAAxiomRuleCheckShell,
    hconsEnv, hslicesEnv, hmemberEnv, hresultValue]

theorem compactAdditiveInductionPAAxiomRuleCheckShellDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveInductionPAAxiomRuleCheckShellDef.val := by
  simp [compactAdditiveInductionPAAxiomRuleCheckShellDef]

def compactGuardedInductionSentenceRouteLift :
    LO.FirstOrder.ArithmeticSemisentence 184 :=
  compactGuardedInductionSentenceRouteDef.val ⇜
    (fun index : Fin 177 =>
      (#(Fin.castLE (show 177 <= 184 by omega) index) :
        Semiterm ℒₒᵣ Empty 184))

def compactInductionPAAxiomRuleCheckShellLift :
    LO.FirstOrder.ArithmeticSemisentence 184 :=
  compactAdditiveInductionPAAxiomRuleCheckShellDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 184), #1, #2, #177, #178, #179,
      #180, #181, #5, #6, #164, #165, #182, #183]

def compactAdditiveInductionPAAxiomRuleCheckDef :
    𝚺₀.Semisentence 184 := .mkSigma
  (compactGuardedInductionSentenceRouteLift ⋏
    compactInductionPAAxiomRuleCheckShellLift)
  (by
    simp [compactGuardedInductionSentenceRouteLift,
      compactInductionPAAxiomRuleCheckShellLift])

def compactAdditiveInductionPAAxiomRuleCheckEnvironment
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate : CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) :
    Fin 184 -> Nat :=
  Matrix.vecAppend rfl
    (compactGuardedInductionSentenceRouteEnvironment
      tokenTable width tokenCount depth body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
      fvarList depthCapture fixed generated coordinates)
    ![gammaBoundary, gammaCount, resultBoolValue,
      axiomTokens.boundary, axiomTokens.count,
      candidate.start, candidate.finish]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
@[simp] theorem compactAdditiveInductionPAAxiomRuleCheckDef_spec
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate : CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates) :
    compactAdditiveInductionPAAxiomRuleCheckDef.val.Evalb
        (compactAdditiveInductionPAAxiomRuleCheckEnvironment
          tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
          depth axiomTokens body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed generated candidate coordinates) ↔
      CompactAdditiveInductionPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
        axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
        captureOne empty base negatedBase stepZero stepSuccessor
        negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
        quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
        generated candidate depth coordinates := by
  let routeEnv := compactGuardedInductionSentenceRouteEnvironment
    tokenTable width tokenCount depth body zeroWitness openZeroWitness
    openSuccessorWitness captureOne empty base negatedBase stepZero
    stepSuccessor negatedStepZero stepDisjunction quantifiedStep
    negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
    fvarList depthCapture fixed generated coordinates
  let env := compactAdditiveInductionPAAxiomRuleCheckEnvironment
    tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
    depth axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
    captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
    stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
    innerDisjunction sentence fvarList depthCapture fixed generated candidate
    coordinates
  change compactAdditiveInductionPAAxiomRuleCheckDef.val.Evalb env ↔ _
  have hrouteEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 177 =>
          (#(Fin.castLE (show 177 <= 184 by omega) index) :
            Semiterm ℒₒᵣ Empty 184))) = routeEnv := by
    funext coordinate
    simp [env, routeEnv,
      compactAdditiveInductionPAAxiomRuleCheckEnvironment,
      Matrix.vecAppend_eq_ite]
  have hshellEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 184), #1, #2, #177, #178, #179,
          #180, #181, #5, #6, #164, #165, #182, #183]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          resultBoolValue, axiomTokens.boundary, axiomTokens.count,
          body.boundary, body.count, generated.start, generated.finish,
          candidate.start, candidate.finish] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env,
        compactAdditiveInductionPAAxiomRuleCheckEnvironment,
        compactGuardedInductionSentenceRouteEnvironment,
        Matrix.vecAppend_eq_ite]
  have hrouteSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            (fun index : Fin 177 =>
              (#(Fin.castLE (show 177 <= 184 by omega) index) :
                Semiterm ℒₒᵣ Empty 184)))
          Empty.elim compactGuardedInductionSentenceRouteDef.val ↔
        CompactGuardedInductionSentenceRoute tokenTable width tokenCount depth
          body zeroWitness openZeroWitness openSuccessorWitness captureOne
          empty base negatedBase stepZero stepSuccessor negatedStepZero
          stepDisjunction quantifiedStep negatedQuantifiedStep
          quantifiedFinal innerDisjunction sentence fvarList depthCapture
          fixed generated coordinates := by
    rw [hrouteEnv]
    exact compactGuardedInductionSentenceRouteDef_spec
      tokenTable width tokenCount depth body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
      fvarList depthCapture fixed generated coordinates
  have hshellSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 184), #1, #2, #177, #178, #179,
              #180, #181, #5, #6, #164, #165, #182, #183])
          Empty.elim compactAdditiveInductionPAAxiomRuleCheckShellDef.val ↔
        CompactAdditiveInductionPAAxiomRuleCheckShell
          tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
          axiomTokens.boundary axiomTokens.count body.boundary body.count
          generated.start generated.finish candidate.start candidate.finish := by
    rw [hshellEnv]
    exact compactAdditiveInductionPAAxiomRuleCheckShellDef_spec
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      axiomTokens.boundary axiomTokens.count body.boundary body.count
      generated.start generated.finish candidate.start candidate.finish
  simp [compactAdditiveInductionPAAxiomRuleCheckDef,
    compactGuardedInductionSentenceRouteLift,
    compactInductionPAAxiomRuleCheckShellLift,
    CompactAdditiveInductionPAAxiomRuleCheck,
    hrouteSpec, hshellSpec]

theorem compactAdditiveInductionPAAxiomRuleCheckDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveInductionPAAxiomRuleCheckDef.val := by
  exact compactAdditiveInductionPAAxiomRuleCheckDef.sigma_prop

theorem compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
    {tokenTable width tokenCount gammaBoundary resultBoolValue depth : Nat}
    {axiomSlot bodySlot zeroWitnessSlot openZeroWitnessSlot
      openSuccessorWitnessSlot captureOneSlot emptySlot baseSlot
      negatedBaseSlot stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
      stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
      quantifiedFinalSlot innerDisjunctionSlot sentenceSlot fvarListSlot
      depthCaptureSlot fixedSlot generatedSlot candidateSlot :
      CompactNatListRowSlot}
    {coordinates : CompactGuardedInductionSentenceRouteCoordinates}
    {Gamma : List (List Nat)}
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hcons : CompactAdditiveNatListConsRows tokenTable width tokenCount
      bodySlot.boundary bodySlot.count
      axiomSlot.boundary axiomSlot.count 22)
    (hroute : CompactGuardedInductionSentenceRoute
      tokenTable width tokenCount depth
      bodySlot zeroWitnessSlot openZeroWitnessSlot openSuccessorWitnessSlot
      captureOneSlot emptySlot baseSlot negatedBaseSlot stepZeroSlot
      stepSuccessorSlot negatedStepZeroSlot stepDisjunctionSlot
      quantifiedStepSlot negatedQuantifiedStepSlot quantifiedFinalSlot
      innerDisjunctionSlot sentenceSlot fvarListSlot depthCaptureSlot
      fixedSlot generatedSlot coordinates)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hbody : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount bodySlot.start bodySlot.finish
        (compactArithmeticFormulaTokens body))
    (hcandidate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateSlot.start candidateSlot.finish
        (compactSentenceTokens candidate)) :
    CompactAdditiveInductionPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary Gamma.length resultBoolValue
        axiomSlot bodySlot zeroWitnessSlot openZeroWitnessSlot
        openSuccessorWitnessSlot captureOneSlot emptySlot baseSlot
        negatedBaseSlot stepZeroSlot stepSuccessorSlot negatedStepZeroSlot
        stepDisjunctionSlot quantifiedStepSlot negatedQuantifiedStepSlot
        quantifiedFinalSlot innerDisjunctionSlot sentenceSlot fvarListSlot
        depthCaptureSlot fixedSlot generatedSlot candidateSlot depth
        coordinates ↔
      resultBoolValue = compactAdditiveBoolTag
        (compactAxmRuleCheck
          (Gamma, (compactSentenceTokens candidate,
            compactPAAxiomCertificateTokens (.induction body)))) := by
  rcases hroute.sound_canonical body hbody with
    ⟨generatedTokens, hgeneratedLayout, hgeneratedCanonical⟩
  have hgeneratedSentence : generatedTokens =
      compactSentenceTokens
        (FoundationCompactPAAxiomCertificate.PAAxiomCertificate.induction
          body).sentence := by
    simpa [compactSentenceTokens] using hgeneratedCanonical
  have hslices :
      CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
          generatedSlot.start generatedSlot.finish
          candidateSlot.start candidateSlot.finish ↔
        (FoundationCompactPAAxiomCertificate.PAAxiomCertificate.induction
          body).sentence = candidate := by
    constructor
    · intro heq
      have htokens := CompactFixedWidthTokenSlicesEq.natListValues_eq
        heq hgeneratedLayout hcandidate
      rw [hgeneratedSentence] at htokens
      exact (compactSentenceTokens_injective htokens).symm
    · intro hsentence
      apply CompactAdditiveNatListDirectLayout.slicesEq_of_eq
        hgeneratedLayout hcandidate
      rw [hgeneratedSentence]
      exact congrArg compactSentenceTokens hsentence
  have hmember := compactAdditiveFormulaMemberRows_iff_mem
    hGamma hcandidate
  have haxiom : compactPAAxiomSentenceEqTokens
      (compactPAAxiomCertificateTokens (.induction body),
        compactSentenceTokens candidate) = true ↔
      (FoundationCompactPAAxiomCertificate.PAAxiomCertificate.induction
        body).sentence = candidate :=
    compactPAAxiomSentenceEqTokens_canonical (.induction body) candidate
  have hformulaMember := tokenFormulaMem_eq_true_iff
    (compactSentenceTokens candidate) Gamma
  simp only [CompactAdditiveInductionPAAxiomRuleCheck,
    CompactAdditiveInductionPAAxiomRuleCheckShell,
    hcons, hroute, true_and, hslices, hmember]
  cases haxiomValue : compactPAAxiomSentenceEqTokens
      (compactPAAxiomCertificateTokens (.induction body),
        compactSentenceTokens candidate) <;>
    cases hmemberValue : tokenFormulaMem
      (compactSentenceTokens candidate) Gamma <;>
      simp [compactAxmRuleCheck, compactAdditiveBoolTag,
        haxiomValue, hmemberValue] at haxiom hformulaMember ⊢ <;>
      simp [haxiom, hformulaMember] <;> omega

#print axioms compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
#print axioms compactAdditiveInductionPAAxiomRuleCheckShellDef_spec
#print axioms compactAdditiveInductionPAAxiomRuleCheckShellDef_sigmaZero
#print axioms compactAdditiveInductionPAAxiomRuleCheckDef_spec
#print axioms compactAdditiveInductionPAAxiomRuleCheckDef_sigmaZero

end FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
