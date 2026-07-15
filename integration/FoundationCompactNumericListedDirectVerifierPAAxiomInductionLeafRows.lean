import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
import integration.FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Joint induction PA-axiom leaf rows

The structural-certificate endpoint and the 184-coordinate induction rule
share the exact axiom-list boundary and count.  The rule therefore checks
`22 :: body` in the same decoded list that the certificate parser consumed.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomInductionLeafRows

open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectNatListAppendSlices

def compactInductionEndpointAxiomSlot
    (axiomStart axiomFinish : Nat)
    (endpoint : CompactCertificateNodeInductionPAEndpointCoordinates) :
    CompactNatListRowSlot where
  start := axiomStart
  finish := axiomFinish
  boundary := endpoint.axiomBoundary
  count := endpoint.axiomCount
  boundarySize := endpoint.axiomBoundarySize

def CompactNumericVerifierPAAxiomInductionLeafRows
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish proofTag certificateTag
      gammaBoundary gammaCount resultBoolValue depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidate : CompactNatListRowSlot)
    (routeCoordinates : CompactGuardedInductionSentenceRouteCoordinates)
    (endpointCoordinates :
      CompactCertificateNodeInductionPAEndpointCoordinates) : Prop :=
  proofTag = 1 ∧
    CompactCertificateNodeInductionPAEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointCoordinates ∧
    CompactAdditiveInductionPAAxiomRuleCheck
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      (compactInductionEndpointAxiomSlot
        axiomStart axiomFinish endpointCoordinates)
      body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate depth routeCoordinates

def compactPAAxiomInductionRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 215 :=
  compactAdditiveInductionPAAxiomRuleCheckDef.val ⇜
    (fun index : Fin 184 =>
      (#(Fin.castLE (show 184 ≤ 215 by omega) index) :
        Semiterm ℒₒᵣ Empty 215))

def compactPAAxiomInductionEndpointLift :
    LO.FirstOrder.ArithmeticSemisentence 215 :=
  compactCertificateNodeInductionPAEndpointGraphDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 215), #1, #2,
      #184, #185, #186, #187, #188, #189, #190, #191, #193,
      #194, #195, #196, #197, #198, #199, #200, #201,
      #202, #203, #204, #205, #206, #207, #208, #209,
      #210, #211, #212, #213, #214]

def compactNumericVerifierPAAxiomInductionLeafRowsDef :
    𝚺₀.Semisentence 215 := .mkSigma
  (“(#192 = 1)” ⋏
    (compactPAAxiomInductionEndpointLift ⋏
      compactPAAxiomInductionRuleLift))
  (by
    simp [compactPAAxiomInductionEndpointLift,
      compactPAAxiomInductionRuleLift])

def compactNumericVerifierPAAxiomInductionLeafRowsEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish proofTag certificateTag
      gammaBoundary gammaCount resultBoolValue depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidate : CompactNatListRowSlot)
    (routeCoordinates : CompactGuardedInductionSentenceRouteCoordinates)
    (endpointCoordinates :
      CompactCertificateNodeInductionPAEndpointCoordinates) :
    Fin 215 → Nat :=
  Matrix.vecAppend rfl
    (compactAdditiveInductionPAAxiomRuleCheckEnvironment
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth
      (compactInductionEndpointAxiomSlot
        axiomStart axiomFinish endpointCoordinates)
      body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate routeCoordinates)
    ![inputStart, inputFinish, axiomStart, axiomFinish,
      formulaStart, formulaFinish, suffixStart, suffixFinish,
      proofTag, certificateTag,
      endpointCoordinates.inputBoundary, endpointCoordinates.inputCount,
      endpointCoordinates.inputBoundarySize, endpointCoordinates.tailStart,
      endpointCoordinates.tailFinish, endpointCoordinates.tailBoundary,
      endpointCoordinates.tailCount, endpointCoordinates.tailBoundarySize,
      endpointCoordinates.axiomBoundary, endpointCoordinates.axiomCount,
      endpointCoordinates.axiomBoundarySize,
      endpointCoordinates.parser.inputBoundary,
      endpointCoordinates.parser.inputCount,
      endpointCoordinates.parser.inputBoundarySize,
      endpointCoordinates.parser.expectedBoundary,
      endpointCoordinates.parser.expectedCount,
      endpointCoordinates.parser.expectedBoundarySize,
      endpointCoordinates.parser.stateBoundary,
      endpointCoordinates.parser.stateCount,
      endpointCoordinates.parser.tableWidth,
      endpointCoordinates.parser.valueBound]

set_option maxHeartbeats 6000000 in
set_option maxRecDepth 8192 in
@[simp] theorem compactNumericVerifierPAAxiomInductionLeafRowsDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish proofTag certificateTag
      gammaBoundary gammaCount resultBoolValue depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidate : CompactNatListRowSlot)
    (routeCoordinates : CompactGuardedInductionSentenceRouteCoordinates)
    (endpointCoordinates :
      CompactCertificateNodeInductionPAEndpointCoordinates) :
    compactNumericVerifierPAAxiomInductionLeafRowsDef.val.Evalb
        (compactNumericVerifierPAAxiomInductionLeafRowsEnvironment
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish proofTag certificateTag
          gammaBoundary gammaCount resultBoolValue depth
          body zeroWitness openZeroWitness openSuccessorWitness captureOne
          empty base negatedBase stepZero stepSuccessor negatedStepZero
          stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
          innerDisjunction sentence fvarList depthCapture fixed generated
          candidate routeCoordinates endpointCoordinates) ↔
      CompactNumericVerifierPAAxiomInductionLeafRows
        tokenTable width tokenCount inputStart inputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish proofTag certificateTag
        gammaBoundary gammaCount resultBoolValue depth
        body zeroWitness openZeroWitness openSuccessorWitness captureOne
        empty base negatedBase stepZero stepSuccessor negatedStepZero
        stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
        innerDisjunction sentence fvarList depthCapture fixed generated
        candidate routeCoordinates endpointCoordinates := by
  let innerEnv := compactAdditiveInductionPAAxiomRuleCheckEnvironment
    tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue depth
    (compactInductionEndpointAxiomSlot
      axiomStart axiomFinish endpointCoordinates)
    body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
    base negatedBase stepZero stepSuccessor negatedStepZero
    stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
    innerDisjunction sentence fvarList depthCapture fixed generated candidate
    routeCoordinates
  let env := compactNumericVerifierPAAxiomInductionLeafRowsEnvironment
    tokenTable width tokenCount inputStart inputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish proofTag certificateTag
    gammaBoundary gammaCount resultBoolValue depth
    body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
    base negatedBase stepZero stepSuccessor negatedStepZero
    stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
    innerDisjunction sentence fvarList depthCapture fixed generated candidate
    routeCoordinates endpointCoordinates
  change compactNumericVerifierPAAxiomInductionLeafRowsDef.val.Evalb env ↔ _
  have hruleEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 184 =>
          (#(Fin.castLE (show 184 ≤ 215 by omega) index) :
            Semiterm ℒₒᵣ Empty 215))) = innerEnv := by
    funext coordinate
    simp [env, innerEnv,
      compactNumericVerifierPAAxiomInductionLeafRowsEnvironment,
      Matrix.vecAppend_eq_ite]
  have hendpointEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 215), #1, #2,
          #184, #185, #186, #187, #188, #189, #190, #191, #193,
          #194, #195, #196, #197, #198, #199, #200, #201,
          #202, #203, #204, #205, #206, #207, #208, #209,
          #210, #211, #212, #213, #214]) =
        compactCertificateNodeInductionPAEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag endpointCoordinates := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env,
        compactNumericVerifierPAAxiomInductionLeafRowsEnvironment,
        compactAdditiveInductionPAAxiomRuleCheckEnvironment,
        compactGuardedInductionSentenceRouteEnvironment,
        compactCertificateNodeInductionPAEndpointEnvironment,
        Matrix.vecAppend_eq_ite]
  have hruleSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            (fun index : Fin 184 =>
              (#(Fin.castLE (show 184 ≤ 215 by omega) index) :
                Semiterm ℒₒᵣ Empty 215)))
          Empty.elim compactAdditiveInductionPAAxiomRuleCheckDef.val ↔
        CompactAdditiveInductionPAAxiomRuleCheck
          tokenTable width tokenCount gammaBoundary gammaCount
          resultBoolValue
          (compactInductionEndpointAxiomSlot
            axiomStart axiomFinish endpointCoordinates)
          body zeroWitness openZeroWitness openSuccessorWitness captureOne
          empty base negatedBase stepZero stepSuccessor negatedStepZero
          stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
          innerDisjunction sentence fvarList depthCapture fixed generated
          candidate depth routeCoordinates := by
    rw [hruleEnv]
    exact compactAdditiveInductionPAAxiomRuleCheckDef_spec
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth
      (compactInductionEndpointAxiomSlot
        axiomStart axiomFinish endpointCoordinates)
      body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate routeCoordinates
  have hendpointSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 215), #1, #2,
              #184, #185, #186, #187, #188, #189, #190, #191, #193,
              #194, #195, #196, #197, #198, #199, #200, #201,
              #202, #203, #204, #205, #206, #207, #208, #209,
              #210, #211, #212, #213, #214])
          Empty.elim compactCertificateNodeInductionPAEndpointGraphDef.val ↔
        CompactCertificateNodeInductionPAEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag endpointCoordinates := by
    rw [hendpointEnv]
    exact compactCertificateNodeInductionPAEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointCoordinates
  have hproofTag : env 192 = proofTag := by
    simp [env,
      compactNumericVerifierPAAxiomInductionLeafRowsEnvironment,
      Matrix.vecAppend_eq_ite]
  simp [compactNumericVerifierPAAxiomInductionLeafRowsDef,
    compactPAAxiomInductionEndpointLift, compactPAAxiomInductionRuleLift,
    CompactNumericVerifierPAAxiomInductionLeafRows,
    hendpointSpec, hruleSpec, hproofTag]

theorem compactNumericVerifierPAAxiomInductionLeafRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierPAAxiomInductionLeafRowsDef.val := by
  exact compactNumericVerifierPAAxiomInductionLeafRowsDef.sigma_prop

theorem CompactNumericVerifierPAAxiomInductionLeafRows.sound
    {tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish proofTag certificateTag
      gammaBoundary gammaCount resultBoolValue depth : Nat}
    {bodySlot zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidateSlot : CompactNatListRowSlot}
    {routeCoordinates : CompactGuardedInductionSentenceRouteCoordinates}
    {endpointCoordinates :
      CompactCertificateNodeInductionPAEndpointCoordinates}
    {Gamma : List (List Nat)}
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
      gammaBoundary Gamma)
    (hCandidate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount candidateSlot.start candidateSlot.finish
      (compactSentenceTokens candidate))
    (hGammaCount : gammaCount = Gamma.length)
    (hrows : CompactNumericVerifierPAAxiomInductionLeafRows
      tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish proofTag certificateTag
      gammaBoundary gammaCount resultBoolValue depth
      bodySlot zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidateSlot routeCoordinates endpointCoordinates) :
    ∃ input axiomTokens suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount axiomStart axiomFinish axiomTokens ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      FoundationCompactNumericListedNodeFields.compactStructuralCertificateNodeParser
        input = some (certificateTag, (axiomTokens, suffix)) ∧
      resultBoolValue = compactAdditiveBoolTag
        (FoundationCompactNumericListedRuleChecks.compactAxmRuleCheck
          (Gamma, (compactSentenceTokens candidate, axiomTokens))) := by
  rcases hrows with ⟨_hproofTag, hendpoint, hrule⟩
  have hrouteFull := hrule.1
  have hcons := hrule.2.1
  rcases hendpoint.sound with
    ⟨input, axiomTokens, suffix,
      hinput, haxiom, hsuffix, hparser⟩
  rcases hendpoint with
    ⟨_hinputRows, htailRows, haxiomRows, _hcertificateTag,
      _houterCons, hinnerCons, hformula, happend⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, htailLayout, htailElementRows⟩
  rcases haxiomRows.realize with
    ⟨decodedAxiom, hdecodedAxiomCount,
      hdecodedAxiomLayout, hdecodedAxiomRows⟩
  have haxiomEq : axiomTokens = decodedAxiom :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hdecodedAxiomLayout haxiom).1
  subst axiomTokens
  rcases hformula.1.realize with
    ⟨formulaInput, hformulaInputCount,
      hformulaInputLayout, hformulaInputRows⟩
  rcases hformula.2.1.realize with
    ⟨formulaSuffix, hformulaSuffixCount,
      hformulaSuffixLayout, hformulaSuffixRows⟩
  have hsuffixEq : suffix = formulaSuffix :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaSuffixLayout hsuffix).1
  subst suffix
  rcases hformula.sound_formula with
    ⟨parsedInput, parsedSuffix,
      hparsedInputLayout, hparsedSuffixLayout, hformulaParser⟩
  have hparsedInputEq : parsedInput = formulaInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaInputLayout hparsedInputLayout).1
  have hparsedSuffixEq : parsedSuffix = formulaSuffix :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaSuffixLayout hparsedSuffixLayout).1
  subst parsedInput
  subst parsedSuffix
  rcases hrouteFull.1.1.2.2.1.2.1.realize with
    ⟨bodyTokens, hbodyCount, hbodyLayout, hbodyRows⟩
  have hinnerCons' :
      FoundationCompactNumericListedDirectNatListConsRows.CompactAdditiveNatListConsRows
        tokenTable width tokenCount endpointCoordinates.parser.inputBoundary
        formulaInput.length endpointCoordinates.tailBoundary tail.length 22 := by
    simpa only [hformulaInputCount, htailCount] using hinnerCons
  have htailCons : tail = 22 :: formulaInput :=
    hinnerCons'.eq_cons_of_rows hformulaInputRows htailElementRows
  have happend' :
      FoundationCompactNumericListedDirectNatListAppendSlices.CompactAdditiveNatListAppendSlices
        tokenTable width tokenCount axiomStart axiomFinish
        decodedAxiom.length suffixStart suffixFinish formulaSuffix.length
        endpointCoordinates.tailStart endpointCoordinates.tailFinish
        tail.length := by
    simpa only [hdecodedAxiomCount, hformulaSuffixCount, htailCount]
      using happend
  have htailAppend : tail = decodedAxiom ++ formulaSuffix :=
    (compactAdditiveNatListAppendSlices_iff_append
      hdecodedAxiomLayout hformulaSuffixLayout htailLayout).mp happend'
  have hcons' :
      FoundationCompactNumericListedDirectNatListConsRows.CompactAdditiveNatListConsRows
        tokenTable width tokenCount bodySlot.boundary bodyTokens.length
        endpointCoordinates.axiomBoundary decodedAxiom.length 22 := by
    simpa [compactInductionEndpointAxiomSlot,
      hbodyCount, hdecodedAxiomCount] using hcons
  have haxiomCons : decodedAxiom = 22 :: bodyTokens :=
    hcons'.eq_cons_of_rows hbodyRows hdecodedAxiomRows
  have hformulaSplit : formulaInput = bodyTokens ++ formulaSuffix := by
    have hconsEq : 22 :: formulaInput =
        22 :: (bodyTokens ++ formulaSuffix) := by
      rw [← htailCons, htailAppend, haxiomCons]
      rfl
    exact (List.cons.inj hconsEq).2
  rcases (compactFormulaTokenParser_success_iff
      1 formulaInput formulaSuffix).mp hformulaParser with
    ⟨body, hparserSplit⟩
  have hbodyAppend : bodyTokens ++ formulaSuffix =
      compactArithmeticFormulaTokens body ++ formulaSuffix := by
    rw [← hformulaSplit, hparserSplit]
  have hbodyTokens : bodyTokens = compactArithmeticFormulaTokens body :=
    List.append_cancel_right hbodyAppend
  subst bodyTokens
  have hrule' : CompactAdditiveInductionPAAxiomRuleCheck
      tokenTable width tokenCount gammaBoundary Gamma.length resultBoolValue
      (compactInductionEndpointAxiomSlot
        axiomStart axiomFinish endpointCoordinates)
      bodySlot zeroWitness openZeroWitness openSuccessorWitness captureOne
      empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidateSlot depth routeCoordinates := by
    simpa [hGammaCount] using hrule
  have hresult :=
    (compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
      body candidate hcons hrouteFull hGamma hbodyLayout hCandidate).mp hrule'
  have haxiomCanonical : decodedAxiom =
      compactPAAxiomCertificateTokens (.induction body) := by
    simpa [compactPAAxiomCertificateTokens] using haxiomCons
  refine ⟨input, decodedAxiom, formulaSuffix,
    hinput, hdecodedAxiomLayout, hformulaSuffixLayout, ?_, ?_⟩
  · simpa using hparser
  · simpa [haxiomCanonical] using hresult

#print axioms compactNumericVerifierPAAxiomInductionLeafRowsDef_spec
#print axioms compactNumericVerifierPAAxiomInductionLeafRowsDef_sigmaZero
#print axioms CompactNumericVerifierPAAxiomInductionLeafRows.sound

end FoundationCompactNumericListedDirectVerifierPAAxiomInductionLeafRows
