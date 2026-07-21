import integration.FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraphPublicBounds

/-!
# Original-input public bounds for an accepted PA-leaf state graph

The parser transport already has an input-weight bound.  The only unsafe
summand in the old PA-leaf graph envelope was the fully expanded PA rule
stream.  This file replaces that summand, under actual checker acceptance,
by the branch-independent original-payload polynomial.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraphPublicBounds
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionRuleWeight
open FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedInductionPublicBounds

def compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight originalWeight : Nat) : Nat :=
  compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight +
    compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound
      originalWeight

/-- A PA leaf's three typed inputs are subobjects of the two current source
streams.  The nested context needs the parser's explicit quadratic envelope;
the candidate and certificate bodies need only their source-stream weights. -/
def compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
    (proofWeight certificateWeight : Nat) : Nat :=
  compactNumericNestedListWeightBound proofWeight +
    proofWeight + certificateWeight

theorem compactStructuralCertificateNodeParser_payloadWeight_le
    {tokens : List Nat} {node : CompactNumericCertificateNode}
    (hparser : compactStructuralCertificateNodeParser tokens = some node) :
    compactAdditiveValueWeight node.2.1 <=
      compactAdditiveValueWeight tokens := by
  cases tokens with
  | nil =>
      simp [compactStructuralCertificateNodeParser] at hparser
  | cons tag body =>
      have hbody : compactAdditiveValueWeight body <=
          compactAdditiveValueWeight (tag :: body) :=
        compactAdditiveValueWeight_suffix_le (List.suffix_cons tag body)
      by_cases hzero : tag = 0
      · subst tag
        have hnode : (0, (([] : List Nat), body)) = node := by
          simpa [compactStructuralCertificateNodeParser] using hparser
        rw [<- hnode]
        exact (compactAdditiveValueWeight_list_pos body).trans hbody
      · by_cases hone : tag = 1
        · subst tag
          cases hcertificate : compactPAAxiomCertificateTokenParser body with
          | none =>
              simp [compactStructuralCertificateNodeParser, hcertificate]
                at hparser
          | some suffix =>
              have hnode :
                  (1, (consumedTokenPrefix body suffix, suffix)) = node := by
                simpa [compactStructuralCertificateNodeParser, hcertificate]
                  using hparser
              rw [<- hnode]
              exact (consumedTokenPrefix_weight_le body suffix).trans hbody
        · by_cases htwo : tag = 2
          · subst tag
            have hnode : (2, (([] : List Nat), body)) = node := by
              simpa [compactStructuralCertificateNodeParser, hzero, hone]
                using hparser
            rw [<- hnode]
            exact (compactAdditiveValueWeight_list_pos body).trans hbody
          · by_cases hthree : tag = 3
            · subst tag
              have hnode : (3, (([] : List Nat), body)) = node := by
                simpa [compactStructuralCertificateNodeParser,
                  hzero, hone, htwo] using hparser
              rw [<- hnode]
              exact (compactAdditiveValueWeight_list_pos body).trans hbody
            · simp [compactStructuralCertificateNodeParser,
                hzero, hone, htwo, hthree] at hparser

theorem compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_le_source
    {proofTokens certificateTokens : List Nat}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens =
      some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser
      certificateTokens = some certificateNode)
    (hcandidate : proofNode.2.2.1 = compactSentenceTokens candidate)
    (hcertificate : certificateNode.2.1 =
      compactPAAxiomCertificateTokens certificate) :
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
        proofNode.2.1 candidate certificate <=
      compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
        (compactAdditiveValueWeight proofTokens)
        (compactAdditiveValueWeight certificateTokens) := by
  have hfields :=
    compactListedProofNodeFieldsParser_componentsWithin hproofParser
  rcases hfields with
    ⟨hgammaWeight, hcandidateWeight, _hsecondWeight,
      _hwitnessWeight, _hsuffixWeight⟩
  have hcertificateWeight :=
    compactStructuralCertificateNodeParser_payloadWeight_le hcertificateParser
  unfold compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
    compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
  rw [<- hcandidate, <- hcertificate]
  omega

theorem
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_mono_original
    (stateBound proofWeight certificateWeight : Nat)
    {left right : Nat} (hweight : left <= right) :
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight left <=
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight right := by
  have hpa :=
    compactNumericVerifierPAAxiomAcceptedPublicCoordinateSizeBound_mono hweight
  unfold compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
  omega

theorem compactNumericParsePayloadSuccessExposedTaskCoordinateBounds_mono
    {rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize left right : Nat}
    (hbounds : CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize left)
    (hle : left <= right) :
    CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize right :=
  { gammaFinish := hbounds.gammaFinish.trans hle
    gammaCount := hbounds.gammaCount.trans hle
    gammaBoundary := hbounds.gammaBoundary.trans hle
    firstFinish := hbounds.firstFinish.trans hle
    firstCount := hbounds.firstCount.trans hle
    secondFinish := hbounds.secondFinish.trans hle
    secondCount := hbounds.secondCount.trans hle
    witnessFinish := hbounds.witnessFinish.trans hle
    witnessCount := hbounds.witnessCount.trans hle
    suffixCount := hbounds.suffixCount.trans hle
    gammaBoundarySize := hbounds.gammaBoundarySize.trans hle }

/-- The parse graph and the typed PA rows share one result coordinate.  Thus
acceptance of the raw parsed payload transfers to the typed candidate and
certificate without any semantic assumption. -/
theorem compactAxmRuleCheck_typed_accept_of_shared_resultBool
    (rawGamma typedGamma : List (List Nat))
    (rawCandidate rawCertificate : List Nat)
    (typedCandidate : LO.FirstOrder.ArithmeticSentence)
    (typedCertificate : PAAxiomCertificate)
    (resultBool : Nat)
    (hrawAccept : compactAxmRuleCheck
      (rawGamma, (rawCandidate, rawCertificate)) = true)
    (hrawResult : compactAdditiveBoolTag
      (compactAxmRuleCheck (rawGamma, (rawCandidate, rawCertificate))) =
        resultBool)
    (htypedResult : resultBool = compactAdditiveBoolTag
      (compactAxmRuleCheck
        (typedGamma, (compactSentenceTokens typedCandidate,
          compactPAAxiomCertificateTokens typedCertificate)))) :
    compactAxmRuleCheck
      (typedGamma, (compactSentenceTokens typedCandidate,
        compactPAAxiomCertificateTokens typedCertificate)) = true := by
  apply Eq.symm
  apply compactAdditiveBoolTag_injective
  calc
    compactAdditiveBoolTag true =
        compactAdditiveBoolTag
          (compactAxmRuleCheck
            (rawGamma, (rawCandidate, rawCertificate))) := by
      rw [hrawAccept]
    _ = resultBool := hrawResult
    _ = compactAdditiveBoolTag
        (compactAxmRuleCheck
          (typedGamma, (compactSentenceTokens typedCandidate,
            compactPAAxiomCertificateTokens typedCertificate))) := htypedResult

theorem compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound_le_of_accept
    (stateBound proofWeight certificateWeight : Nat)
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (haccept : compactAxmRuleCheck
      (Gamma, (compactSentenceTokens candidate,
        compactPAAxiomCertificateTokens certificate)) = true) :
    compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight Gamma candidate certificate <=
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
        (compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          Gamma candidate certificate) := by
  have hpa :=
    compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound_le_of_accept
      Gamma candidate certificate haccept
  unfold compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
  omega

theorem compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_state_le
    (stateBound proofWeight certificateWeight originalWeight : Nat) :
    stateBound <=
      compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight originalWeight := by
  unfold compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds.compactNumericParsePayloadSuccessExposedSeparatedTablesPublicCoordinateSizeBound
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds.compactNumericParsePayloadSuccessSeparatedTablesPublicCoordinateSizeBound
  dsimp only
  omega

set_option maxHeartbeats 4000000 in
theorem
    exists_compactNumericVerifierPAAxiomLeafStateGraph_of_accepted_success_and_transition_with_originalPublicBounds
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      sourceTaskBoundary targetTaskBoundary sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag stateBound : Nat}
    {proofTokens certificateTokens nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {proofNode : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hstateBounds :
      CompactNumericParsePayloadSuccessSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish stateBound)
    (hnextValueValueBoundSize : Nat.size nextValueValueBound <= stateBound)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some proofNode)
    (hcertificateParser : compactStructuralCertificateNodeParser certificateTokens =
      some certificateNode)
    (hproofTag : proofNode.1 = 1)
    (htransition : compactNumericNodeTransition proofNode certificateNode
      (sourceTasks.drop 1) sourceValues =
        some ((nextProof, nextCertificate), (targetTasks, targetValues)))
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount sourceTaskBoundary sourceTasks)
    (htargetTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout
        stateTable stateWidth stateTokenCount targetTaskBoundary targetTasks)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues)
    (hsourceTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount sourceTaskBoundary
        sourceTasks.length currentTaskTableWidth currentTaskValueBound)
    (htargetTaskGraph : CompactNumericVerifierTaskListRowsGraph
      stateTable stateWidth stateTokenCount targetTaskBoundary
        targetTasks.length currentTaskTableWidth currentTaskValueBound)
    (hsourceValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount sourceValueBoundary
        sourceValues.length currentValueTableWidth currentValueValueBound)
    (htargetValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount targetValueBoundary
        targetValues.length currentValueTableWidth currentValueValueBound)
    (hsourceTaskNonempty : 1 <= sourceTasks.length)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hnextStatus : nextStatusTag = 0)
    (haccept : compactAxmRuleCheck
      (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)) = true) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    exists proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    exists rootStart rootFinish proofTag proofEndpointBound,
    exists certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    exists axiomStart axiomFinish formulaStart formulaFinish,
    exists suffixStart suffixFinish certificateTag certificateEndpointBound,
    exists rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize,
    exists targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize,
    exists candidate : LO.FirstOrder.ArithmeticSentence,
    exists certificate : PAAxiomCertificate,
    exists c : CompactNumericVerifierPAAxiomJointLeafCoordinates,
      let originalWeight :=
        compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
          proofNode.2.1 candidate certificate
      let publicBound :=
        compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
          stateBound proofWeight certificateWeight originalWeight
      CompactNumericVerifierPAAxiomLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        sourceTaskBoundary sourceTasks.length targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag
          (compactAxmRuleCheck
            (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)))) c /\
      CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        proofNode.2.1 candidate certificate c /\
      compactAxmRuleCheck
        (proofNode.2.1, (compactSentenceTokens candidate,
          compactPAAxiomCertificateTokens certificate)) = true /\
      originalWeight <=
        compactNumericVerifierPAAxiomLeafOriginalPayloadSourceWeightBound
          proofWeight certificateWeight /\
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound /\
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize publicBound /\
      (forall coordinate : Fin 22,
        Nat.size
          (compactNumericVerifierPAAxiomLeafStateParserEnvironment
            proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound
            certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound
            coordinate) <= publicBound) /\
      (forall coordinate : Fin 11,
        Nat.size
          (compactNumericVerifierParseSuccessParsedEnvironment
            rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
            secondFinish secondCount witnessFinish witnessCount suffixCount
            rootGammaBoundarySize coordinate) <= publicBound) /\
      (forall coordinate : Fin 8,
        Nat.size
          (compactNumericVerifierParseLeafOutputEnvironment
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBool targetGammaBoundarySize
            (compactAdditiveBoolTag
              (compactAxmRuleCheck
                (proofNode.2.1,
                  (proofNode.2.2.1, certificateNode.2.1)))) coordinate) <=
          publicBound) /\
      forall coordinate : Fin 259,
        Nat.size
          (compactNumericVerifierPAAxiomJointLeafRowsEnvironment c coordinate) <=
        publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  rcases
      FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraphPublicBounds.exists_compactNumericVerifierPAAxiomLeafStateGraph_of_success_and_transition_with_publicBounds
        hproofLayout hcertificateLayout hstateBounds hnextValueValueBoundSize
        hproofParser hcertificateParser hproofTag htransition
        hnextProof hnextCertificate
        hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
        hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htaskTableWidth htaskValueBound
        hvalueTableWidth hvalueValueBound hnextStatus with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      rootGammaBoundarySize,
      targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize,
      candidate, certificate, c, hfull, hcanonical,
      hcandidateSource, hcertificateSource,
      hparserStructured, hrootStructured,
      hparserBounds, hrootBounds, hleafBounds, hpaBounds⟩
  have htypedAccept := compactAxmRuleCheck_typed_accept_of_shared_resultBool
    proofNode.2.1 proofNode.2.1 proofNode.2.2.1 certificateNode.2.1
    candidate certificate c.resultBool haccept
    hfull.2.2.2.2.2 hcanonical.2.1
  have hsource :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight_le_source
      candidate certificate hproofParser hcertificateParser
      hcandidateSource hcertificateSource
  let originalWeight :=
    compactNumericVerifierPAAxiomLeafOriginalPayloadWeight
      proofNode.2.1 candidate certificate
  let oldPublicBound :=
    compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight proofNode.2.1
      candidate certificate
  let publicBound :=
    compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight originalWeight
  have hbound : oldPublicBound <= publicBound := by
    dsimp only [oldPublicBound, publicBound, originalWeight]
    exact
      compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound_le_of_accept
        stateBound proofWeight certificateWeight proofNode.2.1
        candidate certificate htypedAccept
  have hparserStructured' :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound :=
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds.CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds.mono
      hparserStructured hbound
  have hrootStructured' :
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize publicBound :=
    compactNumericParsePayloadSuccessExposedTaskCoordinateBounds_mono
      hrootStructured hbound
  have hparserBounds' := fun coordinate =>
    (hparserBounds coordinate).trans hbound
  have hrootBounds' := fun coordinate =>
    (hrootBounds coordinate).trans hbound
  have hleafBounds' := fun coordinate =>
    (hleafBounds coordinate).trans hbound
  have hpaBounds' := fun coordinate =>
    (hpaBounds coordinate).trans hbound
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize,
    candidate, certificate, c, hfull, hcanonical, htypedAccept, hsource,
    hparserStructured', hrootStructured',
    hparserBounds', hrootBounds', hleafBounds', hpaBounds'⟩

#print axioms
  compactAxmRuleCheck_typed_accept_of_shared_resultBool
#print axioms
  compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound_le_of_accept
#print axioms
  compactNumericVerifierPAAxiomAcceptedLeafStateGraphPublicCoordinateSizeBound_state_le
#print axioms
  exists_compactNumericVerifierPAAxiomLeafStateGraph_of_accepted_success_and_transition_with_originalPublicBounds

end FoundationCompactNumericListedDirectVerifierPAAxiomAcceptedLeafStateGraphPublicBounds
