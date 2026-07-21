import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds

/-!
# Public bounds for the PA-axiom leaf state graph

The successful parser transport and canonical PA rows are constructed with
their public bounds.  Their bounds are added to obtain one common envelope for
the parser, parsed-root, leaf-output, and PA coordinate blocks.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraphPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportPublicBounds
open FoundationCompactNumericListedDirectVerifierLeafOutputPublicBounds
open FoundationCompactNumericListedDirectVerifierParseStateFormula
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafCrossTableBridgeGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafParsedSemantics
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
open FoundationCompactPAAxiomCertificate

def compactNumericVerifierPAAxiomLeafStateParserEnvironment
    (proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    Fin 22 -> Nat :=
  ![proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound]

/-- One public envelope for every coordinate block used by the PA leaf graph. -/
def compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound
    (stateBound proofWeight certificateWeight : Nat)
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) : Nat :=
  compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight +
    compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
      Gamma candidate certificate

theorem compactNumericVerifierPAAxiomLeafStateParserEnvironment_size_le
    {proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      bound : Nat}
    (hbounds :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound bound)
    (coordinate : Fin 22) :
    Nat.size
        (compactNumericVerifierPAAxiomLeafStateParserEnvironment
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound
          coordinate) <= bound := by
  rcases hbounds with
    ⟨hproofTable, hproofWidth, _hproofTokenCountValue, hproofTokenCount,
      hproofInputStart, hproofInputFinish, hrootStart, hrootFinish,
      hproofTag, hproofEndpointBound,
      hcertificateTable, hcertificateWidth, hcertificateTokenCount,
      hcertificateInputStart, hcertificateInputFinish,
      haxiomStart, haxiomFinish, hformulaStart, hformulaFinish,
      hsuffixStart, hsuffixFinish, hcertificateTag,
      hcertificateEndpointBound⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierPAAxiomLeafStateParserEnvironment] <;>
    assumption

theorem compactNumericVerifierPAAxiomLeafStateParsedRootEnvironment_size_le
    {rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize bound : Nat}
    (hbounds : CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize bound)
    (coordinate : Fin 11) :
    Nat.size
        (compactNumericVerifierParseSuccessParsedEnvironment
          rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
          secondFinish secondCount witnessFinish witnessCount suffixCount
          rootGammaBoundarySize coordinate) <= bound := by
  rcases hbounds with
    ⟨hrootGammaFinish, hrootGammaCount, hrootGammaBoundary,
      hfirstFinish, hfirstCount, hsecondFinish, hsecondCount,
      hwitnessFinish, hwitnessCount, hsuffixCount,
      hrootGammaBoundarySize⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierParseSuccessParsedEnvironment] <;>
    assumption

private theorem compactNumericParsePayloadSuccessExposedTaskCoordinateBounds_mono
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

set_option maxHeartbeats 4000000 in
theorem
    exists_compactNumericVerifierPAAxiomLeafStateGraph_of_success_and_transition_with_publicBounds
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
    (hnextStatus : nextStatusTag = 0) :
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
      let publicBound :=
        compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound
          stateBound proofWeight certificateWeight proofNode.2.1
          candidate certificate
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
      proofNode.2.2.1 = compactSentenceTokens candidate /\
      certificateNode.2.1 = compactPAAxiomCertificateTokens certificate /\
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
  have houtputCase :=
    (compactNumericNodeTransition_eq_some_iff_outputCase
      proofNode certificateNode (sourceTasks.drop 1) sourceValues
      ((nextProof, nextCertificate), (targetTasks, targetValues))).1 htransition
  have hpaOutput :
      certificateNode.1 = 1 /\
      ((proofNode.2.2.2.2.2, certificateNode.2.2),
        (sourceTasks.drop 1,
          (proofNode.2.1,
            compactAxmRuleCheck
              (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) ::
              sourceValues)) =
        ((nextProof, nextCertificate), (targetTasks, targetValues)) := by
    simpa [CompactNumericNodeTransitionOutputCase, hproofTag,
      compactNumericNodeFieldsSuffix] using houtputCase
  rcases hpaOutput with ⟨_hcertificateNodeTag, houtput⟩
  have hnextProofValue : nextProof = proofNode.2.2.2.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.1)
      houtput
    simpa using h.symm
  have hnextCertificateValue : nextCertificate = certificateNode.2.2 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.1.2)
      houtput
    simpa using h.symm
  have htasks : targetTasks = sourceTasks.drop 1 := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.1)
      houtput
    simpa using h.symm
  have hvalues : targetValues =
      (proofNode.2.1,
        compactAxmRuleCheck
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) ::
        sourceValues := by
    have h := congrArg (fun output : CompactNumericRunningPayload => output.2.2)
      houtput
    simpa using h.symm
  rcases
      exists_compactNumericVerifierLeafParseSuccessTransportGraph_of_success_and_transition_with_publicBounds
        hproofLayout hcertificateLayout hstateBounds hnextValueValueBoundSize
        hproofParser hcertificateParser htransition
        rfl rfl rfl hnextProof hnextCertificate
        hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
        hsourceTaskGraph htargetTaskGraph hsourceValueGraph htargetValueGraph
        hsourceTaskNonempty htasks hvalues hnextProofValue
        hnextCertificateValue htaskTableWidth htaskValueBound
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
      htransport, hparserBounds, hrootBounds, _hleafBounds,
      _htransportEnvironmentBounds, hleafEnvironmentBounds⟩
  have hsuccess := htransport.1
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedProofTokens, decodedRoot, hdecodedProofLayout,
      _hdecodedRootLayout, hdecodedProof, hdecodedTag⟩
  have hdecodedProofTokensEq : decodedProofTokens = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedProofLayout
  subst decodedProofTokens
  have hdecodedRootEq : decodedRoot = proofNode :=
    Option.some.inj (hdecodedProof.symm.trans hproofParser)
  subst decodedRoot
  have hproofTagCoordinate : proofTag = 1 := hdecodedTag.symm.trans hproofTag
  rcases
      CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph.realize_pa_leaf_fields
        hsuccess hproofTagCoordinate with
    ⟨parsedProofInput, parsedRoot, candidate, certificate,
      parsedCertificateInput, axiomTokens, parsedCertificateSuffix,
      hparsedProofInput, _hparsedRoot, hparsedProofParser, _hparsedRootTag,
      hparsedGamma, hparsedCandidate, hparsedRootCandidate,
      hparsedCertificateInput, hparsedAxiom, _hparsedCertificateSuffix,
      hparsedCertificateParser, hparsedAxiomTokens, hcertificateTagCoordinate⟩
  have hparsedProofInputEq : parsedProofInput = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hparsedProofInput
  subst parsedProofInput
  have hparsedRootEq : parsedRoot = proofNode :=
    Option.some.inj (hparsedProofParser.symm.trans hproofParser)
  subst parsedRoot
  have hparsedCertificateInputEq : parsedCertificateInput = certificateTokens :=
    hsuccess.1.2.1.natListValues_eq hcertificateLayout hparsedCertificateInput
  subst parsedCertificateInput
  have hcertificateNodeEq :
      (1, (axiomTokens, parsedCertificateSuffix)) = certificateNode :=
    Option.some.inj (hparsedCertificateParser.symm.trans hcertificateParser)
  have hcertificateAxiom : axiomTokens = certificateNode.2.1 := by
    simpa using congrArg (fun node : CompactNumericCertificateNode => node.2.1)
      hcertificateNodeEq
  have hcertificateAxiomTyped :
      certificateNode.2.1 = compactPAAxiomCertificateTokens certificate :=
    hcertificateAxiom.symm.trans hparsedAxiomTokens
  rcases
      CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical_with_publicBounds
        proofNode.2.1 candidate certificate with
    ⟨c, hcanonical, hpaBounds⟩
  have hparsedAxiomTyped : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
      axiomStart axiomFinish (compactPAAxiomCertificateTokens certificate) := by
    simpa [hparsedAxiomTokens] using hparsedAxiom
  have hbridge := CompactNumericVerifierPAAxiomLeafCrossTableBridgeGraph.of_layouts
    hparsedGamma hcanonical.2.2.1 hparsedCandidate hcanonical.2.2.2.1
    hparsedAxiomTyped hcanonical.2.2.2.2.1
  have hcProofTag : c.proofTag = 1 := hcanonical.1.2.2.2.2.1
  have hcCertificateTag : c.certificateTag = 1 := by
    rcases hcanonical.1.2.2.2.2.2 with hfixedOrSymbol | hinduction
    · rcases hfixedOrSymbol with hfixed | hsymbol
      · exact hfixed.1.2.2.2.2.1
      · exact hsymbol.1.2.2.2.2.1
    · exact hinduction.1.2.2.2.1
  have hproofBinding : proofTag = c.proofTag :=
    hproofTagCoordinate.trans hcProofTag.symm
  have hcertificateBinding : certificateTag = c.certificateTag :=
    hcertificateTagCoordinate.trans hcCertificateTag.symm
  have hresultBinding :
      compactAdditiveBoolTag
          (compactAxmRuleCheck
            (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1))) =
        c.resultBool := by
    symm
    simpa [hparsedRootCandidate, hcertificateAxiomTyped] using hcanonical.2.1
  have hfull : CompactNumericVerifierPAAxiomLeafStateGraph
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
          (proofNode.2.1, (proofNode.2.2.1, certificateNode.2.1)))) c :=
    ⟨htransport, hcanonical.1, hbridge, hproofBinding,
      hcertificateBinding, hresultBinding⟩
  let parserBound :=
    compactNumericVerifierLeafParseSuccessTransportPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  let paBound :=
    compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
      proofNode.2.1 candidate certificate
  let publicBound :=
    compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight proofNode.2.1 candidate certificate
  have hparserToPublic : parserBound <= publicBound := by
    dsimp only [parserBound, publicBound,
      compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound]
    omega
  have hpaToPublic : paBound <= publicBound := by
    dsimp only [paBound, publicBound,
      compactNumericVerifierPAAxiomLeafStateGraphPublicCoordinateSizeBound]
    omega
  have hparserBounds' :
      CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound :=
    FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesPublicBounds.CompactNumericParsePayloadSuccessSeparatedTablesParserCoordinateBounds.mono
      hparserBounds hparserToPublic
  have hrootBounds' :
      CompactNumericParsePayloadSuccessExposedTaskCoordinateBounds
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize publicBound :=
    compactNumericParsePayloadSuccessExposedTaskCoordinateBounds_mono
      hrootBounds hparserToPublic
  have hparserEnvironmentBounds : forall coordinate : Fin 22,
      Nat.size
          (compactNumericVerifierPAAxiomLeafStateParserEnvironment
            proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound
            certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound
            coordinate) <= publicBound := fun coordinate =>
    (compactNumericVerifierPAAxiomLeafStateParserEnvironment_size_le
      hparserBounds coordinate).trans hparserToPublic
  have hrootEnvironmentBounds : forall coordinate : Fin 11,
      Nat.size
          (compactNumericVerifierParseSuccessParsedEnvironment
            rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
            secondFinish secondCount witnessFinish witnessCount suffixCount
            rootGammaBoundarySize coordinate) <= publicBound := fun coordinate =>
    (compactNumericVerifierPAAxiomLeafStateParsedRootEnvironment_size_le
      hrootBounds coordinate).trans hparserToPublic
  have hleafEnvironmentBounds' : forall coordinate : Fin 8,
      Nat.size
          (compactNumericVerifierParseLeafOutputEnvironment
            targetStart targetFinish targetGammaFinish targetGammaCount
            targetGammaBoundary targetBool targetGammaBoundarySize
            (compactAdditiveBoolTag
              (compactAxmRuleCheck
                (proofNode.2.1,
                  (proofNode.2.2.1, certificateNode.2.1)))) coordinate) <=
        publicBound := fun coordinate =>
    (hleafEnvironmentBounds coordinate).trans hparserToPublic
  have hpaEnvironmentBounds : forall coordinate : Fin 259,
      Nat.size
          (compactNumericVerifierPAAxiomJointLeafRowsEnvironment c coordinate) <=
        publicBound := fun coordinate =>
    (hpaBounds coordinate).trans hpaToPublic
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
    candidate, certificate, c, hfull, hcanonical,
    hparsedRootCandidate, hcertificateAxiomTyped,
    hparserBounds', hrootBounds',
    hparserEnvironmentBounds, hrootEnvironmentBounds,
    hleafEnvironmentBounds', hpaEnvironmentBounds⟩

#print axioms
  exists_compactNumericVerifierPAAxiomLeafStateGraph_of_success_and_transition_with_publicBounds

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraphPublicBounds
