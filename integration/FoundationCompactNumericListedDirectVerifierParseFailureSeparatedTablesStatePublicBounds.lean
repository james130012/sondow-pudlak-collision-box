import integration.FoundationCompactNumericListedDirectVerifierParseFailureCanonicalFrameCompleteness
import integration.FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
import integration.FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesPublicBounds

/-!
# Public coordinates for the failed parse-state graph

The canonical state frame supplies the exact proof and certificate slices.
Their parser graphs are reconstructed with public bounds, while the common
state table header is controlled by an explicit caller-supplied bit budget.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStatePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesPublicBounds
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows
open FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStateGraph
open FoundationCompactNumericListedDirectVerifierParseFailureCanonicalFrameCompleteness
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

private theorem compactAdditiveNatListDirectLayout_coordinates_le
    {tokenTable width tokenCount start finish : Nat}
    {values : List Nat}
    (hlayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start finish values) :
    start < tokenCount /\ finish <= tokenCount := by
  rcases hlayout.toSlice with
    ⟨bodyStart, _hbodyStart, hheader, hfinish⟩
  have hbodyFinish : bodyStart + values.length <= tokenCount := hheader.2
  exact ⟨hheader.1.1, by omega⟩

/- A failed parse step has a complete separated-tables state graph whose
parser-specific coordinates are all bounded from the state header and the two
actual parser inputs. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericVerifierParseFailureSeparatedTablesStateGraph_of_layouts_with_publicBounds
    {stateTable stateWidth stateTokenCount
      currentStart currentFinish nextStart nextFinish stateBound : Nat}
    {proofTokens certificateTokens : List Nat}
    {currentTask : CompactNumericVerifierTask}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hcurrent : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentFinish
      (((proofTokens, certificateTokens),
        (currentTask :: restTasks, values)), none))
    (hnext : CompactNumericVerifierStateDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextFinish
      (((proofTokens, certificateTokens), (restTasks, values)), some false))
    (hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = none)
    (hcurrentTaskTag : currentTask.1 = 10)
    (hstateTable : Nat.size stateTable <= stateBound)
    (hstateWidth : Nat.size stateWidth <= stateBound)
    (hstateTokenCount : Nat.size stateTokenCount <= stateBound) :
    let proofWeight := compactAdditiveValueWeight proofTokens
    let certificateWeight := compactAdditiveValueWeight certificateTokens
    let publicBound :=
      compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
        stateBound proofWeight certificateWeight
    ∃ currentCoordinates nextCoordinates :
        CompactNumericVerifierStateRowCoordinates,
    ∃ currentSizeWitness nextSizeWitness :
        CompactNumericVerifierStateSizeWitness,
    ∃ taskCoordinates : CompactNumericVerifierTaskRowCoordinates,
    ∃ taskSizeWitness : CompactNumericVerifierTaskSizeWitness,
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
      currentCoordinates.start = currentStart /\
      currentCoordinates.finish = currentFinish /\
      nextCoordinates.start = nextStart /\
      nextCoordinates.finish = nextFinish /\
      CompactNumericVerifierStateCanonicalCorePackage
        stateTable stateWidth stateTokenCount currentStart currentFinish
        (((proofTokens, certificateTokens),
          (currentTask :: restTasks, values)), none)
        currentCoordinates currentSizeWitness /\
      CompactNumericVerifierStateCanonicalCorePackage
        stateTable stateWidth stateTokenCount nextStart nextFinish
        (((proofTokens, certificateTokens), (restTasks, values)), some false)
        nextCoordinates nextSizeWitness /\
      CompactNumericVerifierParseFailureSeparatedTablesStateGraph
        stateTable stateWidth stateTokenCount
        currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness
        taskCoordinates taskSizeWitness
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound /\
      CompactNumericParsePayloadFailureSeparatedTablesParserCoordinateBounds
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        publicBound /\
      forall coordinate : Fin 29,
        Nat.size
          (compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
            stateTable stateWidth stateTokenCount
            currentCoordinates.start currentCoordinates.proofFinish
            currentCoordinates.proofFinish
            currentCoordinates.certificateFinish
            proofTable proofWidth proofTokenCount
            proofInputStart proofInputFinish
            rootStart rootFinish proofTag proofEndpointBound
            certificateTable certificateWidth certificateTokenCount
            certificateInputStart certificateInputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish certificateTag certificateEndpointBound
            coordinate) <= publicBound := by
  let proofWeight := compactAdditiveValueWeight proofTokens
  let certificateWeight := compactAdditiveValueWeight certificateTokens
  let publicBound :=
    compactNumericParsePayloadFailureSeparatedTablesPublicCoordinateSizeBound
      stateBound proofWeight certificateWeight
  rcases
      CompactNumericVerifierParseFailureCanonicalFramePackage.exists_of_layouts
        hcurrent hnext hcurrentTaskTag with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframePackage⟩
  rcases hframePackage with
    ⟨hcurrentPackage, hnextPackage, hhead, hframe, hfailureRows⟩
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
  have hcurrentStartEq := hcurrentPackage.1
  have hcurrentFinishEq := hcurrentPackage.2.1
  have hnextStartEq := hnextPackage.1
  have hnextFinishEq := hnextPackage.2.1
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      hcurrentProof, hcurrentCertificate,
      _hcurrentTaskLayout, _hcurrentTaskRows,
      _hcurrentValueLayout, _hcurrentValueRows,
      _hcurrentTaskCount, _hcurrentValueCount,
      _hcurrentTaskTableWidth, _hcurrentTaskValueBound,
      _hcurrentValueTableWidth, _hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      _hnextProof, _hnextCertificate,
      _hnextTaskLayout, _hnextTaskRows,
      _hnextValueLayout, _hnextValueRows,
      _hnextTaskCount, _hnextValueCount,
      _hnextTaskTableWidth, _hnextTaskValueBound,
      _hnextValueTableWidth, _hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  rcases compactAdditiveNatListDirectLayout_coordinates_le hcurrentProof with
    ⟨hproofStart, hproofFinish⟩
  rcases
      compactAdditiveNatListDirectLayout_coordinates_le hcurrentCertificate with
    ⟨_hcertificateStart, hcertificateFinish⟩
  have hsmall {value : Nat} (hvalue : value <= stateTokenCount) :
      Nat.size value <= stateBound :=
    (Nat.size_le_size hvalue).trans hstateTokenCount
  have hstateBounds :
      CompactNumericParsePayloadFailureSeparatedTablesStateCoordinateBounds
        stateTable stateWidth stateTokenCount
        currentCoordinates.start currentCoordinates.proofFinish
        currentCoordinates.proofFinish currentCoordinates.certificateFinish
        stateBound :=
    { stateTable := hstateTable
      stateWidth := hstateWidth
      stateTokenCount := hstateTokenCount
      stateProofStart := hsmall (Nat.le_of_lt hproofStart)
      stateProofFinish := hsmall hproofFinish
      stateCertificateStart := hsmall hproofFinish
      stateCertificateFinish := hsmall hcertificateFinish }
  rcases
      exists_compactNumericParsePayloadFailureSeparatedTablesGraph_of_eq_none_with_publicBounds
        hcurrentProof hcurrentCertificate hstateBounds hparse with
    ⟨proofTable, proofWidth, proofTokenCount,
      proofInputStart, proofInputFinish,
      rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      hpayload, hparserBounds, henvironmentBounds⟩
  refine ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness,
    proofTable, proofWidth, proofTokenCount,
    proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound, ?_⟩
  exact ⟨hcurrentStartEq, hcurrentFinishEq,
    hnextStartEq, hnextFinishEq,
    hcurrentPackageSaved, hnextPackageSaved,
    ⟨hcurrentCore, hnextCore, hhead, hframe,
      ⟨hpayload, hfailureRows⟩⟩,
    hparserBounds, henvironmentBounds⟩

#print axioms
  exists_compactNumericVerifierParseFailureSeparatedTablesStateGraph_of_layouts_with_publicBounds

end FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesStatePublicBounds
