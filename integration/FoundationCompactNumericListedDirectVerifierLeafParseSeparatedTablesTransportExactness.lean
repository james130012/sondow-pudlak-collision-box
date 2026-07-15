import integration.FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
import integration.FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRowsCompleteness

/-!
# Exact semantics of separated-table leaf transport

The arithmetic transport graph decodes to the exact proof and certificate
suffixes, drops the parse-task head, and pushes the proof root's own context
with the checked leaf result.  The context identity is proved bit-for-bit
across the independent proof and verifier-state tables.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportExactness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality
open FoundationCompactNumericListedDirectVerifierLeafParseStackRows
open FoundationCompactNumericListedDirectVerifierLeafParseStackRowsCompleteness
open FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows

theorem CompactNumericVerifierLeafParseSeparatedTablesTransportRows.sound
    {stateTable stateWidth stateTokenCount
      sourceTaskBoundary targetTaskBoundary
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount
      suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize : Nat}
    {proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {rootGamma : List (List Nat)} {result : Bool}
    (htransport : CompactNumericVerifierLeafParseSeparatedTablesTransportRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTasks.length
      targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length
      targetValueBoundary targetValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount
      suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag result))
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix)
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish rootGamma)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextStart nextProofFinish nextProof)
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
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    nextProof = proofSuffix ∧
      nextCertificate = certificateSuffix ∧
      targetTasks = sourceTasks.drop 1 ∧
      targetValues = (rootGamma, result) :: sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  rcases htransport with
    ⟨hproofCross, hcertificateCross, htargetExposed,
      hgammaCross, htargetBool, hstack⟩
  have hproof : nextProof = proofSuffix :=
    hproofCross.natListValues_eq hproofSuffix hnextProof
  have hcertificate : nextCertificate = certificateSuffix :=
    hcertificateCross.natListValues_eq
      hcertificateSuffix hnextCertificate
  have hstackSaved := hstack
  rcases hstack with
    ⟨_htaskWidth, _htaskBound, _hvalueWidth, _hvalueBound,
      _hstatus, _htaskDrop, hvaluePush⟩
  have htargetNonempty : 0 < targetValues.length := by
    have hnonempty : 1 ≤ targetValues.length := hvaluePush.2.2.1
    omega
  rcases htargetExposed.realize_actual htargetNonempty htargetValueRows with
    ⟨targetHead, _htargetHead, htargetHeadLayout, htargetGammaRows,
      htargetGammaLength, htargetHeadBool⟩
  have htargetCore := htargetExposed.2.2.2.2.2.2.2.2.2
  have htargetGammaLayout : CompactAdditiveNatListListDirectLayout
      stateTable stateWidth stateTokenCount
        targetStart targetGammaFinish targetHead.1 := by
    refine ⟨targetGammaBoundary, ?_, htargetGammaRows, ?_⟩
    · simpa [compactNumericChildResultRowCoordinatesOf,
        htargetGammaLength] using htargetCore.1
    · have hsizeEq : targetGammaBoundarySize =
          Nat.size targetGammaBoundary := by
        simpa [compactNumericChildResultRowCoordinatesOf] using
          htargetCore.2.2.1
      have hsize : targetGammaBoundarySize ≤
          (targetGammaCount + 1) * stateTokenCount := by
        simpa [compactNumericChildResultRowCoordinatesOf] using
          htargetCore.2.2.2.1
      rw [htargetGammaLength, ← hsizeEq]
      exact hsize
  have htargetGamma : targetHead.1 = rootGamma :=
    FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality.CompactFixedWidthCrossTableSlicesEq.natListListValues_eq
      hgammaCross hrootGamma htargetGammaLayout
  have htargetResult : targetHead.2 = result := by
    apply compactAdditiveBoolTag_injective
    exact htargetHeadBool.trans htargetBool
  have hstackTyped : CompactNumericVerifierLeafParseStackRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTasks.length
      targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length
      targetValueBoundary targetValues.length
      targetGammaBoundary targetHead.1.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      (compactAdditiveBoolTag targetHead.2) nextStatusTag := by
    simpa only [htargetGammaLength, htargetResult] using hstackSaved
  rcases hstackTyped.sound
      hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
      htargetGammaRows with
    ⟨htasks, hvalues, htaskWidth, htaskBound,
      hvalueWidth, hvalueBound, hstatus⟩
  have htargetHeadEq : targetHead = (rootGamma, result) :=
    Prod.ext htargetGamma htargetResult
  rw [htargetHeadEq] at hvalues
  exact ⟨hproof, hcertificate, htasks,
    hvalues,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

theorem exists_compactNumericVerifierLeafParseSeparatedTablesTransportRows_of_rows
    {stateTable stateWidth stateTokenCount
      sourceTaskBoundary targetTaskBoundary
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount
      suffixStart suffixFinish : Nat}
    {proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceTasks targetTasks : List CompactNumericVerifierTask}
    {sourceValues targetValues : List CompactNumericChildResult}
    {rootGamma : List (List Nat)} {result : Bool}
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        witnessFinish rootFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish certificateSuffix)
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish rootGamma)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextStart nextProofFinish nextProof)
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
    (hnextProofValue : nextProof = proofSuffix)
    (hnextCertificateValue : nextCertificate = certificateSuffix)
    (htaskTableWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskValueBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueTableWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueValueBound : nextValueValueBound = currentValueValueBound)
    (hsourceTaskNonempty : 1 ≤ sourceTasks.length)
    (htasks : targetTasks = sourceTasks.drop 1)
    (hvalues : targetValues = (rootGamma, result) :: sourceValues)
    (hstatus : nextStatusTag = 0) :
    ∃ targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize,
      CompactNumericVerifierLeafParseSeparatedTablesTransportRows
        stateTable stateWidth stateTokenCount
        sourceTaskBoundary sourceTasks.length
        targetTaskBoundary targetTasks.length
        sourceValueBoundary sourceValues.length
        targetValueBoundary targetValues.length
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        proofTable proofWidth proofTokenCount rootStart rootGammaFinish
        witnessFinish rootFinish
        certificateTable certificateWidth certificateTokenCount
        suffixStart suffixFinish
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag result) := by
  subst nextProof
  subst nextCertificate
  have hproofCross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    hproofSuffix hnextProof
  have hcertificateCross :=
    CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hcertificateSuffix hnextCertificate
  have htargetNonempty : 0 < targetValues.length := by
    rw [hvalues]
    simp
  have htargetValueGraphNext : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount targetValueBoundary
        targetValues.length nextValueTableWidth nextValueValueBound := by
    rw [hvalueTableWidth, hvalueValueBound]
    exact htargetValueGraph
  rcases
      FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula.CompactNumericChildResultListRowsGraph.exists_exposed
        htargetValueGraphNext htargetNonempty with
    ⟨targetStart, targetFinish, targetGammaFinish, targetGammaCount,
      targetGammaBoundary, targetBool, targetGammaBoundarySize,
      htargetExposed⟩
  rcases htargetExposed.realize_actual htargetNonempty htargetValueRows with
    ⟨targetHead, htargetHeadAt, _htargetHeadLayout,
      htargetGammaRows, htargetGammaLength, htargetHeadBool⟩
  have htargetHeadExpected :
      targetValues.getI 0 = (rootGamma, result) := by
    rw [hvalues]
    simp
  have htargetHeadEq : targetHead = (rootGamma, result) :=
    htargetHeadAt.symm.trans htargetHeadExpected
  rw [htargetHeadEq] at htargetGammaRows htargetGammaLength htargetHeadBool
  have htargetCore := htargetExposed.2.2.2.2.2.2.2.2.2
  have htargetGammaLayout : CompactAdditiveNatListListDirectLayout
      stateTable stateWidth stateTokenCount
        targetStart targetGammaFinish rootGamma := by
    refine ⟨targetGammaBoundary, ?_, htargetGammaRows, ?_⟩
    · simpa [compactNumericChildResultRowCoordinatesOf,
        htargetGammaLength] using htargetCore.1
    · have hsizeEq : targetGammaBoundarySize =
          Nat.size targetGammaBoundary := by
        simpa [compactNumericChildResultRowCoordinatesOf] using
          htargetCore.2.2.1
      have hsize : targetGammaBoundarySize ≤
          (targetGammaCount + 1) * stateTokenCount := by
        simpa [compactNumericChildResultRowCoordinatesOf] using
          htargetCore.2.2.2.1
      rw [htargetGammaLength, ← hsizeEq]
      exact hsize
  have hgammaCross :=
    FoundationCompactNumericListedDirectCrossTableNatListListSliceEquality.CompactFixedWidthCrossTableSlicesEq.of_natListListLayouts
      hrootGamma htargetGammaLayout
  have hstackBase := CompactNumericVerifierLeafParseStackRows.of_rows
    hsourceTaskRows htargetTaskRows hsourceValueRows htargetValueRows
    htargetGammaRows hsourceTaskGraph htargetTaskGraph
    hsourceValueGraph htargetValueGraph
    htaskTableWidth htaskValueBound hvalueTableWidth hvalueValueBound
    hsourceTaskNonempty htasks hvalues hstatus
  have hstack : CompactNumericVerifierLeafParseStackRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTasks.length
      targetTaskBoundary targetTasks.length
      sourceValueBoundary sourceValues.length
      targetValueBoundary targetValues.length
      targetGammaBoundary targetGammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      (compactAdditiveBoolTag result) nextStatusTag := by
    simpa only [htargetGammaLength] using hstackBase
  exact ⟨targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize,
    hproofCross, hcertificateCross, htargetExposed, hgammaCross,
    htargetHeadBool.symm, hstack⟩

#print axioms CompactNumericVerifierLeafParseSeparatedTablesTransportRows.sound
#print axioms
  exists_compactNumericVerifierLeafParseSeparatedTablesTransportRows_of_rows

end FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportExactness
