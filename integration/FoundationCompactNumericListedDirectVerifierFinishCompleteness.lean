import integration.FoundationCompactNumericListedDirectVerifierFinishExactness
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
import integration.FoundationCompactNumericListedDirectNatListSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierValueSliceEquality

/-!
# Canonical converse for the verifier finish branch

The current running state and its executable finish result are encoded in one
canonical token table.  Equality of proof, certificate, empty-task, and value
slices constructs the complete preserved payload; the real finish guard fixes
the stored result bit.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinishCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierFinishFormula
open FoundationCompactNumericListedDirectVerifierPayloadEquality
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectNatListListSliceEquality
open FoundationCompactNumericListedDirectVerifierValueSliceEquality

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

def CompactNumericVerifierCanonicalFinishGraph
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult) : Prop :=
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  let currentState : CompactNumericVerifierState := (payload, none)
  let nextState := compactNumericFinishState payload
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  ∃ currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness,
    currentCoordinates.start = 0 ∧
    currentCoordinates.finish = currentTokens.length ∧
    nextCoordinates.start = currentTokens.length ∧
    nextCoordinates.finish = currentTokens.length + nextTokens.length ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 currentTokens.length currentState
      currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentTokens.length (currentTokens.length + nextTokens.length)
      nextState nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierFinishRows
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.start currentCoordinates.valuesFinish
      currentCoordinates.proofCount currentCoordinates.certificateCount
      currentCoordinates.taskCount currentCoordinates.valueCount
      currentCoordinates.valueBoundary currentSizeWitness.valueValueBound
      currentCoordinates.statusTag
      nextCoordinates.start nextCoordinates.valuesFinish
      nextCoordinates.proofCount nextCoordinates.certificateCount
      nextCoordinates.taskCount nextCoordinates.valueCount
      nextCoordinates.statusTag nextCoordinates.statusBool

theorem CompactNumericVerifierCanonicalFinishGraph.exists
    (proofTokens certificateTokens : List Nat)
    (values : List CompactNumericChildResult) :
    CompactNumericVerifierCanonicalFinishGraph
      proofTokens certificateTokens values := by
  let payload : CompactNumericRunningPayload :=
    ((proofTokens, certificateTokens), ([], values))
  let currentState : CompactNumericVerifierState := (payload, none)
  let nextState := compactNumericFinishState payload
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hlayoutsRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState []
  have hlayouts :
      CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 currentTokens.length currentState ∧
        CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          currentTokens.length (currentTokens.length + nextTokens.length)
          nextState := by
    simpa only [currentTokens, nextTokens, tokens, width,
      List.append_nil] using hlayoutsRaw
  rcases hlayouts with ⟨hcurrentLayout, hnextLayout⟩
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hcurrentLayout with
    ⟨currentCoordinates, currentSizeWitness, hcurrentPackage⟩
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hnextLayout with
    ⟨nextCoordinates, nextSizeWitness, hnextPackage⟩
  have hcurrentPackageOutput := hcurrentPackage
  have hnextPackageOutput := hnextPackage
  dsimp only [currentState, payload] at hcurrentPackage
  have hnextStateShape : nextState =
      (((proofTokens, certificateTokens),
        (([] : List CompactNumericVerifierTask), values)), nextState.2) := by
    by_cases hguard :
        proofTokens = [] ∧ certificateTokens = [] ∧ values.length = 1
    · simp [nextState, payload, compactNumericFinishState, hguard]
    · simp [nextState, payload, compactNumericFinishState, hguard]
  rw [hnextStateShape] at hnextPackage
  have hcurrentPackageSaved := hcurrentPackage
  have hnextPackageSaved := hnextPackage
  rcases hcurrentPackage with
    ⟨_hcurrentStart, _hcurrentFinish,
      hcurrentProof, hcurrentCertificate,
      hcurrentTaskLayout, _hcurrentTaskRows,
      hcurrentValueLayout, hcurrentValueRows,
      hcurrentTaskCount, hcurrentValueCount,
      _hcurrentTaskTableWidth, _hcurrentTaskValueBound,
      _hcurrentValueTableWidth, hcurrentValueValueBound,
      _hcurrentStatus, hcurrentCore⟩
  rcases hnextPackage with
    ⟨_hnextStart, _hnextFinish,
      hnextProof, hnextCertificate,
      hnextTaskLayout, _hnextTaskRows,
      hnextValueLayout, hnextValueRows,
      hnextTaskCount, hnextValueCount,
      _hnextTaskTableWidth, _hnextTaskValueBound,
      _hnextValueTableWidth, _hnextValueValueBound,
      _hnextStatus, hnextCore⟩
  dsimp only at hcurrentProof
  dsimp only at hcurrentCertificate
  dsimp only at hcurrentTaskLayout
  dsimp only at hcurrentValueLayout
  dsimp only at hcurrentValueRows
  dsimp only at hcurrentTaskCount
  dsimp only at hcurrentValueCount
  dsimp only at hnextProof
  dsimp only at hnextCertificate
  dsimp only at hnextTaskLayout
  dsimp only at hnextValueLayout
  dsimp only at hnextValueRows
  dsimp only at hnextTaskCount
  dsimp only at hnextValueCount
  rcases hcurrentCore with
    ⟨hcurrentProofSlice, hcurrentCertificateSlice,
      _hcurrentTaskStructure, _hcurrentTaskGraph,
      _hcurrentTaskBoundarySizeEq, _hcurrentTaskBoundarySize,
      _hcurrentValueStructure, _hcurrentValueGraph,
      hcurrentValueBoundarySizeEq, hcurrentValueBoundarySize,
      _hcurrentOption, _hcurrentCoreStatus⟩
  rcases hnextCore with
    ⟨hnextProofSlice, hnextCertificateSlice,
      _hnextTaskStructure, _hnextTaskGraph,
      _hnextTaskBoundarySizeEq, _hnextTaskBoundarySize,
      _hnextValueStructure, _hnextValueGraph,
      hnextValueBoundarySizeEq, hnextValueBoundarySize,
      _hnextOption, _hnextCoreStatus⟩
  have hcurrentProofCountReal : currentCoordinates.proofCount =
      proofTokens.length := by
    have hfinish : currentCoordinates.proofFinish =
        currentCoordinates.start + 1 + proofTokens.length := by
      simpa only using
        (CompactAdditiveNatListDirectLayout.finish_eq hcurrentProof)
    rcases hcurrentProofSlice with
      ⟨bodyStart, _hbodyBound, hheader, hsliceFinish⟩
    have hbodyStart : bodyStart = currentCoordinates.start + 1 :=
      hheader.1.2.1
    omega
  have hnextProofCountReal : nextCoordinates.proofCount =
      proofTokens.length := by
    have hfinish : nextCoordinates.proofFinish =
        nextCoordinates.start + 1 + proofTokens.length := by
      simpa only using
        (CompactAdditiveNatListDirectLayout.finish_eq hnextProof)
    rcases hnextProofSlice with
      ⟨bodyStart, _hbodyBound, hheader, hsliceFinish⟩
    have hbodyStart : bodyStart = nextCoordinates.start + 1 :=
      hheader.1.2.1
    omega
  have hcurrentCertificateCountReal :
      currentCoordinates.certificateCount = certificateTokens.length := by
    have hfinish : currentCoordinates.certificateFinish =
        currentCoordinates.proofFinish + 1 + certificateTokens.length := by
      simpa only using
        (CompactAdditiveNatListDirectLayout.finish_eq hcurrentCertificate)
    rcases hcurrentCertificateSlice with
      ⟨bodyStart, _hbodyBound, hheader, hsliceFinish⟩
    have hbodyStart : bodyStart = currentCoordinates.proofFinish + 1 :=
      hheader.1.2.1
    omega
  have hnextCertificateCountReal :
      nextCoordinates.certificateCount = certificateTokens.length := by
    have hfinish : nextCoordinates.certificateFinish =
        nextCoordinates.proofFinish + 1 + certificateTokens.length := by
      simpa only using
        (CompactAdditiveNatListDirectLayout.finish_eq hnextCertificate)
    rcases hnextCertificateSlice with
      ⟨bodyStart, _hbodyBound, hheader, hsliceFinish⟩
    have hbodyStart : bodyStart = nextCoordinates.proofFinish + 1 :=
      hheader.1.2.1
    omega
  have hproofSlices : CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.start currentCoordinates.proofFinish
      nextCoordinates.start nextCoordinates.proofFinish :=
    CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hcurrentProof hnextProof rfl
  have hcertificateSlices : CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.proofFinish currentCoordinates.certificateFinish
      nextCoordinates.proofFinish nextCoordinates.certificateFinish :=
    CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hcurrentCertificate hnextCertificate rfl
  have htaskSlices : CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.certificateFinish currentCoordinates.tasksFinish
      nextCoordinates.certificateFinish nextCoordinates.tasksFinish :=
    CompactAdditiveStructuredListLayout.emptySlicesEq
      hcurrentTaskLayout hnextTaskLayout
  have hcurrentValueSize : Nat.size currentCoordinates.valueBoundary ≤
      (values.length + 1) * tokens.length := by
    rw [← hcurrentValueBoundarySizeEq]
    simpa only [hcurrentValueCount] using hcurrentValueBoundarySize
  have hnextValueSize : Nat.size nextCoordinates.valueBoundary ≤
      (values.length + 1) * tokens.length := by
    rw [← hnextValueBoundarySizeEq]
    simpa only [hnextValueCount] using hnextValueBoundarySize
  have hcurrentValues : CompactNumericChildResultListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.tasksFinish currentCoordinates.valuesFinish
      values :=
    ⟨currentCoordinates.valueBoundary, hcurrentValueLayout,
      hcurrentValueRows, hcurrentValueSize⟩
  have hnextValues : CompactNumericChildResultListDirectLayout
      (compactFixedWidthTableCode width tokens) width tokens.length
      nextCoordinates.tasksFinish nextCoordinates.valuesFinish values :=
    ⟨nextCoordinates.valueBoundary, hnextValueLayout,
      hnextValueRows, hnextValueSize⟩
  have hvalueSlices : CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.tasksFinish currentCoordinates.valuesFinish
      nextCoordinates.tasksFinish nextCoordinates.valuesFinish :=
    CompactNumericChildResultListDirectLayout.slicesEq_of_eq
      hcurrentValues hnextValues rfl
  have hpayloadSlices : CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.start currentCoordinates.valuesFinish
      nextCoordinates.start nextCoordinates.valuesFinish :=
    CompactFixedWidthTokenSlicesEq.append
      (CompactFixedWidthTokenSlicesEq.append
        (CompactFixedWidthTokenSlicesEq.append
          hproofSlices hcertificateSlices) htaskSlices) hvalueSlices
  have hcurrentStatusTag : currentCoordinates.statusTag = 0 :=
    hcurrentPackageSaved.statusTag_eq_zero rfl
  have hcurrentTaskCountZero : currentCoordinates.taskCount = 0 := by
    simpa only [List.length_nil] using hcurrentTaskCount
  have hnextTaskCountZero : nextCoordinates.taskCount = 0 := by
    simpa only [List.length_nil] using hnextTaskCount
  have hcurrentValueCountReal : currentCoordinates.valueCount =
      values.length := by
    simpa only using hcurrentValueCount
  have hnextValueCountReal : nextCoordinates.valueCount =
      values.length := by
    simpa only using hnextValueCount
  have hproofCountEq : nextCoordinates.proofCount =
      currentCoordinates.proofCount := by omega
  have hcertificateCountEq : nextCoordinates.certificateCount =
      currentCoordinates.certificateCount := by omega
  have htaskCountEq : nextCoordinates.taskCount =
      currentCoordinates.taskCount := by
    rw [hnextTaskCountZero, hcurrentTaskCountZero]
  have hvalueCountEq : nextCoordinates.valueCount =
      currentCoordinates.valueCount := by
    rw [hnextValueCountReal, hcurrentValueCountReal]
  by_cases hguard : proofTokens = [] ∧ certificateTokens = [] ∧
      values.length = 1
  · let finalResult :=
      (values.head?.getD compactNumericDefaultChildResult).2
    have hfullGuard : payload.1.1 = [] ∧ payload.1.2 = [] ∧
        payload.2.1 = [] ∧ payload.2.2.length = 1 := by
      exact ⟨hguard.1, hguard.2.1, rfl, hguard.2.2⟩
    have hnextStateEq : nextState = (payload, some finalResult) := by
      dsimp only [nextState]
      simp only [compactNumericFinishState, hfullGuard]
      rfl
    have hnextStatus := hnextPackageSaved.statusTagBool_eq_some
      (congrArg Prod.snd hnextStateEq)
    have hindex : 0 < values.length := by omega
    have hheadBool : finalResult = (values.getI 0).2 := by
      cases values with
      | nil => omega
      | cons value tail => rfl
    have hrowRaw :=
      CompactAdditiveStructuredListElementRowLayouts.childResultBoundedRowWithBool
        hcurrentValueRows 0 hindex
    have hrow : CompactNumericChildResultBoundedRowWithBool
        (compactFixedWidthTableCode width tokens) width tokens.length
        currentCoordinates.valueBoundary currentSizeWitness.valueValueBound
        0 nextCoordinates.statusBool := by
      rw [hcurrentValueValueBound]
      rw [hnextStatus.2]
      simpa only [hheadBool] using hrowRaw
    have hfinish : CompactNumericVerifierFinishRows
        (compactFixedWidthTableCode width tokens) width tokens.length
        currentCoordinates.start currentCoordinates.valuesFinish
        currentCoordinates.proofCount currentCoordinates.certificateCount
        currentCoordinates.taskCount currentCoordinates.valueCount
        currentCoordinates.valueBoundary currentSizeWitness.valueValueBound
        currentCoordinates.statusTag
        nextCoordinates.start nextCoordinates.valuesFinish
        nextCoordinates.proofCount nextCoordinates.certificateCount
        nextCoordinates.taskCount nextCoordinates.valueCount
        nextCoordinates.statusTag nextCoordinates.statusBool := by
      refine ⟨hcurrentStatusTag, hcurrentTaskCountZero, hpayloadSlices,
        hproofCountEq, hcertificateCountEq, htaskCountEq, hvalueCountEq,
        hnextStatus.1, Or.inl ⟨?_, ?_, hcurrentTaskCountZero, ?_, hrow⟩⟩
      · simpa [hguard.1] using hcurrentProofCountReal
      · simpa [hguard.2.1] using hcurrentCertificateCountReal
      · omega
    dsimp only [CompactNumericVerifierCanonicalFinishGraph]
    exact ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      hcurrentPackageSaved.1, hcurrentPackageSaved.2.1,
      hnextPackageSaved.1, hnextPackageSaved.2.1,
      hcurrentPackageOutput, hnextPackageOutput, hfinish⟩
  · have hnextStateEq : nextState = (payload, some false) := by
      have hfullGuard :
          ¬(payload.1.1 = [] ∧ payload.1.2 = [] ∧
            payload.2.1 = [] ∧ payload.2.2.length = 1) := by
        intro hfull
        exact hguard ⟨hfull.1, hfull.2.1, hfull.2.2.2⟩
      dsimp only [nextState]
      simp only [compactNumericFinishState, hfullGuard, if_false]
    have hnextStatus := hnextPackageSaved.statusTagBool_eq_some
      (congrArg Prod.snd hnextStateEq)
    have hbadCounts : currentCoordinates.proofCount ≠ 0 ∨
        currentCoordinates.certificateCount ≠ 0 ∨
        currentCoordinates.taskCount ≠ 0 ∨
        currentCoordinates.valueCount ≠ 1 := by
      by_contra hnot
      push Not at hnot
      apply hguard
      refine ⟨?_, ?_, ?_⟩
      · apply List.eq_nil_of_length_eq_zero
        omega
      · apply List.eq_nil_of_length_eq_zero
        omega
      · omega
    have hnextBool : nextCoordinates.statusBool = 0 := by
      simpa [compactAdditiveBoolTag] using hnextStatus.2
    have hfinish : CompactNumericVerifierFinishRows
        (compactFixedWidthTableCode width tokens) width tokens.length
        currentCoordinates.start currentCoordinates.valuesFinish
        currentCoordinates.proofCount currentCoordinates.certificateCount
        currentCoordinates.taskCount currentCoordinates.valueCount
        currentCoordinates.valueBoundary currentSizeWitness.valueValueBound
        currentCoordinates.statusTag
        nextCoordinates.start nextCoordinates.valuesFinish
        nextCoordinates.proofCount nextCoordinates.certificateCount
        nextCoordinates.taskCount nextCoordinates.valueCount
        nextCoordinates.statusTag nextCoordinates.statusBool :=
      ⟨hcurrentStatusTag, hcurrentTaskCountZero, hpayloadSlices,
        hproofCountEq, hcertificateCountEq, htaskCountEq, hvalueCountEq,
        hnextStatus.1, Or.inr ⟨hbadCounts, hnextBool⟩⟩
    dsimp only [CompactNumericVerifierCanonicalFinishGraph]
    exact ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      hcurrentPackageSaved.1, hcurrentPackageSaved.2.1,
      hnextPackageSaved.1, hnextPackageSaved.2.1,
      hcurrentPackageOutput, hnextPackageOutput, hfinish⟩

#print axioms CompactNumericVerifierCanonicalFinishGraph.exists

end FoundationCompactNumericListedDirectVerifierFinishCompleteness
