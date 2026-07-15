import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness

/-!
# Canonical common frame for a concrete verifier combine step

The current and next states are encoded consecutively in one fixed-width token
table.  Rule-specific tokens may follow them.  The two typed layouts then
construct the complete common combine frame without any layout premise.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierCombineCanonicalFrameCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierCombineStateFrameRowsCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

theorem CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back
    (proofTokens certificateTokens : List Nat)
    (task : CompactNumericVerifierTask)
    (tasks : List CompactNumericVerifierTask)
    (source target : List CompactNumericChildResult)
    (nextStatus : Option Bool)
    (backTokens : List Nat)
    (htaskNe : task.1 ≠ 10) :
    let currentState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (task :: tasks, source)), none)
    let nextState : CompactNumericVerifierState :=
      (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    ∃ currentCoordinates nextCoordinates
        currentSizeWitness nextSizeWitness taskCoordinates taskSizeWitness,
      CompactNumericVerifierCombineCanonicalFramePackage
        (compactFixedWidthTableCode width tokens) width tokens.length
        0 currentTokens.length currentTokens.length
        (currentTokens.length + nextTokens.length)
        proofTokens certificateTokens task tasks source target nextStatus
        currentCoordinates nextCoordinates currentSizeWitness nextSizeWitness
        taskCoordinates taskSizeWitness := by
  let currentState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (task :: tasks, source)), none)
  let nextState : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, target)), nextStatus)
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hpairsRaw := compactNumericVerifierStatePairPrefixLayouts_canonical
    currentState nextState backTokens
  have hpairs :
      CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length 0 currentTokens.length currentState ∧
        CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length currentTokens.length
            (currentTokens.length + nextTokens.length) nextState := by
    simpa only [currentTokens, nextTokens, tokens, width] using hpairsRaw
  rcases CompactNumericVerifierCombineCanonicalFramePackage.exists_of_layouts
      hpairs.1 hpairs.2 htaskNe with
    ⟨currentCoordinates, nextCoordinates,
      currentSizeWitness, nextSizeWitness,
      taskCoordinates, taskSizeWitness, hframe⟩
  exact ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    taskCoordinates, taskSizeWitness, hframe⟩

#print axioms
  CompactNumericVerifierCombineCanonicalFramePackage.exists_canonical_with_back

end FoundationCompactNumericListedDirectVerifierCombineCanonicalFrameCompleteness
