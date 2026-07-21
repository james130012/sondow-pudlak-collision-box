import integration.FoundationCompactNumericListedDirectVerifierHaltedExactness
import integration.FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
import integration.FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

/-!
# Canonical converse for the halted verifier branch

Two copies of the same halted state are placed consecutively in one canonical
token table.  Their complete token slices agree, so the bounded halted row is
constructed without accepting a slice-equality witness as input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierHaltedCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierStateLayout
open FoundationCompactNumericListedDirectVerifierStateFormula
open FoundationCompactNumericListedDirectVerifierHaltedFormula
open FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
open FoundationCompactNumericListedDirectVerifierStateCoreCompleteness

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

def CompactNumericVerifierCanonicalHaltedGraph
    (state : CompactNumericVerifierState) : Prop :=
  let stateTokens := compactAdditiveEncode state
  let tokens := stateTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  ∃ currentCoordinates nextCoordinates
      currentSizeWitness nextSizeWitness,
    currentCoordinates.start = 0 ∧
    currentCoordinates.finish = stateTokens.length ∧
    nextCoordinates.start = stateTokens.length ∧
    nextCoordinates.finish = stateTokens.length + stateTokens.length ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 stateTokens.length state currentCoordinates currentSizeWitness ∧
    CompactNumericVerifierStateCanonicalCorePackage
      (compactFixedWidthTableCode width tokens) width tokens.length
      stateTokens.length (stateTokens.length + stateTokens.length)
      state nextCoordinates nextSizeWitness ∧
    CompactNumericVerifierHaltedRows
      (compactFixedWidthTableCode width tokens) width tokens.length
      currentCoordinates.start currentCoordinates.finish
      currentCoordinates.statusTag
      nextCoordinates.start nextCoordinates.finish

theorem CompactNumericVerifierCanonicalHaltedGraph.exists_of_some
    (proofTokens certificateTokens : List Nat)
    (tasks : List CompactNumericVerifierTask)
    (values : List CompactNumericChildResult)
    (result : Bool) :
    CompactNumericVerifierCanonicalHaltedGraph
      (((proofTokens, certificateTokens), (tasks, values)), some result) := by
  let state : CompactNumericVerifierState :=
    (((proofTokens, certificateTokens), (tasks, values)), some result)
  let stateTokens := compactAdditiveEncode state
  let tokens := stateTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  change CompactNumericVerifierCanonicalHaltedGraph state
  have hlayouts := compactNumericVerifierStatePairPrefixLayouts_canonical
    state state []
  dsimp only at hlayouts
  have hlayouts' :
      CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          0 stateTokens.length state ∧
        CompactNumericVerifierStateDirectLayout
          (compactFixedWidthTableCode width tokens) width tokens.length
          stateTokens.length (stateTokens.length + stateTokens.length) state := by
    simpa only [stateTokens, tokens, width, List.append_nil] using hlayouts
  rcases hlayouts' with ⟨hcurrentLayout, hnextLayout⟩
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hcurrentLayout with
    ⟨currentCoordinates, currentSizeWitness, hcurrentPackage⟩
  rcases CompactNumericVerifierStateDirectLayout.toCanonicalCorePackage
      hnextLayout with
    ⟨nextCoordinates, nextSizeWitness, hnextPackage⟩
  have hcurrentStatus := hcurrentPackage.statusTagBool_eq_some rfl
  have hslices : CompactFixedWidthTokenSlicesEq
      (compactFixedWidthTableCode width tokens) width tokens.length
      0 stateTokens.length stateTokens.length
        (stateTokens.length + stateTokens.length) := by
    have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
      intro token htoken
      exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
    have hsource : 0 + stateTokens.length ≤ tokens.length := by
      simp [tokens]
    have htarget : stateTokens.length + stateTokens.length ≤
        tokens.length := by
      simp [tokens]
    have hvalues : ∀ offset < stateTokens.length,
        tokens.getI (0 + offset) =
          tokens.getI (stateTokens.length + offset) := by
      intro offset hoffset
      simp only [Nat.zero_add]
      rw [List.getI_append stateTokens stateTokens offset (by omega)]
      rw [List.getI_append_right stateTokens stateTokens
        (stateTokens.length + offset) (by omega)]
      simp only [Nat.add_sub_cancel_left]
    simpa only [Nat.zero_add] using
      compactFixedWidthTokenSlicesEq_tableCode
        tokens width 0 stateTokens.length stateTokens.length
          hwidth hsource htarget hvalues
  dsimp only [CompactNumericVerifierCanonicalHaltedGraph]
  refine ⟨currentCoordinates, nextCoordinates,
    currentSizeWitness, nextSizeWitness,
    hcurrentPackage.1, hcurrentPackage.2.1,
    hnextPackage.1, hnextPackage.2.1,
    hcurrentPackage, hnextPackage, ?_⟩
  exact ⟨hcurrentStatus.1, by
    simpa only [hcurrentPackage.1, hcurrentPackage.2.1,
      hnextPackage.1, hnextPackage.2.1] using hslices⟩

#print axioms CompactNumericVerifierCanonicalHaltedGraph.exists_of_some

end FoundationCompactNumericListedDirectVerifierHaltedCompleteness
