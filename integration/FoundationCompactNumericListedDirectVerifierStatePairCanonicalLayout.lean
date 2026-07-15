import integration.FoundationCompactNumericListedDirectVerifierStateLayout

/-!
# Canonical shared layout for two verifier states

Two arbitrary verifier states occupy consecutive slices of one canonical token
table.  An arbitrary suffix is retained so rule-specific transform traces can be
placed in the same table without rebuilding the state layouts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectVerifierStateLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericSequentValuePrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNumericNodeFieldsAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericChildResultAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactNumericVerifierStateAdditiveCodec

theorem compactNumericVerifierStatePairPrefixLayouts_canonical
    (currentState nextState : CompactNumericVerifierState)
    (backTokens : List Nat) :
    let currentTokens := compactAdditiveEncode currentState
    let nextTokens := compactAdditiveEncode nextState
    let tokens := currentTokens ++ nextTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    CompactNumericVerifierStateDirectLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length 0 currentTokens.length currentState ∧
      CompactNumericVerifierStateDirectLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length currentTokens.length
          (currentTokens.length + nextTokens.length) nextState := by
  let currentTokens := compactAdditiveEncode currentState
  let nextTokens := compactAdditiveEncode nextState
  let tokens := currentTokens ++ nextTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  have hcurrentRaw := compactNumericVerifierStateDirectLayout_canonical
    [] currentState (nextTokens ++ backTokens)
  have hnextRaw := compactNumericVerifierStateDirectLayout_canonical
    currentTokens nextState backTokens
  dsimp only at hcurrentRaw hnextRaw ⊢
  have hcurrent : CompactNumericVerifierStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length 0 currentTokens.length currentState := by
    simpa only [List.nil_append, List.length_nil, Nat.zero_add,
      currentTokens, nextTokens, tokens, width, List.append_assoc] using
      hcurrentRaw
  have hnext : CompactNumericVerifierStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length currentTokens.length
        (currentTokens.length + nextTokens.length) nextState := by
    simpa only [List.append_nil, currentTokens, nextTokens, tokens, width,
      List.append_assoc] using hnextRaw
  exact ⟨hcurrent, hnext⟩

theorem compactNumericVerifierStatePairPrefix_tokenCount_pos
    (currentState nextState : CompactNumericVerifierState)
    (backTokens : List Nat) :
    1 ≤ (compactAdditiveEncode currentState ++
      compactAdditiveEncode nextState ++ backTokens).length := by
  have hcurrent : compactAdditiveEncode currentState ≠ [] :=
    compactAdditiveEncode_ne_nil currentState
  have hcurrentPos : 0 < (compactAdditiveEncode currentState).length :=
    List.length_pos_iff.mpr hcurrent
  simp only [List.length_append]
  omega

#print axioms compactNumericVerifierStatePairPrefixLayouts_canonical
#print axioms compactNumericVerifierStatePairPrefix_tokenCount_pos

end FoundationCompactNumericListedDirectVerifierStatePairCanonicalLayout
