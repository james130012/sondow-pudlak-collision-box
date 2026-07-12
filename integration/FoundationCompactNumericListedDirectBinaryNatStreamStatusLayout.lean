import integration.FoundationCompactNumericListedDirectAdditiveTypeCanonical

/-!
# Direct layout of the nested binary-stream status

`BinaryNatStreamStatus` is `Option (Option (List Nat))`.  The two option tags
and the optional output-token list are aligned to one common token table and
one exact status interval.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAdditiveTypeCanonical

def CompactBinaryNatStreamStatusDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (status : Option (Option (List Nat))) : Prop :=
  ∃ outerPayloadStart,
    CompactAdditiveOptionLayout
      tokenTable width tokenCount start
      (compactAdditiveOptionTag status) outerPayloadStart finish ∧
    match status with
    | none => True
    | some inner =>
        ∃ innerPayloadStart,
          CompactAdditiveOptionLayout
            tokenTable width tokenCount outerPayloadStart
            (compactAdditiveOptionTag inner) innerPayloadStart finish ∧
          match inner with
          | none => True
          | some outputTokens =>
              ∃ outputBoundaryTable,
                CompactAdditiveStructuredListLayout
                  tokenTable width tokenCount innerPayloadStart
                  outputTokens.length finish outputBoundaryTable ∧
                Nat.size outputBoundaryTable ≤
                  (outputTokens.length + 1) * tokenCount

theorem compactBinaryNatStreamStatusDirectLayout_canonical
    (frontTokens : List Nat) (status : Option (Option (List Nat)))
    (backTokens : List Nat) :
    let statusTokens := compactAdditiveEncode status
    let tokens := frontTokens ++ statusTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + statusTokens.length
    CompactBinaryNatStreamStatusDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish status := by
  let statusTokens := compactAdditiveEncode status
  let tokens := frontTokens ++ statusTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let finish := start + statusTokens.length
  let outerPayloadStart := start + 1
  have houter := compactAdditiveOptionLayout_canonical
    frontTokens status backTokens
  cases status with
  | none =>
      refine ⟨outerPayloadStart, ?_, trivial⟩
      simpa [statusTokens, tokens, width, start, finish,
        outerPayloadStart] using houter
  | some inner =>
      let innerFront := frontTokens ++ [1]
      let innerPayloadStart := outerPayloadStart + 1
      have hinnerRaw := compactAdditiveOptionLayout_canonical
        innerFront inner backTokens
      have hstatusTokens : statusTokens =
          1 :: compactAdditiveEncode inner := by rfl
      have hinnerTokens :
          innerFront ++ compactAdditiveEncode inner ++ backTokens =
            tokens := by
        simp [innerFront, tokens, statusTokens, hstatusTokens,
          List.append_assoc]
      dsimp only at hinnerRaw
      rw [hinnerTokens] at hinnerRaw
      have hinnerStart : innerFront.length = outerPayloadStart := by
        simp [innerFront, outerPayloadStart, start]
      have hinnerPayloadStart : innerFront.length + 1 =
          innerPayloadStart := by
        simp [innerPayloadStart, hinnerStart]
      have hinnerFinish :
          innerFront.length + (compactAdditiveEncode inner).length =
            finish := by
        simp [innerFront, finish, start, statusTokens, hstatusTokens]
        omega
      have hinnerPayloadDirect : outerPayloadStart + 1 =
          innerPayloadStart := by
        omega
      have hinnerFinishDirect :
          outerPayloadStart + (compactAdditiveEncode inner).length =
            finish := by
        omega
      have hinner : CompactAdditiveOptionLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length outerPayloadStart
          (compactAdditiveOptionTag inner) innerPayloadStart finish := by
        simpa only [width, hinnerStart, hinnerPayloadDirect,
          hinnerFinishDirect] using hinnerRaw
      have houter' : CompactAdditiveOptionLayout
          (compactFixedWidthTableCode width tokens)
          width tokens.length start 1 outerPayloadStart finish := by
        simpa [statusTokens, tokens, width, start, finish,
          outerPayloadStart, compactAdditiveOptionTag] using houter
      refine ⟨outerPayloadStart, houter', ?_⟩
      cases inner with
      | none =>
          exact ⟨innerPayloadStart, hinner, trivial⟩
      | some outputTokens =>
          let outputFront := frontTokens ++ [1, 1]
          have houtputRaw := compactAdditiveStructuredListLayout_canonical
            outputFront outputTokens backTokens
          rcases houtputRaw with
            ⟨outputBoundaryTable, houtputLayout, houtputSize⟩
          have houtputTokenEq :
              outputFront ++ compactAdditiveEncode outputTokens ++
                  backTokens = tokens := by
            simp [outputFront, tokens, statusTokens,
              List.append_assoc]
          rw [houtputTokenEq] at houtputLayout houtputSize
          have houtputStart : outputFront.length =
              innerPayloadStart := by
            simp [outputFront, innerPayloadStart,
              outerPayloadStart, start]
          have houtputFinish :
              outputFront.length +
                  (compactAdditiveEncode outputTokens).length = finish := by
            simp [outputFront, finish, start, statusTokens]
            omega
          have houtputFinishDirect :
              innerPayloadStart +
                  (compactAdditiveEncode outputTokens).length = finish := by
            omega
          have houtputLayout' : CompactAdditiveStructuredListLayout
              (compactFixedWidthTableCode width tokens)
              width tokens.length innerPayloadStart outputTokens.length
              finish outputBoundaryTable := by
            simpa only [width, houtputStart, houtputFinishDirect] using
              houtputLayout
          refine ⟨innerPayloadStart, hinner,
            outputBoundaryTable, houtputLayout', ?_⟩
          exact houtputSize

#print axioms compactBinaryNatStreamStatusDirectLayout_canonical

end FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
