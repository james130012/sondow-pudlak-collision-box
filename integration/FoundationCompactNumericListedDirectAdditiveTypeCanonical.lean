import integration.FoundationCompactNumericListedDirectTracePackedStreamListLayouts

/-!
# Canonical witnesses for direct additive type layouts

Real additive encodings of `Bool`, `Option`, and products are shown to satisfy
the direct bounded layouts at their exact cursors inside arbitrary surrounding
token streams.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectAdditiveTypeCanonical

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTraceComponentTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts

def compactAdditiveBoolTag (value : Bool) : Nat :=
  if value then 1 else 0

def compactAdditiveOptionTag {α : Type*} : Option α → Nat
  | none => 0
  | some _ => 1

theorem compactAdditiveBoolSlice_canonical
    (frontTokens : List Nat) (value : Bool) (backTokens : List Nat) :
    let boolTokens := compactAdditiveEncode value
    let tokens := frontTokens ++ boolTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    CompactAdditiveBoolSlice
      (compactFixedWidthTableCode width tokens)
      width tokens.length start (compactAdditiveBoolTag value) (start + 1) := by
  let boolTokens := compactAdditiveEncode value
  let tokens := frontTokens ++ boolTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  have hboolTokens : boolTokens = [compactAdditiveBoolTag value] := by
    cases value <;> rfl
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hstartLt : start < tokens.length := by
    rw [show tokens = frontTokens ++ boolTokens ++ backTokens by rfl]
    rw [hboolTokens]
    simp [start]
  have htokenAt : tokens.getI start = compactAdditiveBoolTag value := by
    rw [show tokens = frontTokens ++ boolTokens ++ backTokens by rfl]
    rw [hboolTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens
      ([compactAdditiveBoolTag value] ++ backTokens)
      frontTokens.length (by rfl)]
    simp
  have hcellRaw := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hcell : CompactAdditiveTokenCell
      (compactFixedWidthTableCode width tokens)
      width tokens.length start (compactAdditiveBoolTag value) (start + 1) := by
    simpa [htokenAt] using hcellRaw
  refine ⟨hcell, ?_⟩
  cases value <;> simp [compactAdditiveBoolTag]

theorem compactAdditiveProductSplit_canonical
    {α β : Type*} [Primcodable α] [Primcodable β]
    [CompactAdditiveTokenCodec α] [CompactAdditiveTokenCodec β]
    [CompactAdditiveNonemptyCodec α] [CompactAdditiveNonemptyCodec β]
    (frontTokens : List Nat) (left : α) (right : β)
    (backTokens : List Nat) :
    let pairTokens := compactAdditiveEncode (left, right)
    let tokens := frontTokens ++ pairTokens ++ backTokens
    let start := frontTokens.length
    let middle := start + (compactAdditiveEncode left).length
    let finish := middle + (compactAdditiveEncode right).length
    CompactAdditiveProductSplit tokens.length start middle finish := by
  let pairTokens := compactAdditiveEncode (left, right)
  let tokens := frontTokens ++ pairTokens ++ backTokens
  let start := frontTokens.length
  let middle := start + (compactAdditiveEncode left).length
  let finish := middle + (compactAdditiveEncode right).length
  have hpairTokens : pairTokens =
      compactAdditiveEncode left ++ compactAdditiveEncode right := by
    simp [pairTokens]
  have hleft : 0 < (compactAdditiveEncode left).length :=
    List.length_pos_iff.mpr (compactAdditiveEncode_ne_nil left)
  have hright : 0 < (compactAdditiveEncode right).length :=
    List.length_pos_iff.mpr (compactAdditiveEncode_ne_nil right)
  have hfinish : finish ≤ tokens.length := by
    rw [show tokens = frontTokens ++ pairTokens ++ backTokens by rfl]
    rw [hpairTokens]
    simp [finish, middle, start]
    omega
  exact compactAdditiveProductSplit_of_lengths
    tokens.length start (compactAdditiveEncode left).length
      (compactAdditiveEncode right).length hleft hright hfinish

theorem compactAdditiveOptionLayout_canonical
    {α : Type*} [Primcodable α] [CompactAdditiveTokenCodec α]
    [CompactAdditiveNonemptyCodec α]
    (frontTokens : List Nat) (value : Option α) (backTokens : List Nat) :
    let optionTokens := compactAdditiveEncode value
    let tokens := frontTokens ++ optionTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let payloadStart := start + 1
    let finish := start + optionTokens.length
    CompactAdditiveOptionLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start (compactAdditiveOptionTag value)
      payloadStart finish := by
  let optionTokens := compactAdditiveEncode value
  let tokens := frontTokens ++ optionTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let payloadStart := start + 1
  let finish := start + optionTokens.length
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  cases value with
  | none =>
      have hoptionTokens : optionTokens = [0] := by rfl
      have hstartLt : start < tokens.length := by
        rw [show tokens = frontTokens ++ optionTokens ++ backTokens by rfl]
        rw [hoptionTokens]
        simp
        dsimp only [start]
        omega
      have htokenAt : tokens.getI start = 0 := by
        rw [show tokens = frontTokens ++ optionTokens ++ backTokens by rfl]
        rw [hoptionTokens, List.append_assoc]
        rw [List.getI_append_right frontTokens ([0] ++ backTokens)
          frontTokens.length (by rfl)]
        simp
      have hcellRaw := compactAdditiveTokenCell_canonical
        tokens width start hstartLt hwidth
      have hcell : CompactAdditiveTokenCell
          (compactFixedWidthTableCode width tokens)
          width tokens.length start 0 payloadStart := by
        simpa [payloadStart, htokenAt] using hcellRaw
      refine ⟨hcell, Or.inl ⟨rfl, ?_⟩⟩
      simp
  | some inner =>
      have hoptionTokens : optionTokens =
          1 :: compactAdditiveEncode inner := by rfl
      have hstartLt : start < tokens.length := by
        rw [show tokens = frontTokens ++ optionTokens ++ backTokens by rfl]
        rw [hoptionTokens]
        simp
        dsimp only [start]
        omega
      have htokenAt : tokens.getI start = 1 := by
        rw [show tokens = frontTokens ++ optionTokens ++ backTokens by rfl]
        rw [hoptionTokens, List.append_assoc]
        rw [List.getI_append_right frontTokens
          ((1 :: compactAdditiveEncode inner) ++ backTokens)
          frontTokens.length (by rfl)]
        simp
      have hcellRaw := compactAdditiveTokenCell_canonical
        tokens width start hstartLt hwidth
      have hcell : CompactAdditiveTokenCell
          (compactFixedWidthTableCode width tokens)
          width tokens.length start 1 payloadStart := by
        simpa [payloadStart, htokenAt] using hcellRaw
      have hinnerPos : 0 < (compactAdditiveEncode inner).length :=
        List.length_pos_iff.mpr (compactAdditiveEncode_ne_nil inner)
      have hpayload : payloadStart < finish := by
        simp [payloadStart, finish, start, optionTokens, hoptionTokens]
        omega
      have hfinish : finish ≤ tokens.length := by
        rw [show tokens = frontTokens ++ optionTokens ++ backTokens by rfl]
        simp [finish, start]
      refine ⟨hcell, Or.inr ⟨rfl, hpayload, hfinish⟩⟩

#print axioms compactAdditiveBoolSlice_canonical
#print axioms compactAdditiveProductSplit_canonical
#print axioms compactAdditiveOptionLayout_canonical

end FoundationCompactNumericListedDirectAdditiveTypeCanonical
