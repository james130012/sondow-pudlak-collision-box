import integration.FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public bounds for outer proof-root failure

The proof-root parser fails before entering a child parser exactly on empty
input or on a leading tag greater than nine.  This file repeats both canonical
table constructions while retaining an explicit input-weight bound for every
coordinate exposed by the bounded endpoint formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectProofRootOuterFailureBoundedFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

private theorem compactAdditiveTokenList_length_le_weight
    (tokens : List Nat) :
    tokens.length <= compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

private theorem natSize_add_le (left right : Nat) :
    Nat.size (left + right) <= Nat.size left + Nat.size right + 1 := by
  rw [Nat.size_le]
  have hleft : left < 2 ^ Nat.size left := Nat.lt_size_self left
  have hright : right < 2 ^ Nat.size right := Nat.lt_size_self right
  have hleftPower :
      2 ^ Nat.size left <= 2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower :
      2 ^ Nat.size right <= 2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_left (Nat.size right) (Nat.size left))
  calc
    left + right < 2 ^ Nat.size left + 2 ^ Nat.size right :=
      Nat.add_lt_add hleft hright
    _ <= 2 ^ (Nat.size left + Nat.size right) +
        2 ^ (Nat.size left + Nat.size right) :=
      Nat.add_le_add hleftPower hrightPower
    _ = 2 ^ (Nat.size left + Nat.size right + 1) := by
      rw [pow_succ]
      omega

private theorem natSize_seven_add_le
    (a b c d e f g : Nat) :
    Nat.size (a + b + c + d + e + f + g) <=
      Nat.size a + Nat.size b + Nat.size c + Nat.size d +
        Nat.size e + Nat.size f + Nat.size g + 6 := by
  have hab := natSize_add_le a b
  have habc := natSize_add_le (a + b) c
  have habcd := natSize_add_le (a + b + c) d
  have habcde := natSize_add_le (a + b + c + d) e
  have habcdef := natSize_add_le (a + b + c + d + e) f
  have habcdefg := natSize_add_le (a + b + c + d + e + f) g
  omega

def compactProofRootOuterFailureTokenWeightBound
    (inputWeight : Nat) : Nat :=
  2 * inputWeight

def compactProofRootOuterFailureWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactProofRootOuterFailureTokenWeightBound inputWeight

def compactProofRootOuterFailureTableSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootOuterFailureTokenWeightBound inputWeight *
    compactProofRootOuterFailureWidthBound inputWeight

def compactProofRootOuterFailureBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactProofRootOuterFailureTokenWeightBound inputWeight

def compactProofRootOuterFailureEndpointSizeBound
    (inputWeight : Nat) : Nat :=
  4 * compactProofRootOuterFailureBoundarySizeBound inputWeight +
    3 * inputWeight + 6

/-- One common bit-size budget for all eight public endpoint coordinates. -/
def compactProofRootOuterFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootOuterFailureTableSizeBound inputWeight +
    compactProofRootOuterFailureWidthBound inputWeight +
    compactProofRootOuterFailureTokenWeightBound inputWeight +
    compactProofRootOuterFailureBoundarySizeBound inputWeight +
    compactProofRootOuterFailureEndpointSizeBound inputWeight +
    inputWeight + 8

structure CompactProofRootOuterFailurePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      tailStart tailFinish endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width : Nat.size width <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  tailStart : Nat.size tailStart <= bound
  tailFinish : Nat.size tailFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

theorem
    exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty_with_publicBounds :
    let input := ([] : List Nat)
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootOuterFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound ∧
        CompactProofRootOuterFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound
            (compactProofRootOuterFailurePublicCoordinateSizeBound
              inputWeight) := by
  let input := ([] : List Nat)
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let tokens := inputTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactProofRootOuterFailureTokenWeightBound inputWeight := by
    change compactAdditiveValueWeight input <= _
    unfold compactProofRootOuterFailureTokenWeightBound
    omega
  have htokenCount :
      tokens.length <=
        compactProofRootOuterFailureTokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <= compactProofRootOuterFailureWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactProofRootOuterFailureWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactProofRootOuterFailureTableSizeBound inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input []
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ [] = tokens := by
    simp [tokens, inputTokens]
  rw [hinputTokenEq] at hinputRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, tokens, inputTokens,
      List.length_nil, Nat.zero_add, Nat.add_zero] using hinputRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows,
      hinputBoundarySize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputBoundarySize⟩
  have hgraph : CompactProofRootOuterFailureEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length 0 0
        { inputBoundary := inputBoundary
          inputCount := input.length
          inputBoundarySize := Nat.size inputBoundary
          tailBoundary := 0
          tailCount := 0
          tailBoundarySize := 0
          tag := 0 } :=
    ⟨hinputRows, Or.inl rfl⟩
  let endpointBound :=
    inputBoundary + input.length + Nat.size inputBoundary +
      0 + 0 + 0 + 0
  have hbounded : CompactProofRootOuterFailureEndpointBoundedGraph
      tokenTable width tokens.length 0 inputTokens.length
        0 0 endpointBound := by
    unfold CompactProofRootOuterFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        0, ?_, 0, ?_, 0, ?_, 0, ?_, ?_⟩
    all_goals try
      (dsimp only [endpointBound]
       omega)
    simpa only [
      compactProofRootOuterFailureEndpointCoordinatesOfValues] using hgraph
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactProofRootOuterFailureBoundarySizeBound inputWeight := by
    exact hinputBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have hinputBoundarySizeSize :
      Nat.size (Nat.size inputBoundary) <=
        compactProofRootOuterFailureBoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size inputBoundary))).trans
      hinputBoundaryPublic
  have hendpointRaw := natSize_seven_add_le
    inputBoundary input.length (Nat.size inputBoundary) 0 0 0 0
  simp only [Nat.size_zero] at hendpointRaw
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootOuterFailureEndpointSizeBound inputWeight := by
    dsimp only [endpointBound]
    unfold compactProofRootOuterFailureEndpointSizeBound
    omega
  let publicBound :=
    compactProofRootOuterFailurePublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound := by
    exact htable.trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound := by
    exact (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have hinputFinishPublic :
      Nat.size inputTokens.length <= publicBound := by
    have hinputTokensLength :
        inputTokens.length <=
          compactProofRootOuterFailureTokenWeightBound inputWeight := by
      simpa only [tokens] using htokenCount
    exact (natSize_le_of_le hinputTokensLength).trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have hendpointPublic : Nat.size endpointBound <= publicBound :=
    hendpoint.trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    0, 0, endpointBound, by simpa [input] using hinputLayoutExact,
    hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      tailStart := by simp
      tailFinish := by simp
      endpointBound := hendpointPublic }

theorem
    exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid_with_publicBounds
    (tag : Nat) (tail : List Nat) (htag : 9 < tag) :
    let input := tag :: tail
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ tailStart tailFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootOuterFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound ∧
        CompactProofRootOuterFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            tailStart tailFinish endpointBound
            (compactProofRootOuterFailurePublicCoordinateSizeBound
              inputWeight) := by
  let input := tag :: tail
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let tokens := inputTokens ++ tailTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htailWeight :
      compactAdditiveValueWeight tail <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show tail <:+ input from by simp [input])
  have htagSize : Nat.size tag <= inputWeight := by
    have htagWeight :
        compactAdditiveValueWeight tag <= inputWeight := by
      exact compactAdditiveValueWeight_nat_mem_le
        (show tag ∈ input from by simp [input])
    simpa only [compactAdditiveValueWeight_nat] using
      (Nat.le_trans (Nat.le_add_right (Nat.size tag) 1) htagWeight)
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactProofRootOuterFailureTokenWeightBound inputWeight := by
    rw [compactAdditiveTokenWeight_append]
    change compactAdditiveValueWeight input +
        compactAdditiveValueWeight tail <= _
    unfold compactProofRootOuterFailureTokenWeightBound
    omega
  have htokenCount :
      tokens.length <=
        compactProofRootOuterFailureTokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <= compactProofRootOuterFailureWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactProofRootOuterFailureWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactProofRootOuterFailureTableSizeBound inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input tailTokens
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ tailTokens = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail []
  dsimp only at htailRaw
  have htailTokenEq :
      inputTokens ++ compactAdditiveEncode tail ++ [] = tokens := by
    simp [tailTokens, tokens]
  rw [htailTokenEq] at htailRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have htailLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length tokens.length tail := by
    simpa only [tokenTable, width, tokens, tailTokens,
      List.length_append, List.length_nil, Nat.add_zero] using htailRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows,
      hinputBoundarySize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows,
      htailBoundarySize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputBoundarySize⟩
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length
        tokens.length tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailBoundarySize⟩
  have hconsRows : CompactAdditiveNatListConsRows
      tokenTable width tokens.length tailBoundary tail.length
        inputBoundary input.length tag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  have hgraph : CompactProofRootOuterFailureEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length
        inputTokens.length tokens.length
        { inputBoundary := inputBoundary
          inputCount := input.length
          inputBoundarySize := Nat.size inputBoundary
          tailBoundary := tailBoundary
          tailCount := tail.length
          tailBoundarySize := Nat.size tailBoundary
          tag := tag } :=
    ⟨hinputRows, Or.inr ⟨htailRows, htag, hconsRows⟩⟩
  let endpointBound :=
    inputBoundary + input.length + Nat.size inputBoundary +
      tailBoundary + tail.length + Nat.size tailBoundary + tag
  have hbounded : CompactProofRootOuterFailureEndpointBoundedGraph
      tokenTable width tokens.length 0 inputTokens.length
        inputTokens.length tokens.length endpointBound := by
    unfold CompactProofRootOuterFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        tag, ?_, ?_⟩
    all_goals try
      (dsimp only [endpointBound]
       omega)
    simpa only [
      compactProofRootOuterFailureEndpointCoordinatesOfValues] using hgraph
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le tail).trans htailWeight
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactProofRootOuterFailureBoundarySizeBound inputWeight := by
    exact hinputBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactProofRootOuterFailureBoundarySizeBound inputWeight := by
    exact htailBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have htailCountSize : Nat.size tail.length <= inputWeight :=
    natSize_le_of_le htailLength
  have hinputBoundarySizeSize :
      Nat.size (Nat.size inputBoundary) <=
        compactProofRootOuterFailureBoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size inputBoundary))).trans
      hinputBoundaryPublic
  have htailBoundarySizeSize :
      Nat.size (Nat.size tailBoundary) <=
        compactProofRootOuterFailureBoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size tailBoundary))).trans
      htailBoundaryPublic
  have hendpointRaw := natSize_seven_add_le
    inputBoundary input.length (Nat.size inputBoundary)
      tailBoundary tail.length (Nat.size tailBoundary) tag
  have hendpoint :
      Nat.size endpointBound <=
        compactProofRootOuterFailureEndpointSizeBound inputWeight := by
    dsimp only [endpointBound]
    unfold compactProofRootOuterFailureEndpointSizeBound
    omega
  let publicBound :=
    compactProofRootOuterFailurePublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound := by
    exact htable.trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound := by
    exact (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have hinputFinishPublic :
      Nat.size inputTokens.length <= publicBound := by
    have hinputTokensLength :
        inputTokens.length <=
          compactProofRootOuterFailureTokenWeightBound inputWeight := by
      exact (Nat.le_add_right inputTokens.length tailTokens.length).trans
        (by simpa only [tokens, List.length_append] using htokenCount)
    exact (natSize_le_of_le hinputTokensLength).trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  have htailFinishPublic : Nat.size tokens.length <= publicBound :=
    htokenCountPublic
  have hendpointPublic : Nat.size endpointBound <= publicBound :=
    hendpoint.trans (by
      unfold publicBound
        compactProofRootOuterFailurePublicCoordinateSizeBound
      omega)
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, tokens.length, endpointBound,
    by simpa [input] using hinputLayoutExact, hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      tailStart := hinputFinishPublic
      tailFinish := htailFinishPublic
      endpointBound := hendpointPublic }

#print axioms
  exists_compactProofRootOuterFailureEndpointBoundedGraph_of_empty_with_publicBounds
#print axioms
  exists_compactProofRootOuterFailureEndpointBoundedGraph_of_invalid_with_publicBounds

end FoundationCompactNumericListedDirectProofRootOuterFailurePublicBounds
