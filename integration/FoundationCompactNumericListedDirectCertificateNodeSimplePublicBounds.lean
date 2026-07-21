import integration.FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula

/-!
# Public quantitative bounds for simple certificate-node parsing

The simple structural-certificate branches (tags `0`, `2`, and `3`) use one
canonical table containing the input followed by its returned suffix.  This
file repeats that concrete construction while retaining bounds for every
coordinate exposed by the bounded endpoint formula.  No table, endpoint, or
size certificate is supplied as an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSimplePublicBounds

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
open FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSimpleBoundedFormula

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
  have hleftPower : 2 ^ Nat.size left <=
      2 ^ (Nat.size left + Nat.size right) := by
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : Nat))
      (Nat.le_add_right (Nat.size left) (Nat.size right))
  have hrightPower : 2 ^ Nat.size right <=
      2 ^ (Nat.size left + Nat.size right) := by
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

private theorem natSize_six_add_le
    (a b c d e f : Nat) :
    Nat.size (a + b + c + d + e + f) <=
      Nat.size a + Nat.size b + Nat.size c +
        Nat.size d + Nat.size e + Nat.size f + 5 := by
  have hab := natSize_add_le a b
  have habc := natSize_add_le (a + b) c
  have habcd := natSize_add_le (a + b + c) d
  have habcde := natSize_add_le (a + b + c + d) e
  have habcdef := natSize_add_le (a + b + c + d + e) f
  omega

def compactCertificateNodeSimpleTokenWeightBound
    (inputWeight : Nat) : Nat :=
  inputWeight + inputWeight

def compactCertificateNodeSimpleWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodeSimpleTokenWeightBound inputWeight

def compactCertificateNodeSimpleTableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSimpleTokenWeightBound inputWeight *
    compactCertificateNodeSimpleWidthBound inputWeight

def compactCertificateNodeSimpleBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodeSimpleTokenWeightBound inputWeight

def compactCertificateNodeSimpleEndpointSizeBound
    (inputWeight : Nat) : Nat :=
  4 * compactCertificateNodeSimpleBoundarySizeBound inputWeight +
    2 * inputWeight + 5

/-- One common bit-size budget for all nine public endpoint coordinates. -/
def compactCertificateNodeSimplePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSimpleTableSizeBound inputWeight +
    compactCertificateNodeSimpleWidthBound inputWeight +
    compactCertificateNodeSimpleTokenWeightBound inputWeight +
    compactCertificateNodeSimpleBoundarySizeBound inputWeight +
    compactCertificateNodeSimpleEndpointSizeBound inputWeight +
    inputWeight + 8

theorem compactCertificateNodeSimplePublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeSimplePublicCoordinateSizeBound left <=
      compactCertificateNodeSimplePublicCoordinateSizeBound right := by
  have htoken : left + left <= right + right := by omega
  have hwidth : 2 * (left + left) <= 2 * (right + right) := by omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hboundary := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  unfold compactCertificateNodeSimplePublicCoordinateSizeBound
    compactCertificateNodeSimpleEndpointSizeBound
    compactCertificateNodeSimpleBoundarySizeBound
    compactCertificateNodeSimpleTableSizeBound
    compactCertificateNodeSimpleWidthBound
    compactCertificateNodeSimpleTokenWeightBound at *
  omega

structure CompactCertificateNodeSimplePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  suffixStart : Nat.size suffixStart <= bound
  suffixFinish : Nat.size suffixFinish <= bound
  tag : Nat.size tag <= bound
  endpointBound : Nat.size endpointBound <= bound

theorem exists_compactCertificateNodeSimpleEndpointBoundedGraph_with_publicBounds
    (tag : Nat) (suffix : List Nat)
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    let input := tag :: suffix
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeSimpleEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound ∧
        CompactCertificateNodeSimplePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound
            (compactCertificateNodeSimplePublicCoordinateSizeBound
              inputWeight) := by
  let input := tag :: suffix
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let suffixTokens := compactAdditiveEncode suffix
  let tokens := inputTokens ++ suffixTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hsuffixWeight :
      compactAdditiveValueWeight suffix <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show suffix <:+ input from by simp [input])
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodeSimpleTokenWeightBound inputWeight := by
    rw [compactAdditiveTokenWeight_append]
    change compactAdditiveValueWeight input +
        compactAdditiveValueWeight suffix <= _
    unfold compactCertificateNodeSimpleTokenWeightBound
    simpa only [inputWeight] using
      Nat.add_le_add_left hsuffixWeight inputWeight
  have htokenCount :
      tokens.length <=
        compactCertificateNodeSimpleTokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <= compactCertificateNodeSimpleWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodeSimpleWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodeSimpleTableSizeBound inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input suffixTokens
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ suffixTokens = tokens := by
    simp [inputTokens, tokens]
  rw [hinputTokenEq] at hinputRaw
  have hsuffixRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens suffix []
  dsimp only at hsuffixRaw
  have hsuffixTokenEq :
      inputTokens ++ compactAdditiveEncode suffix ++ [] = tokens := by
    simp [suffixTokens, tokens]
  rw [hsuffixTokenEq] at hsuffixRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, List.length_nil, Nat.zero_add,
      inputTokens] using hinputRaw
  have hsuffixLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length tokens.length suffix := by
    simpa only [tokenTable, width, tokens, suffixTokens,
      List.length_append, List.length_nil, Nat.add_zero] using hsuffixRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputBoundarySize⟩
  rcases hsuffixLayout with
    ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows,
      hsuffixBoundarySize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputBoundarySize⟩
  have hsuffixRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length suffix.length
        tokens.length suffixBoundary (Nat.size suffixBoundary) :=
    ⟨hsuffixStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsuffixElementRows,
      rfl, hsuffixBoundarySize⟩
  have hconsRows : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
        suffixBoundary suffix.length inputBoundary input.length tag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hsuffixElementRows hinputElementRows
    rfl
  let coordinates : CompactCertificateNodeSimpleEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      suffixBoundary := suffixBoundary
      suffixCount := suffix.length
      suffixBoundarySize := Nat.size suffixBoundary }
  have hgraph : CompactCertificateNodeSimpleEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length
        inputTokens.length tokens.length tag coordinates := by
    exact ⟨hinputRows, hsuffixRows, htag, hconsRows⟩
  let endpointBound :=
    inputBoundary + input.length + Nat.size inputBoundary +
      suffixBoundary + suffix.length + Nat.size suffixBoundary
  have hbounded : CompactCertificateNodeSimpleEndpointBoundedGraph
      tokenTable width tokens.length 0 inputTokens.length
        inputTokens.length tokens.length tag endpointBound := by
    unfold CompactCertificateNodeSimpleEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        suffixBoundary, ?_, suffix.length, ?_, Nat.size suffixBoundary, ?_,
        ?_⟩
    all_goals try
      (dsimp only [endpointBound]
       omega)
    simpa only [coordinates,
      compactCertificateNodeSimpleEndpointCoordinatesOfValues] using hgraph
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hsuffixLength : suffix.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le suffix).trans hsuffixWeight
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodeSimpleBoundarySizeBound inputWeight := by
    exact hinputBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have hsuffixBoundaryPublic :
      Nat.size suffixBoundary <=
        compactCertificateNodeSimpleBoundarySizeBound inputWeight := by
    exact hsuffixBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hsuffixLength 1) htokenCount)
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have hsuffixCountSize : Nat.size suffix.length <= inputWeight :=
    natSize_le_of_le hsuffixLength
  have hinputBoundarySizeSize :
      Nat.size (Nat.size inputBoundary) <=
        compactCertificateNodeSimpleBoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size inputBoundary))).trans
      hinputBoundaryPublic
  have hsuffixBoundarySizeSize :
      Nat.size (Nat.size suffixBoundary) <=
        compactCertificateNodeSimpleBoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size suffixBoundary))).trans
      hsuffixBoundaryPublic
  have hendpointRaw := natSize_six_add_le
    inputBoundary input.length (Nat.size inputBoundary)
    suffixBoundary suffix.length (Nat.size suffixBoundary)
  have hendpoint :
      Nat.size endpointBound <=
        compactCertificateNodeSimpleEndpointSizeBound inputWeight := by
    dsimp only [endpointBound]
    unfold compactCertificateNodeSimpleEndpointSizeBound
    omega
  let publicBound :=
    compactCertificateNodeSimplePublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound := by
    exact htable.trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound := by
    exact (natSize_le_of_le hwidth).trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have hwidthValuePublic : width <= publicBound :=
    hwidth.trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have htokenCountValuePublic : tokens.length <= publicBound :=
    htokenCount.trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have hinputFinishPublic : Nat.size inputTokens.length <= publicBound := by
    have hinputTokensLength :
        inputTokens.length <=
          compactCertificateNodeSimpleTokenWeightBound inputWeight := by
      exact (Nat.le_add_right inputTokens.length suffixTokens.length).trans
        (by simpa only [tokens, List.length_append] using htokenCount)
    exact (natSize_le_of_le hinputTokensLength).trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have hsuffixFinishPublic : Nat.size tokens.length <= publicBound :=
    htokenCountPublic
  have htagPublic : Nat.size tag <= publicBound := by
    have hsmall : Nat.size tag <= 8 := by
      apply natSize_le_of_le
      rcases htag with rfl | rfl | rfl <;> omega
    exact hsmall.trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  have hendpointPublic : Nat.size endpointBound <= publicBound :=
    hendpoint.trans (by
      unfold publicBound compactCertificateNodeSimplePublicCoordinateSizeBound
      omega)
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, tokens.length, endpointBound,
    by simpa [input] using hinputLayoutExact, hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width_value := hwidthValuePublic
      width := hwidthPublic
      tokenCount_value := htokenCountValuePublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      suffixStart := hinputFinishPublic
      suffixFinish := hsuffixFinishPublic
      tag := htagPublic
      endpointBound := hendpointPublic }

theorem exists_compactCertificateNodeSimpleEndpointBoundedGraph_of_success_with_publicBounds
    {input : List Nat} {tag : Nat} {axiomTokens suffix : List Nat}
    (hparser : compactStructuralCertificateNodeParser input =
      some (tag, (axiomTokens, suffix)))
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeSimpleEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound ∧
        CompactCertificateNodeSimplePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag endpointBound
            (compactCertificateNodeSimplePublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  rcases compactStructuralCertificateNodeParser_simple_result
      hparser htag with ⟨haxiom, hinput⟩
  subst axiomTokens
  subst input
  simpa using
    exists_compactCertificateNodeSimpleEndpointBoundedGraph_with_publicBounds
      tag suffix htag

#print axioms
  exists_compactCertificateNodeSimpleEndpointBoundedGraph_with_publicBounds
#print axioms
  exists_compactCertificateNodeSimpleEndpointBoundedGraph_of_success_with_publicBounds
#print axioms compactCertificateNodeSimplePublicCoordinateSizeBound_mono

end FoundationCompactNumericListedDirectCertificateNodeSimplePublicBounds
