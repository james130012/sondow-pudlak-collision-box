import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula

/-!
# Public quantitative bounds for symbol PA-axiom certificate parsing

The symbol branches for PA tags `3` and `4` use one canonical table containing
the input, its tail, the three-token axiom payload, and the returned suffix.
Every public and existential coordinate is bounded from the additive input
weight alone.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds

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
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula

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

private theorem nat_le_two_pow_of_size_le
    {value bound : Nat} (hsize : Nat.size value <= bound) :
    value <= 2 ^ bound := by
  have hvalue : value < 2 ^ Nat.size value := Nat.lt_size_self value
  have hpower : 2 ^ Nat.size value <= 2 ^ bound :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hsize
  exact (Nat.le_of_lt hvalue).trans hpower

def compactCertificateNodeSymbolPATokenWeightBound
    (inputWeight : Nat) : Nat :=
  4 * inputWeight

def compactCertificateNodeSymbolPAWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodeSymbolPATokenWeightBound inputWeight

def compactCertificateNodeSymbolPATableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPATokenWeightBound inputWeight *
    compactCertificateNodeSymbolPAWidthBound inputWeight

def compactCertificateNodeSymbolPABoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodeSymbolPATokenWeightBound inputWeight

/-- A bit-size budget for all seventeen existential endpoint coordinates. -/
def compactCertificateNodeSymbolPAHiddenCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPABoundarySizeBound inputWeight +
    compactCertificateNodeSymbolPATokenWeightBound inputWeight +
    inputWeight + 8

def compactCertificateNodeSymbolPAEndpointSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPAHiddenCoordinateSizeBound inputWeight + 1

/-- One common bit-size budget for all eleven public endpoint coordinates. -/
def compactCertificateNodeSymbolPAPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPATableSizeBound inputWeight +
    compactCertificateNodeSymbolPAWidthBound inputWeight +
    compactCertificateNodeSymbolPATokenWeightBound inputWeight +
    compactCertificateNodeSymbolPABoundarySizeBound inputWeight +
    compactCertificateNodeSymbolPAEndpointSizeBound inputWeight +
    inputWeight + 20

theorem compactCertificateNodeSymbolPAPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound left <=
      compactCertificateNodeSymbolPAPublicCoordinateSizeBound right := by
  have htoken : 4 * left <= 4 * right := by omega
  have hwidth : 2 * (4 * left) <= 2 * (4 * right) := by omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hboundary := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  unfold compactCertificateNodeSymbolPAPublicCoordinateSizeBound
    compactCertificateNodeSymbolPAEndpointSizeBound
    compactCertificateNodeSymbolPAHiddenCoordinateSizeBound
    compactCertificateNodeSymbolPABoundarySizeBound
    compactCertificateNodeSymbolPATableSizeBound
    compactCertificateNodeSymbolPAWidthBound
    compactCertificateNodeSymbolPATokenWeightBound at *
  omega

structure CompactCertificateNodeSymbolPAPublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish suffixStart suffixFinish certificateTag
      endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  axiomStart : Nat.size axiomStart <= bound
  axiomFinish : Nat.size axiomFinish <= bound
  suffixStart : Nat.size suffixStart <= bound
  suffixFinish : Nat.size suffixFinish <= bound
  certificateTag : Nat.size certificateTag <= bound
  endpointBound : Nat.size endpointBound <= bound

theorem
    exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_with_publicBounds
    (paTag arity symbolCode : Nat) (suffix : List Nat)
    (hvalid : CompactSymbolPAAxiomTagValid paTag arity symbolCode) :
    let input := 1 :: paTag :: arity :: symbolCode :: suffix
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeSymbolPAEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish 1 endpointBound ∧
        CompactCertificateNodeSymbolPAPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish 1 endpointBound
            (compactCertificateNodeSymbolPAPublicCoordinateSizeBound
              inputWeight) := by
  let axiomTokens := [paTag, arity, symbolCode]
  let tail := axiomTokens ++ suffix
  let input := 1 :: tail
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let axiomEncoded := compactAdditiveEncode axiomTokens
  let suffixTokens := compactAdditiveEncode suffix
  let tokens := inputTokens ++ tailTokens ++ axiomEncoded ++ suffixTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htailWeight :
      compactAdditiveValueWeight tail <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show tail <:+ input from by simp [input])
  have hsuffixWeight :
      compactAdditiveValueWeight suffix <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show suffix <:+ input from by
        refine ⟨[1, paTag, arity, symbolCode], ?_⟩
        simp [input, tail, axiomTokens])
  have haxiomWeight :
      compactAdditiveValueWeight axiomTokens <= inputWeight := by
    exact compactAdditiveValueWeight_infix_le
      (show axiomTokens <:+: input from by
        refine ⟨[1], suffix, ?_⟩
        simp [input, tail])
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight := by
    calc
      compactAdditiveTokenWeight tokens =
          compactAdditiveValueWeight input +
            compactAdditiveValueWeight tail +
            compactAdditiveValueWeight axiomTokens +
            compactAdditiveValueWeight suffix := by
        simp [tokens, inputTokens, tailTokens, axiomEncoded, suffixTokens,
          compactAdditiveValueWeight, Nat.add_assoc]
      _ <= compactCertificateNodeSymbolPATokenWeightBound inputWeight := by
        unfold compactCertificateNodeSymbolPATokenWeightBound
        omega
  have htokenCount :
      tokens.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <= compactCertificateNodeSymbolPAWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodeSymbolPAWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodeSymbolPATableSizeBound inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ axiomEncoded ++ suffixTokens)
  dsimp only at hinputRaw
  have hinputTokenEq : [] ++ compactAdditiveEncode input ++
      (tailTokens ++ axiomEncoded ++ suffixTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail (axiomEncoded ++ suffixTokens)
  dsimp only at htailRaw
  have htailTokenEq : inputTokens ++ compactAdditiveEncode tail ++
      (axiomEncoded ++ suffixTokens) = tokens := by
    simp [tailTokens, tokens, List.append_assoc]
  rw [htailTokenEq] at htailRaw
  have haxiomRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens) axiomTokens suffixTokens
  dsimp only at haxiomRaw
  have haxiomTokenEq : (inputTokens ++ tailTokens) ++
      compactAdditiveEncode axiomTokens ++ suffixTokens = tokens := by
    simp [axiomEncoded, tokens, List.append_assoc]
  rw [haxiomTokenEq] at haxiomRaw
  have hsuffixRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded) suffix []
  dsimp only at hsuffixRaw
  have hsuffixTokenEq : (inputTokens ++ tailTokens ++ axiomEncoded) ++
      compactAdditiveEncode suffix ++ [] = tokens := by
    simp [suffixTokens, tokens, List.append_assoc]
  rw [hsuffixTokenEq] at hsuffixRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have htailLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length
        (inputTokens.length + tailTokens.length) tail := by
    simpa only [tokenTable, width, tailTokens,
      List.length_append] using htailRaw
  have haxiomLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens := by
    simpa only [tokenTable, width, axiomEncoded,
      List.length_append] using haxiomRaw
  have hsuffixLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length suffix := by
    simpa only [tokenTable, width, tokens, suffixTokens,
      List.length_append, List.length_nil, Nat.add_zero] using hsuffixRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputBoundarySize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailBoundarySize⟩
  rcases haxiomLayout with
    ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomBoundarySize⟩
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
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length
        (inputTokens.length + tailTokens.length)
        tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailBoundarySize⟩
  have haxiomRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length) axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomBoundary (Nat.size axiomBoundary) :=
    ⟨haxiomStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        haxiomElementRows,
      rfl, haxiomBoundarySize⟩
  have hsuffixRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        suffix.length tokens.length suffixBoundary (Nat.size suffixBoundary) :=
    ⟨hsuffixStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsuffixElementRows,
      rfl, hsuffixBoundarySize⟩
  have houterCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
        tailBoundary tail.length inputBoundary input.length 1 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  have happend : CompactAdditiveNatListAppendSlices
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length suffix.length
        inputTokens.length (inputTokens.length + tailTokens.length)
        tail.length := by
    apply (compactAdditiveNatListAppendSlices_iff_append
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens from
          ⟨axiomBoundary, haxiomStructure, haxiomElementRows,
            haxiomBoundarySize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length suffix from
          ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows,
            hsuffixBoundarySize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        inputTokens.length (inputTokens.length + tailTokens.length) tail from
          ⟨tailBoundary, htailStructure, htailElementRows,
            htailBoundarySize⟩)).2
    rfl
  have hatZero : CompactAdditiveNatListAtRows tokenTable width tokens.length
      axiomBoundary axiomTokens.length 0 paTag := by
    apply (compactAdditiveNatListAtRows_iff_getI
      haxiomElementRows 0 paTag).2
    simp [axiomTokens]
  have hatOne : CompactAdditiveNatListAtRows tokenTable width tokens.length
      axiomBoundary axiomTokens.length 1 arity := by
    apply (compactAdditiveNatListAtRows_iff_getI
      haxiomElementRows 1 arity).2
    simp [axiomTokens]
  have hatTwo : CompactAdditiveNatListAtRows tokenTable width tokens.length
      axiomBoundary axiomTokens.length 2 symbolCode := by
    apply (compactAdditiveNatListAtRows_iff_getI
      haxiomElementRows 2 symbolCode).2
    simp [axiomTokens]
  let coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := inputTokens.length + tailTokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      axiomBoundary := axiomBoundary
      axiomCount := axiomTokens.length
      axiomBoundarySize := Nat.size axiomBoundary
      suffixBoundary := suffixBoundary
      suffixCount := suffix.length
      suffixBoundarySize := Nat.size suffixBoundary
      paTag := paTag
      arity := arity
      symbolCode := symbolCode }
  have hgraph : CompactCertificateNodeSymbolPAEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length 1 coordinates := by
    exact ⟨hinputRows, htailRows, haxiomRows, hsuffixRows,
      rfl, by simp [coordinates, axiomTokens], hvalid, houterCons, happend,
      hatZero, hatOne, hatTwo⟩
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le tail).trans htailWeight
  have haxiomLength : axiomTokens.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le axiomTokens).trans haxiomWeight
  have hsuffixLength : suffix.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le suffix).trans hsuffixWeight
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight := by
    exact hinputBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight := by
    exact htailBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  have haxiomBoundaryPublic :
      Nat.size axiomBoundary <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight := by
    exact haxiomBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right haxiomLength 1) htokenCount)
  have hsuffixBoundaryPublic :
      Nat.size suffixBoundary <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight := by
    exact hsuffixBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hsuffixLength 1) htokenCount)
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have htailCountSize : Nat.size tail.length <= inputWeight :=
    natSize_le_of_le htailLength
  have haxiomCountSize : Nat.size axiomTokens.length <= inputWeight :=
    natSize_le_of_le haxiomLength
  have hsuffixCountSize : Nat.size suffix.length <= inputWeight :=
    natSize_le_of_le hsuffixLength
  have hpaTagSize : Nat.size paTag <= inputWeight := by
    have hsingle : Nat.size paTag <=
        compactAdditiveValueWeight axiomTokens := by
      simp [axiomTokens, compactAdditiveValueWeight_list,
        compactAdditiveValueWeight_nat]
      omega
    exact hsingle.trans haxiomWeight
  have haritySize : Nat.size arity <= inputWeight := by
    have hsingle : Nat.size arity <=
        compactAdditiveValueWeight axiomTokens := by
      simp [axiomTokens, compactAdditiveValueWeight_list,
        compactAdditiveValueWeight_nat]
      omega
    exact hsingle.trans haxiomWeight
  have hsymbolCodeSize : Nat.size symbolCode <= inputWeight := by
    have hsingle : Nat.size symbolCode <=
        compactAdditiveValueWeight axiomTokens := by
      simp [axiomTokens, compactAdditiveValueWeight_list,
        compactAdditiveValueWeight_nat]
      omega
    exact hsingle.trans haxiomWeight
  have hinputBoundarySizeSize :
      Nat.size (Nat.size inputBoundary) <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size inputBoundary))).trans
      hinputBoundaryPublic
  have htailBoundarySizeSize :
      Nat.size (Nat.size tailBoundary) <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size tailBoundary))).trans
      htailBoundaryPublic
  have haxiomBoundarySizeSize :
      Nat.size (Nat.size axiomBoundary) <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size axiomBoundary))).trans
      haxiomBoundaryPublic
  have hsuffixBoundarySizeSize :
      Nat.size (Nat.size suffixBoundary) <=
        compactCertificateNodeSymbolPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size suffixBoundary))).trans
      hsuffixBoundaryPublic
  have htailStartLength :
      inputTokens.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight := by
    have hpartial : inputTokens.length <= tokens.length := by
      simp [tokens]
    exact hpartial.trans htokenCount
  have htailFinishLength :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight := by
    have hpartial :
        inputTokens.length + tailTokens.length <= tokens.length := by
      simp only [tokens, List.length_append]
      omega
    exact hpartial.trans htokenCount
  have htailStartSize :
      Nat.size inputTokens.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight :=
    natSize_le_of_le htailStartLength
  have htailFinishSize :
      Nat.size (inputTokens.length + tailTokens.length) <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight :=
    natSize_le_of_le htailFinishLength
  let hiddenBound :=
    compactCertificateNodeSymbolPAHiddenCoordinateSizeBound inputWeight
  have hboundaryToHidden :
      compactCertificateNodeSymbolPABoundarySizeBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound compactCertificateNodeSymbolPAHiddenCoordinateSizeBound
    omega
  have htokenToHidden :
      compactCertificateNodeSymbolPATokenWeightBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound compactCertificateNodeSymbolPAHiddenCoordinateSizeBound
    omega
  have hinputToHidden : inputWeight <= hiddenBound := by
    unfold hiddenBound compactCertificateNodeSymbolPAHiddenCoordinateSizeBound
    omega
  let endpointBound := 2 ^ hiddenBound
  have hbounded : CompactCertificateNodeSymbolPAEndpointBoundedGraph
      tokenTable width tokens.length 0 inputTokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length 1 endpointBound := by
    unfold CompactCertificateNodeSymbolPAEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        inputTokens.length, ?_,
        inputTokens.length + tailTokens.length, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        axiomBoundary, ?_, axiomTokens.length, ?_, Nat.size axiomBoundary, ?_,
        suffixBoundary, ?_, suffix.length, ?_, Nat.size suffixBoundary, ?_,
        paTag, ?_, arity, ?_, symbolCode, ?_, ?_⟩
    · exact nat_le_two_pow_of_size_le
        (hinputBoundaryPublic.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hinputCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (hinputBoundarySizeSize.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailStartSize.trans htokenToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailFinishSize.trans htokenToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailBoundaryPublic.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailBoundarySizeSize.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (haxiomBoundaryPublic.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (haxiomCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (haxiomBoundarySizeSize.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hsuffixBoundaryPublic.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hsuffixCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (hsuffixBoundarySizeSize.trans hboundaryToHidden)
    · exact nat_le_two_pow_of_size_le (hpaTagSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le (haritySize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le (hsymbolCodeSize.trans hinputToHidden)
    · simpa only [coordinates,
        compactCertificateNodeSymbolPAEndpointCoordinatesOfValues] using hgraph
  have hendpoint :
      Nat.size endpointBound <=
        compactCertificateNodeSymbolPAEndpointSizeBound inputWeight := by
    dsimp only [endpointBound]
    rw [Nat.size_pow]
    unfold hiddenBound compactCertificateNodeSymbolPAEndpointSizeBound
    exact Nat.le_refl _
  let publicBound :=
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound := by
    exact htable.trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound := by
    exact (natSize_le_of_le hwidth).trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have hwidthValuePublic : width <= publicBound :=
    hwidth.trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have htokenCountValuePublic : tokens.length <= publicBound :=
    htokenCount.trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have hinputFinishLength :
      inputTokens.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight :=
    htailStartLength
  have haxiomStartLength :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight :=
    htailFinishLength
  have haxiomFinishLength :
      inputTokens.length + tailTokens.length + axiomEncoded.length <=
        compactCertificateNodeSymbolPATokenWeightBound inputWeight := by
    have hpartial :
        inputTokens.length + tailTokens.length + axiomEncoded.length <=
          tokens.length := by
      simp only [tokens, List.length_append]
      omega
    exact hpartial.trans htokenCount
  have hinputFinishPublic : Nat.size inputTokens.length <= publicBound :=
    (natSize_le_of_le hinputFinishLength).trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have haxiomStartPublic :
      Nat.size (inputTokens.length + tailTokens.length) <= publicBound :=
    (natSize_le_of_le haxiomStartLength).trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have haxiomFinishPublic :
      Nat.size
        (inputTokens.length + tailTokens.length + axiomEncoded.length) <=
          publicBound :=
    (natSize_le_of_le haxiomFinishLength).trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  have hsuffixFinishPublic : Nat.size tokens.length <= publicBound :=
    htokenCountPublic
  have hcertificateTagPublic : Nat.size 1 <= publicBound := by
    unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
    simp
  have hendpointPublic : Nat.size endpointBound <= publicBound :=
    hendpoint.trans (by
      unfold publicBound compactCertificateNodeSymbolPAPublicCoordinateSizeBound
      omega)
  refine
    ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
      inputTokens.length + tailTokens.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length,
      tokens.length, endpointBound,
      by simpa [input, tail, axiomTokens] using hinputLayoutExact,
      hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width_value := hwidthValuePublic
      width := hwidthPublic
      tokenCount_value := htokenCountValuePublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      axiomStart := haxiomStartPublic
      axiomFinish := haxiomFinishPublic
      suffixStart := haxiomFinishPublic
      suffixFinish := hsuffixFinishPublic
      certificateTag := hcertificateTagPublic
      endpointBound := hendpointPublic }

#print axioms
  exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_with_publicBounds
#print axioms compactCertificateNodeSymbolPAPublicCoordinateSizeBound_mono

end FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds
