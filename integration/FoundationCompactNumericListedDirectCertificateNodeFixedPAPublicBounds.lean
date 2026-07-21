import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula

/-!
# Public quantitative bounds for fixed PA-axiom certificate parsing

The fixed one-token PA-axiom branch uses one canonical table containing the
input, its tail, the consumed axiom token, and the returned suffix.  This file
retains explicit bounds for every public coordinate and every existential
endpoint coordinate.  No table, endpoint, or size certificate is supplied as
an input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds

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
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula

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

private theorem natSize_fifteen_add_le
    (a b c d e f g h i j k l m n o : Nat) :
    Nat.size (a + b + c + d + e + f + g + h + i + j + k + l + m + n + o) <=
      Nat.size a + Nat.size b + Nat.size c + Nat.size d + Nat.size e +
        Nat.size f + Nat.size g + Nat.size h + Nat.size i + Nat.size j +
        Nat.size k + Nat.size l + Nat.size m + Nat.size n + Nat.size o + 14 := by
  have hab := natSize_add_le a b
  have habc := natSize_add_le (a + b) c
  have habcd := natSize_add_le (a + b + c) d
  have habcde := natSize_add_le (a + b + c + d) e
  have habcdef := natSize_add_le (a + b + c + d + e) f
  have habcdefg := natSize_add_le (a + b + c + d + e + f) g
  have habcdefgh := natSize_add_le (a + b + c + d + e + f + g) h
  have habcdefghi := natSize_add_le (a + b + c + d + e + f + g + h) i
  have habcdefghij :=
    natSize_add_le (a + b + c + d + e + f + g + h + i) j
  have habcdefghijk :=
    natSize_add_le (a + b + c + d + e + f + g + h + i + j) k
  have habcdefghijkl :=
    natSize_add_le (a + b + c + d + e + f + g + h + i + j + k) l
  have habcdefghijklm :=
    natSize_add_le (a + b + c + d + e + f + g + h + i + j + k + l) m
  have habcdefghijklmn :=
    natSize_add_le (a + b + c + d + e + f + g + h + i + j + k + l + m) n
  have habcdefghijklmno :=
    natSize_add_le
      (a + b + c + d + e + f + g + h + i + j + k + l + m + n) o
  omega

def compactCertificateNodeFixedPATokenWeightBound
    (inputWeight : Nat) : Nat :=
  4 * inputWeight

def compactCertificateNodeFixedPAWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodeFixedPATokenWeightBound inputWeight

def compactCertificateNodeFixedPATableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeFixedPATokenWeightBound inputWeight *
    compactCertificateNodeFixedPAWidthBound inputWeight

def compactCertificateNodeFixedPABoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodeFixedPATokenWeightBound inputWeight

def compactCertificateNodeFixedPAEndpointSizeBound
    (inputWeight : Nat) : Nat :=
  8 * compactCertificateNodeFixedPABoundarySizeBound inputWeight +
    2 * compactCertificateNodeFixedPATokenWeightBound inputWeight +
    5 * inputWeight + 14

/-- One common bit-size budget for all eleven public endpoint coordinates. -/
def compactCertificateNodeFixedPAPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeFixedPATableSizeBound inputWeight +
    compactCertificateNodeFixedPAWidthBound inputWeight +
    compactCertificateNodeFixedPATokenWeightBound inputWeight +
    compactCertificateNodeFixedPABoundarySizeBound inputWeight +
    compactCertificateNodeFixedPAEndpointSizeBound inputWeight +
    inputWeight + 16

theorem compactCertificateNodeFixedPAPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeFixedPAPublicCoordinateSizeBound left <=
      compactCertificateNodeFixedPAPublicCoordinateSizeBound right := by
  have htoken : 4 * left <= 4 * right := by omega
  have hwidth : 2 * (4 * left) <= 2 * (4 * right) := by omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hboundary := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  unfold compactCertificateNodeFixedPAPublicCoordinateSizeBound
    compactCertificateNodeFixedPAEndpointSizeBound
    compactCertificateNodeFixedPABoundarySizeBound
    compactCertificateNodeFixedPATableSizeBound
    compactCertificateNodeFixedPAWidthBound
    compactCertificateNodeFixedPATokenWeightBound at *
  omega

structure CompactCertificateNodeFixedPAPublicCoordinateBounds
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
    exists_compactCertificateNodeFixedPAEndpointBoundedGraph_with_publicBounds
    (paTag : Nat) (suffix : List Nat)
    (hfixed : CompactFixedPAAxiomTag paTag) :
    let input := 1 :: paTag :: suffix
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish suffixStart suffixFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeFixedPAEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish 1 endpointBound ∧
        CompactCertificateNodeFixedPAPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish suffixStart suffixFinish 1 endpointBound
            (compactCertificateNodeFixedPAPublicCoordinateSizeBound
              inputWeight) := by
  let tail := paTag :: suffix
  let input := 1 :: tail
  let axiomTokens := [paTag]
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
        refine ⟨[1, paTag], ?_⟩
        simp [input, tail])
  have haxiomWeight :
      compactAdditiveValueWeight axiomTokens <= inputWeight := by
    exact compactAdditiveValueWeight_infix_le
      (show axiomTokens <:+: input from by
        refine ⟨[1], suffix, ?_⟩
        simp [axiomTokens, input, tail])
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight := by
    calc
      compactAdditiveTokenWeight tokens =
          compactAdditiveValueWeight input +
            compactAdditiveValueWeight tail +
            compactAdditiveValueWeight axiomTokens +
            compactAdditiveValueWeight suffix := by
        simp [tokens, inputTokens, tailTokens, axiomEncoded, suffixTokens,
          compactAdditiveValueWeight, Nat.add_assoc]
      _ <= compactCertificateNodeFixedPATokenWeightBound inputWeight := by
        unfold compactCertificateNodeFixedPATokenWeightBound
        omega
  have htokenCount :
      tokens.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <= compactCertificateNodeFixedPAWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodeFixedPAWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodeFixedPATableSizeBound inputWeight := by
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
  have hinnerCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length
        suffixBoundary suffix.length tailBoundary tail.length paTag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hsuffixElementRows htailElementRows
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
  let coordinates : CompactCertificateNodeFixedPAEndpointCoordinates :=
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
      paTag := paTag }
  have hgraph : CompactCertificateNodeFixedPAEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length 1 coordinates := by
    exact ⟨hinputRows, htailRows, haxiomRows, hsuffixRows,
      rfl, hfixed, houterCons, hinnerCons, happend⟩
  let endpointBound :=
    inputBoundary + input.length + Nat.size inputBoundary +
      inputTokens.length +
      (inputTokens.length + tailTokens.length) +
      tailBoundary + tail.length + Nat.size tailBoundary +
      axiomBoundary + axiomTokens.length + Nat.size axiomBoundary +
      suffixBoundary + suffix.length + Nat.size suffixBoundary + paTag
  have hbounded : CompactCertificateNodeFixedPAEndpointBoundedGraph
      tokenTable width tokens.length 0 inputTokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        tokens.length 1 endpointBound := by
    unfold CompactCertificateNodeFixedPAEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        inputTokens.length, ?_,
        inputTokens.length + tailTokens.length, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        axiomBoundary, ?_, axiomTokens.length, ?_, Nat.size axiomBoundary, ?_,
        suffixBoundary, ?_, suffix.length, ?_, Nat.size suffixBoundary, ?_,
        paTag, ?_, ?_⟩
    all_goals try
      (dsimp only [endpointBound]
       omega)
    simpa only [coordinates,
      compactCertificateNodeFixedPAEndpointCoordinatesOfValues] using hgraph
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
        compactCertificateNodeFixedPABoundarySizeBound inputWeight := by
    exact hinputBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight := by
    exact htailBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  have haxiomBoundaryPublic :
      Nat.size axiomBoundary <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight := by
    exact haxiomBoundarySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right haxiomLength 1) htokenCount)
  have hsuffixBoundaryPublic :
      Nat.size suffixBoundary <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight := by
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
  have hinputBoundarySizeSize :
      Nat.size (Nat.size inputBoundary) <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size inputBoundary))).trans
      hinputBoundaryPublic
  have htailBoundarySizeSize :
      Nat.size (Nat.size tailBoundary) <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size tailBoundary))).trans
      htailBoundaryPublic
  have haxiomBoundarySizeSize :
      Nat.size (Nat.size axiomBoundary) <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size axiomBoundary))).trans
      haxiomBoundaryPublic
  have hsuffixBoundarySizeSize :
      Nat.size (Nat.size suffixBoundary) <=
        compactCertificateNodeFixedPABoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size suffixBoundary))).trans
      hsuffixBoundaryPublic
  have htailStartLength :
      inputTokens.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight := by
    exact (by
      have : inputTokens.length <= tokens.length := by
        simp [tokens]
      exact this.trans htokenCount)
  have htailFinishLength :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight := by
    exact (by
      have : inputTokens.length + tailTokens.length <= tokens.length := by
        simp [tokens]
      exact this.trans htokenCount)
  have htailStartSize :
      Nat.size inputTokens.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight :=
    natSize_le_of_le htailStartLength
  have htailFinishSize :
      Nat.size (inputTokens.length + tailTokens.length) <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight :=
    natSize_le_of_le htailFinishLength
  have hendpointRaw := natSize_fifteen_add_le
    inputBoundary input.length (Nat.size inputBoundary)
    inputTokens.length (inputTokens.length + tailTokens.length)
    tailBoundary tail.length (Nat.size tailBoundary)
    axiomBoundary axiomTokens.length (Nat.size axiomBoundary)
    suffixBoundary suffix.length (Nat.size suffixBoundary) paTag
  have hendpoint :
      Nat.size endpointBound <=
        compactCertificateNodeFixedPAEndpointSizeBound inputWeight := by
    dsimp only [endpointBound]
    unfold compactCertificateNodeFixedPAEndpointSizeBound
    omega
  let publicBound :=
    compactCertificateNodeFixedPAPublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound := by
    exact htable.trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound := by
    exact (natSize_le_of_le hwidth).trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have hwidthValuePublic : width <= publicBound :=
    hwidth.trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have htokenCountValuePublic : tokens.length <= publicBound :=
    htokenCount.trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have hinputFinishLength :
      inputTokens.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight :=
    htailStartLength
  have haxiomStartLength :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight :=
    htailFinishLength
  have haxiomFinishLength :
      inputTokens.length + tailTokens.length + axiomEncoded.length <=
        compactCertificateNodeFixedPATokenWeightBound inputWeight := by
    have hpartial :
        inputTokens.length + tailTokens.length + axiomEncoded.length <=
          tokens.length := by
      simp only [tokens, List.length_append]
      omega
    exact hpartial.trans htokenCount
  have hinputFinishPublic : Nat.size inputTokens.length <= publicBound :=
    (natSize_le_of_le hinputFinishLength).trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have haxiomStartPublic :
      Nat.size (inputTokens.length + tailTokens.length) <= publicBound :=
    (natSize_le_of_le haxiomStartLength).trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have haxiomFinishPublic :
      Nat.size
        (inputTokens.length + tailTokens.length + axiomEncoded.length) <=
          publicBound :=
    (natSize_le_of_le haxiomFinishLength).trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  have hsuffixFinishPublic : Nat.size tokens.length <= publicBound :=
    htokenCountPublic
  have hcertificateTagPublic : Nat.size 1 <= publicBound := by
    unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
    simp
  have hendpointPublic : Nat.size endpointBound <= publicBound :=
    hendpoint.trans (by
      unfold publicBound compactCertificateNodeFixedPAPublicCoordinateSizeBound
      omega)
  refine
    ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
      inputTokens.length + tailTokens.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length,
      tokens.length, endpointBound,
      by simpa [input, tail] using hinputLayoutExact, hbounded, ?_⟩
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
  exists_compactCertificateNodeFixedPAEndpointBoundedGraph_with_publicBounds
#print axioms compactCertificateNodeFixedPAPublicCoordinateSizeBound_mono

end FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds
