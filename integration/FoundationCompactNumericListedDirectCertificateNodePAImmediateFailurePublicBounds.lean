import integration.FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public bounds for immediate PA-certificate failure

The PA parser fails immediately on an empty tail or on a PA tag above 22.
Both canonical constructions below expose a fixed-width table and use an
explicit power-of-two endpoint derived only from the original input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds

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
open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint
open FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureBoundedFormula

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

def compactCertificateNodePAImmediateFailureTokenWeightBound
    (inputWeight : Nat) : Nat :=
  3 * inputWeight

def compactCertificateNodePAImmediateFailureWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight

def compactCertificateNodePAImmediateFailureTableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight *
    compactCertificateNodePAImmediateFailureWidthBound inputWeight

def compactCertificateNodePAImmediateFailureBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight

/-- Every one of the fourteen hidden endpoint coordinates has binary size at
most this quantity. -/
def compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodePAImmediateFailureBoundarySizeBound inputWeight +
    compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight +
    inputWeight + 8

def compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodePAImmediateFailureTableSizeBound inputWeight +
    compactCertificateNodePAImmediateFailureWidthBound inputWeight +
    compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight +
    compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      inputWeight +
    inputWeight + 8

structure CompactCertificateNodePAImmediateFailurePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish endpointBound
      bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width : Nat.size width <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

private theorem hidden_le_endpoint
    {inputWeight value : Nat}
    (hvalue : Nat.size value <=
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
        inputWeight) :
    value <=
      2 ^
        compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
          inputWeight :=
  nat_le_two_pow_of_size_le hvalue

theorem
    exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty_with_publicBounds :
    let input := [1]
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodePAImmediateFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
              inputWeight) := by
  let tail := ([] : List Nat)
  let input := [1]
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let tokens := inputTokens ++ tailTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodePAImmediateFailureTokenWeightBound
          inputWeight := by
    rw [compactAdditiveTokenWeight_append]
    change compactAdditiveValueWeight input +
        compactAdditiveValueWeight tail <= _
    unfold compactCertificateNodePAImmediateFailureTokenWeightBound
    simp [tail, inputWeight]
  have htokenCount :
      tokens.length <=
        compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <=
        compactCertificateNodePAImmediateFailureWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodePAImmediateFailureWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodePAImmediateFailureTableSizeBound
          inputWeight := by
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
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length
        tokens.length tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailSize⟩
  have houterCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length tailBoundary tail.length
        inputBoundary input.length 1 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  let coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := tokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      bodyStart := 0
      bodyFinish := 0
      bodyBoundary := 0
      bodyCount := 0
      bodyBoundarySize := 0
      paTag := 0 }
  have hgraph : CompactCertificateNodePAImmediateFailureEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length coordinates :=
    ⟨hinputRows, htailRows, houterCons, Or.inl rfl⟩
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight := by
    simp [tail]
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodePAImmediateFailureBoundarySizeBound
          inputWeight := by
    exact hinputSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodePAImmediateFailureBoundarySizeBound
          inputWeight := by
    exact htailSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  let hiddenBound :=
    compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      inputWeight
  have hboundaryToHidden :
      compactCertificateNodePAImmediateFailureBoundarySizeBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    omega
  have htokenToHidden :
      compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    omega
  have hinputToHidden : inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    omega
  have hinputBoundaryHidden :=
    hinputBoundaryPublic.trans hboundaryToHidden
  have htailBoundaryHidden :=
    htailBoundaryPublic.trans hboundaryToHidden
  have hinputBoundarySizeHidden :
      Nat.size (Nat.size inputBoundary) <= hiddenBound :=
    (natSize_le_of_le (Nat.le_refl (Nat.size inputBoundary))).trans
      hinputBoundaryHidden
  have htailBoundarySizeHidden :
      Nat.size (Nat.size tailBoundary) <= hiddenBound :=
    (natSize_le_of_le (Nat.le_refl (Nat.size tailBoundary))).trans
      htailBoundaryHidden
  have hinputCountHidden :
      Nat.size input.length <= hiddenBound :=
    (natSize_le_of_le hinputLength).trans hinputToHidden
  have htailCountHidden :
      Nat.size tail.length <= hiddenBound :=
    (natSize_le_of_le htailLength).trans hinputToHidden
  have hinputFinishHidden :
      Nat.size inputTokens.length <= hiddenBound := by
    have hlength : inputTokens.length <=
        compactCertificateNodePAImmediateFailureTokenWeightBound
          inputWeight :=
      (Nat.le_add_right inputTokens.length tailTokens.length).trans
        (by simpa only [tokens, List.length_append] using htokenCount)
    exact (natSize_le_of_le hlength).trans htokenToHidden
  have htokenCountHidden :
      Nat.size tokens.length <= hiddenBound :=
    (natSize_le_of_le htokenCount).trans htokenToHidden
  let endpointBound := 2 ^ hiddenBound
  have hbounded :
      CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
        tokenTable width tokens.length 0 inputTokens.length endpointBound := by
    unfold CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        inputTokens.length, ?_, tokens.length, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        0, ?_, 0, ?_, 0, ?_, 0, ?_, 0, ?_, 0, ?_, ?_⟩
    · exact hidden_le_endpoint hinputBoundaryHidden
    · exact hidden_le_endpoint hinputCountHidden
    · exact hidden_le_endpoint hinputBoundarySizeHidden
    · exact hidden_le_endpoint hinputFinishHidden
    · exact hidden_le_endpoint htokenCountHidden
    · exact hidden_le_endpoint htailBoundaryHidden
    · exact hidden_le_endpoint htailCountHidden
    · exact hidden_le_endpoint htailBoundarySizeHidden
    all_goals try
      (simp [endpointBound])
    simpa only [coordinates,
      compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues]
      using hgraph
  let publicBound :=
    compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound :=
    htable.trans (by
      unfold publicBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound :=
    (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound :=
    htokenCountHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
        compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      omega)
  have hinputFinishPublic :
      Nat.size inputTokens.length <= publicBound :=
    hinputFinishHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
        compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      omega)
  have hendpointPublic : Nat.size endpointBound <= publicBound := by
    rw [Nat.size_pow]
    dsimp only [publicBound, hiddenBound]
    unfold
      compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
    omega
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    endpointBound, by simpa [input] using hinputLayoutExact, hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      endpointBound := hendpointPublic }

theorem
    exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large_with_publicBounds
    (paTag : Nat) (body : List Nat) (htag : 22 < paTag) :
    let input := 1 :: paTag :: body
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodePAImmediateFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
              inputWeight) := by
  let tail := paTag :: body
  let input := 1 :: tail
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let bodyTokens := compactAdditiveEncode body
  let tokens := inputTokens ++ tailTokens ++ bodyTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htailWeight :
      compactAdditiveValueWeight tail <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show tail <:+ input from by simp [input])
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show body <:+ input from
        ⟨[1, paTag], by simp [input, tail]⟩)
  have hpaTagSize : Nat.size paTag <= inputWeight := by
    have hweight :
        compactAdditiveValueWeight paTag <= inputWeight :=
      compactAdditiveValueWeight_nat_mem_le
        (show paTag ∈ input from by simp [input, tail])
    simpa only [compactAdditiveValueWeight_nat] using
      (Nat.le_trans (Nat.le_add_right (Nat.size paTag) 1) hweight)
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodePAImmediateFailureTokenWeightBound
          inputWeight := by
    simp only [tokens, compactAdditiveTokenWeight_append]
    change compactAdditiveValueWeight input +
        compactAdditiveValueWeight tail +
        compactAdditiveValueWeight body <= _
    unfold compactCertificateNodePAImmediateFailureTokenWeightBound
    omega
  have htokenCount :
      tokens.length <=
        compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <=
        compactCertificateNodePAImmediateFailureWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodePAImmediateFailureWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodePAImmediateFailureTableSizeBound
          inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ bodyTokens)
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ (tailTokens ++ bodyTokens) =
        tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail bodyTokens
  dsimp only at htailRaw
  have htailTokenEq :
      inputTokens ++ compactAdditiveEncode tail ++ bodyTokens = tokens := by
    simp [tailTokens, tokens, List.append_assoc]
  rw [htailTokenEq] at htailRaw
  have hbodyRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens) body []
  dsimp only at hbodyRaw
  have hbodyTokenEq :
      (inputTokens ++ tailTokens) ++ compactAdditiveEncode body ++ [] =
        tokens := by
    simp [bodyTokens, tokens, List.append_assoc]
  rw [hbodyTokenEq] at hbodyRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have htailLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length
        (inputTokens.length + tailTokens.length) tail := by
    simpa only [tokenTable, width, tailTokens,
      List.length_append] using htailRaw
  have hbodyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length) tokens.length body := by
    simpa only [tokenTable, width, tokens, bodyTokens,
      List.length_append, List.length_nil, Nat.add_zero,
      List.append_assoc, Nat.add_assoc] using hbodyRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  rcases hbodyLayout with
    ⟨bodyBoundary, hbodyStructure, hbodyElementRows, hbodySize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length
        (inputTokens.length + tailTokens.length)
        tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailSize⟩
  have hbodyRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length) body.length tokens.length
        bodyBoundary (Nat.size bodyBoundary) :=
    ⟨hbodyStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hbodyElementRows,
      rfl, hbodySize⟩
  have houterCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length tailBoundary tail.length
        inputBoundary input.length 1 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  have hinnerCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length bodyBoundary body.length
        tailBoundary tail.length paTag := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hbodyElementRows htailElementRows
    rfl
  let coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := inputTokens.length + tailTokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      bodyStart := inputTokens.length + tailTokens.length
      bodyFinish := tokens.length
      bodyBoundary := bodyBoundary
      bodyCount := body.length
      bodyBoundarySize := Nat.size bodyBoundary
      paTag := paTag }
  have hgraph : CompactCertificateNodePAImmediateFailureEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length coordinates :=
    ⟨hinputRows, htailRows, houterCons,
      Or.inr ⟨hbodyRows, htag, hinnerCons⟩⟩
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le tail).trans htailWeight
  have hbodyLength : body.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le body).trans hbodyWeight
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodePAImmediateFailureBoundarySizeBound
          inputWeight :=
    hinputSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodePAImmediateFailureBoundarySizeBound
          inputWeight :=
    htailSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  have hbodyBoundaryPublic :
      Nat.size bodyBoundary <=
        compactCertificateNodePAImmediateFailureBoundarySizeBound
          inputWeight :=
    hbodySize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hbodyLength 1) htokenCount)
  let hiddenBound :=
    compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      inputWeight
  have hboundaryToHidden :
      compactCertificateNodePAImmediateFailureBoundarySizeBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    omega
  have htokenToHidden :
      compactCertificateNodePAImmediateFailureTokenWeightBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    omega
  have hinputToHidden : inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
    omega
  have hinputBoundaryHidden :=
    hinputBoundaryPublic.trans hboundaryToHidden
  have htailBoundaryHidden :=
    htailBoundaryPublic.trans hboundaryToHidden
  have hbodyBoundaryHidden :=
    hbodyBoundaryPublic.trans hboundaryToHidden
  have hboundarySizeHidden
      {boundary : Nat} (hboundary : Nat.size boundary <= hiddenBound) :
      Nat.size (Nat.size boundary) <= hiddenBound :=
    (natSize_le_of_le (Nat.le_refl (Nat.size boundary))).trans hboundary
  have hinputCountHidden :
      Nat.size input.length <= hiddenBound :=
    (natSize_le_of_le hinputLength).trans hinputToHidden
  have htailCountHidden :
      Nat.size tail.length <= hiddenBound :=
    (natSize_le_of_le htailLength).trans hinputToHidden
  have hbodyCountHidden :
      Nat.size body.length <= hiddenBound :=
    (natSize_le_of_le hbodyLength).trans hinputToHidden
  have hinputFinishValue :
      inputTokens.length <=
        compactCertificateNodePAImmediateFailureTokenWeightBound
          inputWeight :=
    (Nat.le_add_right inputTokens.length
      (tailTokens.length + bodyTokens.length)).trans
      (by simpa only [tokens, List.length_append, Nat.add_assoc]
        using htokenCount)
  have htailFinishValue :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodePAImmediateFailureTokenWeightBound
          inputWeight :=
    (Nat.le_add_right (inputTokens.length + tailTokens.length)
      bodyTokens.length).trans
      (by simpa only [tokens, List.length_append, Nat.add_assoc]
        using htokenCount)
  have hinputFinishHidden :
      Nat.size inputTokens.length <= hiddenBound :=
    (natSize_le_of_le hinputFinishValue).trans htokenToHidden
  have htailFinishHidden :
      Nat.size (inputTokens.length + tailTokens.length) <= hiddenBound :=
    (natSize_le_of_le htailFinishValue).trans htokenToHidden
  have htokenCountHidden :
      Nat.size tokens.length <= hiddenBound :=
    (natSize_le_of_le htokenCount).trans htokenToHidden
  have hpaTagHidden : Nat.size paTag <= hiddenBound :=
    hpaTagSize.trans hinputToHidden
  let endpointBound := 2 ^ hiddenBound
  have hbounded :
      CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
        tokenTable width tokens.length 0 inputTokens.length endpointBound := by
    unfold CompactCertificateNodePAImmediateFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        inputTokens.length, ?_,
        inputTokens.length + tailTokens.length, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        inputTokens.length + tailTokens.length, ?_, tokens.length, ?_,
        bodyBoundary, ?_, body.length, ?_, Nat.size bodyBoundary, ?_,
        paTag, ?_, ?_⟩
    · exact hidden_le_endpoint hinputBoundaryHidden
    · exact hidden_le_endpoint hinputCountHidden
    · exact hidden_le_endpoint (hboundarySizeHidden hinputBoundaryHidden)
    · exact hidden_le_endpoint hinputFinishHidden
    · exact hidden_le_endpoint htailFinishHidden
    · exact hidden_le_endpoint htailBoundaryHidden
    · exact hidden_le_endpoint htailCountHidden
    · exact hidden_le_endpoint (hboundarySizeHidden htailBoundaryHidden)
    · exact hidden_le_endpoint htailFinishHidden
    · exact hidden_le_endpoint htokenCountHidden
    · exact hidden_le_endpoint hbodyBoundaryHidden
    · exact hidden_le_endpoint hbodyCountHidden
    · exact hidden_le_endpoint (hboundarySizeHidden hbodyBoundaryHidden)
    · exact hidden_le_endpoint hpaTagHidden
    · simpa only [coordinates,
        compactCertificateNodePAImmediateFailureEndpointCoordinatesOfValues]
        using hgraph
  let publicBound :=
    compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound :=
    htable.trans (by
      unfold publicBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound :=
    (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound :=
    htokenCountHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
        compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      omega)
  have hinputFinishPublic :
      Nat.size inputTokens.length <= publicBound :=
    hinputFinishHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
        compactCertificateNodePAImmediateFailureHiddenCoordinateSizeBound
      omega)
  have hendpointPublic : Nat.size endpointBound <= publicBound := by
    rw [Nat.size_pow]
    dsimp only [publicBound, hiddenBound]
    unfold
      compactCertificateNodePAImmediateFailurePublicCoordinateSizeBound
    omega
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    endpointBound, by simpa [input, tail] using hinputLayoutExact,
    hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      endpointBound := hendpointPublic }

#print axioms
  exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_empty_with_publicBounds
#print axioms
  exists_compactCertificateNodePAImmediateFailureEndpointBoundedGraph_of_large_with_publicBounds

end FoundationCompactNumericListedDirectCertificateNodePAImmediateFailurePublicBounds
