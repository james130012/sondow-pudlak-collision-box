import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public bounds for malformed symbol PA certificates

Function- and relation-symbol certificates fail when their two symbol fields
are missing or invalid.  The canonical input/tail table and every hidden
endpoint coordinate are bounded directly from the original input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds

open FoundationCompactArithmeticSymbolCode
open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
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
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureBoundedFormula

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

def compactCertificateNodeSymbolPAFailureTokenWeightBound
    (inputWeight : Nat) : Nat :=
  2 * inputWeight

def compactCertificateNodeSymbolPAFailureWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight

def compactCertificateNodeSymbolPAFailureTableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight *
    compactCertificateNodeSymbolPAFailureWidthBound inputWeight

def compactCertificateNodeSymbolPAFailureBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight

def compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPAFailureBoundarySizeBound inputWeight +
    compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight +
    inputWeight + 8

def compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeSymbolPAFailureTableSizeBound inputWeight +
    compactCertificateNodeSymbolPAFailureWidthBound inputWeight +
    compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight +
    compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
      inputWeight +
    inputWeight + 8

structure CompactCertificateNodeSymbolPAFailurePublicCoordinateBounds
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
      compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
        inputWeight) :
    value <=
      2 ^
        compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
          inputWeight :=
  nat_le_two_pow_of_size_le hvalue

theorem
    exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_publicBounds
    (paTag : Nat) (body : List Nat)
    (htag : paTag = 3 ∨ paTag = 4)
    (hfailure :
      body.length < 2 ∨
        ((paTag = 3 ∧
            ¬ ArithmeticFuncCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)) ∨
          (paTag = 4 ∧
            ¬ ArithmeticRelCodeValid
              (compactTokenAt 0 body) (compactTokenAt 1 body)))) :
    let input := 1 :: paTag :: body
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodeSymbolPAFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
              inputWeight) := by
  let tail := paTag :: body
  let input := 1 :: tail
  let inputWeight := compactAdditiveValueWeight input
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let tokens := inputTokens ++ tailTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htailWeight :
      compactAdditiveValueWeight tail <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show tail <:+ input from by simp [input])
  have hbodySuffix : body <:+ input :=
    ⟨[1, paTag], by simp [input, tail]⟩
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight :=
    compactAdditiveValueWeight_suffix_le hbodySuffix
  have hpaTagSize : Nat.size paTag <= inputWeight := by
    have hweight :
        compactAdditiveValueWeight paTag <= inputWeight :=
      compactAdditiveValueWeight_nat_mem_le
        (show paTag ∈ input from by simp [input, tail])
    simpa only [compactAdditiveValueWeight_nat] using
      (Nat.le_trans (Nat.le_add_right (Nat.size paTag) 1) hweight)
  let arity := compactTokenAt 0 body
  let symbolCode := compactTokenAt 1 body
  have haritySize : Nat.size arity <= inputWeight := by
    have hweight :=
      compactTokenAt_weight_le_of_suffix hbodySuffix 0
    dsimp only [arity]
    change Nat.size (compactTokenAt 0 body) <= inputWeight
    change Nat.size (compactTokenAt 0 body) + 1 <= inputWeight at hweight
    omega
  have hsymbolSize : Nat.size symbolCode <= inputWeight := by
    have hweight :=
      compactTokenAt_weight_le_of_suffix hbodySuffix 1
    dsimp only [symbolCode]
    change Nat.size (compactTokenAt 1 body) <= inputWeight
    change Nat.size (compactTokenAt 1 body) + 1 <= inputWeight at hweight
    omega
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight := by
    rw [compactAdditiveTokenWeight_append]
    change compactAdditiveValueWeight input +
        compactAdditiveValueWeight tail <= _
    unfold compactCertificateNodeSymbolPAFailureTokenWeightBound
    omega
  have htokenCount :
      tokens.length <=
        compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <=
        compactCertificateNodeSymbolPAFailureWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodeSymbolPAFailureWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodeSymbolPAFailureTableSizeBound inputWeight := by
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
  have hatZero : CompactAdditiveNatListAtRows
      tokenTable width tokens.length tailBoundary tail.length 0 paTag := by
    apply (compactAdditiveNatListAtRows_iff_getI
      htailElementRows 0 paTag).mpr
    simp [tail]
  let coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := tokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      paTag := paTag
      arity := arity
      symbolCode := symbolCode }
  have hgraph : CompactCertificateNodeSymbolPAFailureEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length coordinates := by
    refine
      ⟨hinputRows, htailRows, houterCons, hatZero, htag, ?_⟩
    rcases hfailure with hshort | hinvalid
    · apply Or.inl
      change tail.length < 3
      dsimp only [tail]
      simp only [List.length_cons]
      omega
    · by_cases hshort : body.length < 2
      · apply Or.inl
        change tail.length < 3
        dsimp only [tail]
        simp only [List.length_cons]
        omega
      · have hlength : 2 <= body.length := by omega
        have hatOne : CompactAdditiveNatListAtRows
            tokenTable width tokens.length tailBoundary tail.length
              1 arity := by
          apply (compactAdditiveNatListAtRows_iff_getI
            htailElementRows 1 arity).mpr
          constructor
          · dsimp only [tail]
            simp only [List.length_cons]
            omega
          · cases body with
            | nil => simp at hlength
            | cons first rest => simp [tail, arity, compactTokenAt]
        have hatTwo : CompactAdditiveNatListAtRows
            tokenTable width tokens.length tailBoundary tail.length
              2 symbolCode := by
          apply (compactAdditiveNatListAtRows_iff_getI
            htailElementRows 2 symbolCode).mpr
          constructor
          · dsimp only [tail]
            simp only [List.length_cons]
            omega
          · cases body with
            | nil => simp at hlength
            | cons first rest =>
                cases rest with
                | nil => simp at hlength
                | cons second rest =>
                    simp [tail, symbolCode, compactTokenAt]
        exact Or.inr ⟨hatOne, hatTwo, by
          simpa [CompactSymbolPAAxiomTagInvalid, arity, symbolCode]
            using hinvalid⟩
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le tail).trans htailWeight
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodeSymbolPAFailureBoundarySizeBound inputWeight :=
    hinputSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodeSymbolPAFailureBoundarySizeBound inputWeight :=
    htailSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  let hiddenBound :=
    compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound inputWeight
  have hboundaryToHidden :
      compactCertificateNodeSymbolPAFailureBoundarySizeBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
    omega
  have htokenToHidden :
      compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
    omega
  have hinputToHidden : inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
    omega
  have hinputBoundaryHidden :=
    hinputBoundaryPublic.trans hboundaryToHidden
  have htailBoundaryHidden :=
    htailBoundaryPublic.trans hboundaryToHidden
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
  have hinputFinishValue :
      inputTokens.length <=
        compactCertificateNodeSymbolPAFailureTokenWeightBound inputWeight :=
    (Nat.le_add_right inputTokens.length tailTokens.length).trans
      (by simpa only [tokens, List.length_append] using htokenCount)
  have hinputFinishHidden :
      Nat.size inputTokens.length <= hiddenBound :=
    (natSize_le_of_le hinputFinishValue).trans htokenToHidden
  have htokenCountHidden :
      Nat.size tokens.length <= hiddenBound :=
    (natSize_le_of_le htokenCount).trans htokenToHidden
  have hpaTagHidden : Nat.size paTag <= hiddenBound :=
    hpaTagSize.trans hinputToHidden
  have harityHidden : Nat.size arity <= hiddenBound :=
    haritySize.trans hinputToHidden
  have hsymbolHidden : Nat.size symbolCode <= hiddenBound :=
    hsymbolSize.trans hinputToHidden
  let endpointBound := 2 ^ hiddenBound
  have hbounded :
      CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
        tokenTable width tokens.length 0 inputTokens.length endpointBound := by
    unfold CompactCertificateNodeSymbolPAFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        inputTokens.length, ?_, tokens.length, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        paTag, ?_, arity, ?_, symbolCode, ?_, ?_⟩
    · exact hidden_le_endpoint hinputBoundaryHidden
    · exact hidden_le_endpoint hinputCountHidden
    · exact hidden_le_endpoint (hboundarySizeHidden hinputBoundaryHidden)
    · exact hidden_le_endpoint hinputFinishHidden
    · exact hidden_le_endpoint htokenCountHidden
    · exact hidden_le_endpoint htailBoundaryHidden
    · exact hidden_le_endpoint htailCountHidden
    · exact hidden_le_endpoint (hboundarySizeHidden htailBoundaryHidden)
    · exact hidden_le_endpoint hpaTagHidden
    · exact hidden_le_endpoint harityHidden
    · exact hidden_le_endpoint hsymbolHidden
    · simpa only [coordinates,
        compactCertificateNodeSymbolPAFailureEndpointCoordinatesOfValues]
        using hgraph
  let publicBound :=
    compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound :=
    htable.trans (by
      unfold publicBound
        compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound :=
    (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound :=
    htokenCountHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
        compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
      omega)
  have hinputFinishPublic :
      Nat.size inputTokens.length <= publicBound :=
    hinputFinishHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
        compactCertificateNodeSymbolPAFailureHiddenCoordinateSizeBound
      omega)
  have hendpointPublic : Nat.size endpointBound <= publicBound := by
    rw [Nat.size_pow]
    dsimp only [publicBound, hiddenBound]
    unfold compactCertificateNodeSymbolPAFailurePublicCoordinateSizeBound
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
  exists_compactCertificateNodeSymbolPAFailureEndpointBoundedGraph_with_publicBounds

end FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailurePublicBounds
