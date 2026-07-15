import integration.FoundationCompactNumericListedDirectCertificateNodeOuterFailureEndpoint

/-!
# Exact endpoint for immediate PA-certificate failure

The PA-certificate parser fails immediately on an empty tail and on a leading
PA tag strictly larger than 22.  Both cases include the outer structural tag 1.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

structure CompactCertificateNodePAImmediateFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailStart : Nat
  tailFinish : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  bodyStart : Nat
  bodyFinish : Nat
  bodyBoundary : Nat
  bodyCount : Nat
  bodyBoundarySize : Nat
  paTag : Nat

def CompactCertificateNodePAImmediateFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
        coordinates.tailFinish coordinates.tailBoundary
        coordinates.tailBoundarySize ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount
        coordinates.inputBoundary coordinates.inputCount 1 ∧
    (coordinates.tailCount = 0 ∨
      (CompactAdditiveNatListWitnessRows
          tokenTable width tokenCount coordinates.bodyStart coordinates.bodyCount
            coordinates.bodyFinish coordinates.bodyBoundary
            coordinates.bodyBoundarySize ∧
        22 < coordinates.paTag ∧
        CompactAdditiveNatListConsRows
          tokenTable width tokenCount
            coordinates.bodyBoundary coordinates.bodyCount
            coordinates.tailBoundary coordinates.tailCount coordinates.paTag))

def compactCertificateNodePAImmediateFailureEndpointGraphDef :
    𝚺₀.Semisentence 19 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      bodyStart bodyFinish bodyBoundary bodyCount bodyBoundarySize paTag.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount tailStart tailCount tailFinish
        tailBoundary tailBoundarySize ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount inputBoundary inputCount 1 ∧
    (tailCount = 0 ∨
      (!(compactAdditiveNatListWitnessRowsDef)
          tokenTable width tokenCount bodyStart bodyCount bodyFinish
            bodyBoundary bodyBoundarySize ∧
        22 < paTag ∧
        !(compactAdditiveNatListConsRowsDef)
          tokenTable width tokenCount
            bodyBoundary bodyCount tailBoundary tailCount paTag))”

def compactCertificateNodePAImmediateFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    Fin 19 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailStart, coordinates.tailFinish,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize,
    coordinates.bodyStart, coordinates.bodyFinish,
    coordinates.bodyBoundary, coordinates.bodyCount,
    coordinates.bodyBoundarySize, coordinates.paTag]

set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodePAImmediateFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates) :
    compactCertificateNodePAImmediateFailureEndpointGraphDef.val.Evalb
        (compactCertificateNodePAImmediateFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish coordinates) ↔
      CompactCertificateNodePAImmediateFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  let env := compactCertificateNodePAImmediateFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish coordinates
  change compactCertificateNodePAImmediateFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #3, #6, #4, #5, #7]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #8, #11, #9, #10, #12]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hbodyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #13, #16, #14, #15, #17]) =
        ![tokenTable, width, tokenCount, coordinates.bodyStart,
          coordinates.bodyCount, coordinates.bodyFinish,
          coordinates.bodyBoundary, coordinates.bodyBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have houterConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #10, #11, #5, #6, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodePAImmediateFailureEndpointEnvironment]
  have hinnerConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 19), #1, #2, #15, #16, #10, #11, #18]) =
        ![tokenTable, width, tokenCount,
          coordinates.bodyBoundary, coordinates.bodyCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.paTag] := by
    funext index
    fin_cases index <;> rfl
  have htailCount : env 11 = coordinates.tailCount := rfl
  have hpaTag : env 18 = coordinates.paTag := rfl
  simp [compactCertificateNodePAImmediateFailureEndpointGraphDef,
    CompactCertificateNodePAImmediateFailureEndpointGraph,
    hinputEnv, htailEnv, hbodyEnv, houterConsEnv, hinnerConsEnv,
    htailCount, hpaTag] <;> tauto

theorem compactCertificateNodePAImmediateFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodePAImmediateFailureEndpointGraphDef.val := by
  simp [compactCertificateNodePAImmediateFailureEndpointGraphDef]

theorem CompactCertificateNodePAImmediateFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodePAImmediateFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactStructuralCertificateNodeParser input = none := by
  rcases hgraph with
    ⟨hinputRows, htailRows, houterCons, hempty | hlarge⟩
  · rcases hinputRows.realize with
      ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
    rcases htailRows.realize with
      ⟨tail, htailCount, _htailLayout, htailElementRows⟩
    have houterCons' : CompactAdditiveNatListConsRows
        tokenTable width tokenCount coordinates.tailBoundary tail.length
          coordinates.inputBoundary input.length 1 := by
      simpa only [hinputCount, htailCount] using houterCons
    have hinput : input = 1 :: tail :=
      houterCons'.eq_cons_of_rows htailElementRows hinputElementRows
    have htailNil : tail = [] := by
      cases tail <;> simp_all
    subst tail
    refine ⟨input, hinputLayout, ?_⟩
    simp [compactStructuralCertificateNodeParser,
      compactPAAxiomCertificateTokenParser, hinput]
  · rcases hlarge with ⟨hbodyRows, htag, hinnerCons⟩
    rcases hinputRows.realize with
      ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
    rcases htailRows.realize with
      ⟨tail, htailCount, _htailLayout, htailElementRows⟩
    rcases hbodyRows.realize with
      ⟨body, hbodyCount, _hbodyLayout, hbodyElementRows⟩
    have houterCons' : CompactAdditiveNatListConsRows
        tokenTable width tokenCount coordinates.tailBoundary tail.length
          coordinates.inputBoundary input.length 1 := by
      simpa only [hinputCount, htailCount] using houterCons
    have hinnerCons' : CompactAdditiveNatListConsRows
        tokenTable width tokenCount coordinates.bodyBoundary body.length
          coordinates.tailBoundary tail.length coordinates.paTag := by
      simpa only [htailCount, hbodyCount] using hinnerCons
    have hinput : input = 1 :: tail :=
      houterCons'.eq_cons_of_rows htailElementRows hinputElementRows
    have htail : tail = coordinates.paTag :: body :=
      hinnerCons'.eq_cons_of_rows hbodyElementRows htailElementRows
    have h3 : coordinates.paTag ≠ 3 := by omega
    have h4 : coordinates.paTag ≠ 4 := by omega
    have h22 : coordinates.paTag ≠ 22 := by omega
    have hnotLt : ¬ coordinates.paTag < 22 := by omega
    refine ⟨input, hinputLayout, ?_⟩
    rw [hinput, htail]
    simp [compactStructuralCertificateNodeParser,
      compactPAAxiomCertificateTokenParser, h3, h4, h22, hnotLt]

theorem exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_empty_with_inputLayout :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish [1] ∧
        CompactCertificateNodePAImmediateFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish coordinates := by
  let tail := ([] : List Nat)
  let input := [1]
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let tokens := inputTokens ++ tailTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
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
      tokenTable width tokens.length inputTokens.length tail.length tokens.length
        tailBoundary (Nat.size tailBoundary) :=
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
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    coordinates, by simpa [input] using hinputLayoutExact,
    hinputRows, htailRows, houterCons, ?_⟩
  exact Or.inl rfl

theorem exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_empty :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates,
      CompactCertificateNodePAImmediateFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases
      exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_empty_with_inputLayout with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates, hgraph⟩

theorem exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_large_with_inputLayout
    (paTag : Nat) (body : List Nat) (htag : 22 < paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: body) ∧
        CompactCertificateNodePAImmediateFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish coordinates := by
  let tail := paTag :: body
  let input := 1 :: tail
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let bodyTokens := compactAdditiveEncode body
  let tokens := inputTokens ++ tailTokens ++ bodyTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ bodyTokens)
  dsimp only at hinputRaw
  have hinputTokenEq :
      [] ++ compactAdditiveEncode input ++ (tailTokens ++ bodyTokens) = tokens := by
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
      (inputTokens ++ tailTokens) ++ compactAdditiveEncode body ++ [] = tokens := by
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
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    coordinates, by simpa [input, tail] using hinputLayoutExact,
    hinputRows, htailRows, houterCons, Or.inr ?_⟩
  exact ⟨hbodyRows, htag, hinnerCons⟩

theorem exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_large
    (paTag : Nat) (body : List Nat) (htag : 22 < paTag) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodePAImmediateFailureEndpointCoordinates,
      CompactCertificateNodePAImmediateFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases
      exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_large_with_inputLayout
        paTag body htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates, hgraph⟩

#print axioms compactCertificateNodePAImmediateFailureEndpointGraphDef_spec
#print axioms compactCertificateNodePAImmediateFailureEndpointGraphDef_sigmaZero
#print axioms CompactCertificateNodePAImmediateFailureEndpointGraph.sound
#print axioms exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_empty
#print axioms exists_compactCertificateNodePAImmediateFailureEndpointGraph_of_large

end FoundationCompactNumericListedDirectCertificateNodePAImmediateFailureEndpoint
