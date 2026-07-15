import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint

/-!
# Exact endpoint for malformed symbol PA certificates

For PA tags 3 and 4, failure is exactly a tail shorter than three tokens or an
invalid function/relation symbol code in tail positions 1 and 2.  The outer
structural tag 1 and the complete PA tail share one fixed-width token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactArithmeticSymbolCode
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectArithmeticSymbolCodeFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

def CompactSymbolPAAxiomTagInvalid
    (paTag arity symbolCode : Nat) : Prop :=
  (paTag = 3 ∧ ¬ ArithmeticFuncCodeValid arity symbolCode) ∨
    (paTag = 4 ∧ ¬ ArithmeticRelCodeValid arity symbolCode)

structure CompactCertificateNodeSymbolPAFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailStart : Nat
  tailFinish : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  paTag : Nat
  arity : Nat
  symbolCode : Nat

def CompactCertificateNodeSymbolPAFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates) : Prop :=
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
    CompactAdditiveNatListAtRows tokenTable width tokenCount
      coordinates.tailBoundary coordinates.tailCount 0 coordinates.paTag ∧
    (coordinates.paTag = 3 ∨ coordinates.paTag = 4) ∧
    (coordinates.tailCount < 3 ∨
      (CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.tailBoundary coordinates.tailCount 1 coordinates.arity ∧
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.tailBoundary coordinates.tailCount 2 coordinates.symbolCode ∧
        CompactSymbolPAAxiomTagInvalid
          coordinates.paTag coordinates.arity coordinates.symbolCode))

def compactCertificateNodeSymbolPAFailureEndpointGraphDef :
    𝚺₀.Semisentence 16 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      paTag arity symbolCode.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount tailStart tailCount tailFinish
        tailBoundary tailBoundarySize ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount inputBoundary inputCount 1 ∧
    !(compactAdditiveNatListAtRowsDef)
      tokenTable width tokenCount tailBoundary tailCount 0 paTag ∧
    (paTag = 3 ∨ paTag = 4) ∧
    (tailCount < 3 ∨
      (!(compactAdditiveNatListAtRowsDef)
          tokenTable width tokenCount tailBoundary tailCount 1 arity ∧
        !(compactAdditiveNatListAtRowsDef)
          tokenTable width tokenCount tailBoundary tailCount 2 symbolCode ∧
        ((paTag = 3 ∧
            ¬ !(compactAdditiveArithmeticFuncCodeValidDef) arity symbolCode) ∨
          (paTag = 4 ∧
            ¬ !(compactAdditiveArithmeticRelCodeValidDef) arity symbolCode))))”

def compactCertificateNodeSymbolPAFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates) :
    Fin 16 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailStart, coordinates.tailFinish,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize,
    coordinates.paTag, coordinates.arity, coordinates.symbolCode]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeSymbolPAFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates) :
    compactCertificateNodeSymbolPAFailureEndpointGraphDef.val.Evalb
        (compactCertificateNodeSymbolPAFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish coordinates) ↔
      CompactCertificateNodeSymbolPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  let env := compactCertificateNodeSymbolPAFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish coordinates
  change compactCertificateNodeSymbolPAFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #3, #6, #4, #5, #7]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #8, #11, #9, #10, #12]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #10, #11, #5, #6, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAFailureEndpointEnvironment]
  have hatZeroEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #10, #11, ‘0’, #13]) =
        ![tokenTable, width, tokenCount, coordinates.tailBoundary,
          coordinates.tailCount, 0, coordinates.paTag] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAFailureEndpointEnvironment]
  have hatOneEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #10, #11, ‘1’, #14]) =
        ![tokenTable, width, tokenCount, coordinates.tailBoundary,
          coordinates.tailCount, 1, coordinates.arity] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAFailureEndpointEnvironment]
  have hatTwoEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #10, #11, ‘2’, #15]) =
        ![tokenTable, width, tokenCount, coordinates.tailBoundary,
          coordinates.tailCount, 2, coordinates.symbolCode] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeSymbolPAFailureEndpointEnvironment]
  have hfuncEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#14 : Semiterm ℒₒᵣ Empty 16), #15]) =
        ![coordinates.arity, coordinates.symbolCode] := by
    funext index
    fin_cases index <;> rfl
  have htailCount : env 11 = coordinates.tailCount := rfl
  have hpaTag : env 13 = coordinates.paTag := rfl
  have hatZeroSpec :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, coordinates.tailBoundary,
            coordinates.tailCount, 0, coordinates.paTag]
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.tailBoundary coordinates.tailCount 0
          coordinates.paTag := by
    simpa [compactAdditiveNatListAtRowsEnvironment] using
      (compactAdditiveNatListAtRowsDef_spec tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount 0 coordinates.paTag)
  have hatOneSpec :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, coordinates.tailBoundary,
            coordinates.tailCount, 1, coordinates.arity]
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.tailBoundary coordinates.tailCount 1
          coordinates.arity := by
    simpa [compactAdditiveNatListAtRowsEnvironment] using
      (compactAdditiveNatListAtRowsDef_spec tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount 1 coordinates.arity)
  have hatTwoSpec :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, coordinates.tailBoundary,
            coordinates.tailCount, 2, coordinates.symbolCode]
          Empty.elim) compactAdditiveNatListAtRowsDef.val ↔
        CompactAdditiveNatListAtRows tokenTable width tokenCount
          coordinates.tailBoundary coordinates.tailCount 2
          coordinates.symbolCode := by
    simpa [compactAdditiveNatListAtRowsEnvironment] using
      (compactAdditiveNatListAtRowsDef_spec tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount 2
        coordinates.symbolCode)
  simp [compactCertificateNodeSymbolPAFailureEndpointGraphDef,
    CompactCertificateNodeSymbolPAFailureEndpointGraph,
    CompactSymbolPAAxiomTagInvalid,
    hinputEnv, htailEnv, hconsEnv, hatZeroEnv, hatOneEnv, hatTwoEnv,
    hfuncEnv, htailCount, hpaTag]
  rw [hatZeroSpec, hatOneSpec, hatTwoSpec]
  intro _ _ _
  rfl

theorem compactCertificateNodeSymbolPAFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSymbolPAFailureEndpointGraphDef.val := by
  simp [compactCertificateNodeSymbolPAFailureEndpointGraphDef]

theorem CompactCertificateNodeSymbolPAFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodeSymbolPAFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactStructuralCertificateNodeParser input = none := by
  rcases hgraph with
    ⟨hinputRows, htailRows, houterCons, hatZero, htag,
      hshort | ⟨hatOne, hatTwo, hinvalid⟩⟩
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
    have hatZero' : CompactAdditiveNatListAtRows
        tokenTable width tokenCount coordinates.tailBoundary tail.length
          0 coordinates.paTag := by
      simpa only [htailCount] using hatZero
    have hzeroData :=
      (compactAdditiveNatListAtRows_iff_getI htailElementRows
        0 coordinates.paTag).mp hatZero'
    have htailNonempty : 0 < tail.length := hzeroData.1
    have hzero := hzeroData.2
    obtain ⟨body, htail⟩ : ∃ body, tail = coordinates.paTag :: body := by
      cases tail with
      | nil => simp at htailNonempty
      | cons head body =>
          have hhead : head = coordinates.paTag := by simpa using hzero
          subst head
          exact ⟨body, rfl⟩
    have hbodyShort : body.length < 2 := by
      simp [htail] at htailCount
      omega
    have hnotLength : ¬ 2 ≤ body.length := by omega
    refine ⟨input, hinputLayout, ?_⟩
    rcases htag with htag | htag <;> rw [htag] at htail <;>
      rw [hinput, htail] <;>
      simp [compactStructuralCertificateNodeParser,
        compactPAAxiomCertificateTokenParser, hnotLength]
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
    have hatZero' : CompactAdditiveNatListAtRows
        tokenTable width tokenCount coordinates.tailBoundary tail.length
          0 coordinates.paTag := by
      simpa only [htailCount] using hatZero
    have hatOne' : CompactAdditiveNatListAtRows
        tokenTable width tokenCount coordinates.tailBoundary tail.length
          1 coordinates.arity := by
      simpa only [htailCount] using hatOne
    have hatTwo' : CompactAdditiveNatListAtRows
        tokenTable width tokenCount coordinates.tailBoundary tail.length
          2 coordinates.symbolCode := by
      simpa only [htailCount] using hatTwo
    have hzeroData :=
      (compactAdditiveNatListAtRows_iff_getI htailElementRows
        0 coordinates.paTag).mp hatZero'
    have honeData :=
      (compactAdditiveNatListAtRows_iff_getI htailElementRows
        1 coordinates.arity).mp hatOne'
    have htwoData :=
      (compactAdditiveNatListAtRows_iff_getI htailElementRows
        2 coordinates.symbolCode).mp hatTwo'
    have hzero := hzeroData.2
    have hone := honeData.2
    have htwo := htwoData.2
    cases tail with
    | nil => simp at hzeroData
    | cons head tail =>
      cases tail with
      | nil => simp at honeData
      | cons arity tail =>
        cases tail with
        | nil => simp at htwoData
        | cons symbolCode suffix =>
          simp at hzero hone htwo
          subst head
          subst arity
          subst symbolCode
          refine ⟨input, hinputLayout, ?_⟩
          rcases hinvalid with ⟨htag, hinvalid⟩ | ⟨htag, hinvalid⟩
          · rw [hinput, htag]
            simp [compactStructuralCertificateNodeParser,
              compactPAAxiomCertificateTokenParser, compactTokenAt, hinvalid]
          · rw [hinput, htag]
            simp [compactStructuralCertificateNodeParser,
              compactPAAxiomCertificateTokenParser, compactTokenAt, hinvalid]

theorem exists_compactCertificateNodeSymbolPAFailureEndpointGraph_with_inputLayout
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
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: paTag :: body) ∧
        CompactCertificateNodeSymbolPAFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish coordinates := by
  let tail := paTag :: body
  let input := 1 :: tail
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
  have hatZero : CompactAdditiveNatListAtRows
      tokenTable width tokens.length tailBoundary tail.length 0 paTag := by
    apply (compactAdditiveNatListAtRows_iff_getI
      htailElementRows 0 paTag).mpr
    simp [tail]
  let arity := compactTokenAt 0 body
  let symbolCode := compactTokenAt 1 body
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
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    coordinates, by simpa [input, tail] using hinputLayoutExact,
    hinputRows, htailRows, houterCons, hatZero, htag, ?_⟩
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
    · have hlength : 2 ≤ body.length := by omega
      have hatOne : CompactAdditiveNatListAtRows
          tokenTable width tokens.length tailBoundary tail.length 1 arity := by
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
          tokenTable width tokens.length tailBoundary tail.length 2 symbolCode := by
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

theorem exists_compactCertificateNodeSymbolPAFailureEndpointGraph
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
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodeSymbolPAFailureEndpointCoordinates,
      CompactCertificateNodeSymbolPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases exists_compactCertificateNodeSymbolPAFailureEndpointGraph_with_inputLayout
      paTag body htag hfailure with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates, hgraph⟩

#print axioms compactCertificateNodeSymbolPAFailureEndpointGraphDef_spec
#print axioms compactCertificateNodeSymbolPAFailureEndpointGraphDef_sigmaZero
#print axioms CompactCertificateNodeSymbolPAFailureEndpointGraph.sound
#print axioms exists_compactCertificateNodeSymbolPAFailureEndpointGraph

end FoundationCompactNumericListedDirectCertificateNodeSymbolPAFailureEndpoint
