import integration.FoundationCompactNumericListedDirectNatListConsRows
import integration.FoundationCompactNumericListedDirectNatListWitnessRows
import integration.FoundationCompactNumericListedNodeFields

/-!
# Exact endpoint for the simple structural-certificate nodes

Structural-certificate tags 0, 2, and 3 consume exactly their leading tag and
return an empty PA-axiom payload together with the remaining token suffix.  The
input and suffix are represented in one fixed-width token table.  The graph is
both sound for the public parser and constructible from every successful public
run in these three branches.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactNumericSyntaxValueParser
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

structure CompactCertificateNodeSimpleEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  suffixBoundary : Nat
  suffixCount : Nat
  suffixBoundarySize : Nat

def CompactCertificateNodeSimpleEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount suffixStart coordinates.suffixCount suffixFinish
        coordinates.suffixBoundary coordinates.suffixBoundarySize ∧
    (tag = 0 ∨ tag = 2 ∨ tag = 3) ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.suffixBoundary coordinates.suffixCount
        coordinates.inputBoundary coordinates.inputCount tag

def compactCertificateNodeSimpleEndpointGraphDef : 𝚺₀.Semisentence 14 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish suffixStart suffixFinish tag
      inputBoundary inputCount inputBoundarySize
      suffixBoundary suffixCount suffixBoundarySize.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount suffixStart suffixCount suffixFinish
        suffixBoundary suffixBoundarySize ∧
    (tag = 0 ∨ tag = 2 ∨ tag = 3) ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        suffixBoundary suffixCount inputBoundary inputCount tag”

def compactCertificateNodeSimpleEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    Fin 14 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    suffixStart, suffixFinish, tag,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.suffixBoundary, coordinates.suffixCount,
    coordinates.suffixBoundarySize]

@[simp] theorem compactCertificateNodeSimpleEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat)
    (coordinates : CompactCertificateNodeSimpleEndpointCoordinates) :
    compactCertificateNodeSimpleEndpointGraphDef.val.Evalb
        (compactCertificateNodeSimpleEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag coordinates) ↔
      CompactCertificateNodeSimpleEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates := by
  let env := compactCertificateNodeSimpleEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag coordinates
  change compactCertificateNodeSimpleEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #3, #9, #4, #8, #10]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hsuffixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #5, #12, #6, #11, #13]) =
        ![tokenTable, width, tokenCount, suffixStart,
          coordinates.suffixCount, suffixFinish,
          coordinates.suffixBoundary, coordinates.suffixBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2, #11, #12, #8, #9, #7]) =
        ![tokenTable, width, tokenCount,
          coordinates.suffixBoundary, coordinates.suffixCount,
          coordinates.inputBoundary, coordinates.inputCount, tag] := by
    funext index
    fin_cases index <;> rfl
  have htagValue : env 7 = tag := rfl
  simp [compactCertificateNodeSimpleEndpointGraphDef,
    CompactCertificateNodeSimpleEndpointGraph,
    hinputEnv, hsuffixEnv, hconsEnv, htagValue] <;> tauto

theorem compactCertificateNodeSimpleEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeSimpleEndpointGraphDef.val := by
  simp [compactCertificateNodeSimpleEndpointGraphDef]

theorem CompactCertificateNodeSimpleEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      suffixStart suffixFinish tag : Nat}
    {coordinates : CompactCertificateNodeSimpleEndpointCoordinates}
    (hgraph : CompactCertificateNodeSimpleEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        suffixStart suffixFinish tag coordinates) :
    ∃ input suffix : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount suffixStart suffixFinish suffix ∧
      compactStructuralCertificateNodeParser input =
        some (tag, ([], suffix)) := by
  rcases hgraph with ⟨hinputRows, hsuffixRows, htag, hconsRows⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases hsuffixRows.realize with
    ⟨suffix, hsuffixCount, hsuffixLayout, hsuffixElementRows⟩
  have hconsRows' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.suffixBoundary suffix.length
        coordinates.inputBoundary input.length tag := by
    simpa only [hinputCount, hsuffixCount] using hconsRows
  have hinput : input = tag :: suffix :=
    hconsRows'.eq_cons_of_rows hsuffixElementRows hinputElementRows
  refine ⟨input, suffix, hinputLayout, hsuffixLayout, ?_⟩
  rcases htag with rfl | rfl | rfl <;>
    simp [compactStructuralCertificateNodeParser, hinput]

theorem compactStructuralCertificateNodeParser_simple_result
    {input : List Nat} {tag : Nat} {axiomTokens suffix : List Nat}
    (hparser : compactStructuralCertificateNodeParser input =
      some (tag, (axiomTokens, suffix)))
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    axiomTokens = [] ∧ input = tag :: suffix := by
  cases input with
  | nil =>
      simp [compactStructuralCertificateNodeParser] at hparser
  | cons head tail =>
      by_cases h0 : head = 0
      · subst head
        have hparseEq :
            some (0, (([] : List Nat), tail)) =
              some (tag, (axiomTokens, suffix)) := by
          simpa [compactStructuralCertificateNodeParser] using hparser
        have hnode := Option.some.inj hparseEq
        have htagEq : tag = 0 :=
          (congrArg (fun node => node.1) hnode).symm
        have hfields := congrArg (fun node => node.2) hnode
        have haxiomEq : axiomTokens = [] :=
          (congrArg (fun fields => fields.1) hfields).symm
        have hsuffixEq : suffix = tail :=
          (congrArg (fun fields => fields.2) hfields).symm
        subst tag
        subst axiomTokens
        subst suffix
        exact ⟨rfl, rfl⟩
      by_cases h1 : head = 1
      · subst head
        cases hpa : compactPAAxiomCertificateTokenParser tail with
        | none =>
            simp [compactStructuralCertificateNodeParser, h0, hpa] at hparser
        | some after =>
            have hparseEq :
                some (1, (consumedTokenPrefix tail after, after)) =
                  some (tag, (axiomTokens, suffix)) := by
              simpa [compactStructuralCertificateNodeParser, h0, hpa]
                using hparser
            have hnode := Option.some.inj hparseEq
            have htagEq : tag = 1 :=
              (congrArg (fun node => node.1) hnode).symm
            omega
      by_cases h2 : head = 2
      · subst head
        have hparseEq :
            some (2, (([] : List Nat), tail)) =
              some (tag, (axiomTokens, suffix)) := by
          simpa [compactStructuralCertificateNodeParser, h0] using hparser
        have hnode := Option.some.inj hparseEq
        have htagEq : tag = 2 :=
          (congrArg (fun node => node.1) hnode).symm
        have hfields := congrArg (fun node => node.2) hnode
        have haxiomEq : axiomTokens = [] :=
          (congrArg (fun fields => fields.1) hfields).symm
        have hsuffixEq : suffix = tail :=
          (congrArg (fun fields => fields.2) hfields).symm
        subst tag
        subst axiomTokens
        subst suffix
        exact ⟨rfl, rfl⟩
      by_cases h3 : head = 3
      · subst head
        have hparseEq :
            some (3, (([] : List Nat), tail)) =
              some (tag, (axiomTokens, suffix)) := by
          simpa [compactStructuralCertificateNodeParser, h0, h1, h2]
            using hparser
        have hnode := Option.some.inj hparseEq
        have htagEq : tag = 3 :=
          (congrArg (fun node => node.1) hnode).symm
        have hfields := congrArg (fun node => node.2) hnode
        have haxiomEq : axiomTokens = [] :=
          (congrArg (fun fields => fields.1) hfields).symm
        have hsuffixEq : suffix = tail :=
          (congrArg (fun fields => fields.2) hfields).symm
        subst tag
        subst axiomTokens
        subst suffix
        exact ⟨rfl, rfl⟩
      simp [compactStructuralCertificateNodeParser,
        h0, h1, h2, h3] at hparser

theorem exists_compactCertificateNodeSimpleEndpointGraph_of_results_with_inputLayout
    (tag : Nat) (suffix : List Nat)
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeSimpleEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish (tag :: suffix) ∧
        CompactCertificateNodeSimpleEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag coordinates := by
  let input := tag :: suffix
  let inputTokens := compactAdditiveEncode input
  let suffixTokens := compactAdditiveEncode suffix
  let tokens := inputTokens ++ suffixTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
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
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases hsuffixLayout with
    ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have hsuffixRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length suffix.length
        tokens.length suffixBoundary (Nat.size suffixBoundary) :=
    ⟨hsuffixStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsuffixElementRows,
      rfl, hsuffixSize⟩
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
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    inputTokens.length, tokens.length, coordinates,
    by simpa [input] using hinputLayoutExact, ?_⟩
  exact ⟨hinputRows, hsuffixRows, htag, hconsRows⟩

theorem exists_compactCertificateNodeSimpleEndpointGraph_of_results
    (tag : Nat) (suffix : List Nat)
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeSimpleEndpointCoordinates,
      CompactCertificateNodeSimpleEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates := by
  rcases
      exists_compactCertificateNodeSimpleEndpointGraph_of_results_with_inputLayout
        tag suffix htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      suffixStart, suffixFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    suffixStart, suffixFinish, coordinates, hgraph⟩

theorem exists_compactCertificateNodeSimpleEndpointGraph_of_success_with_inputLayout
    {input : List Nat} {tag : Nat} {axiomTokens suffix : List Nat}
    (hparser : compactStructuralCertificateNodeParser input =
      some (tag, (axiomTokens, suffix)))
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeSimpleEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeSimpleEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            suffixStart suffixFinish tag coordinates := by
  rcases compactStructuralCertificateNodeParser_simple_result
      hparser htag with ⟨_haxiomTokens, hinput⟩
  subst input
  exact
    exists_compactCertificateNodeSimpleEndpointGraph_of_results_with_inputLayout
      tag suffix htag

theorem exists_compactCertificateNodeSimpleEndpointGraph_of_success
    {input : List Nat} {tag : Nat} {axiomTokens suffix : List Nat}
    (hparser : compactStructuralCertificateNodeParser input =
      some (tag, (axiomTokens, suffix)))
    (htag : tag = 0 ∨ tag = 2 ∨ tag = 3) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ suffixStart suffixFinish,
    ∃ coordinates : CompactCertificateNodeSimpleEndpointCoordinates,
      CompactCertificateNodeSimpleEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          suffixStart suffixFinish tag coordinates := by
  rcases
      exists_compactCertificateNodeSimpleEndpointGraph_of_success_with_inputLayout
        hparser htag with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      suffixStart, suffixFinish, coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    suffixStart, suffixFinish, coordinates, hgraph⟩

#print axioms compactCertificateNodeSimpleEndpointGraphDef_spec
#print axioms compactCertificateNodeSimpleEndpointGraphDef_sigmaZero
#print axioms CompactCertificateNodeSimpleEndpointGraph.sound
#print axioms compactStructuralCertificateNodeParser_simple_result
#print axioms exists_compactCertificateNodeSimpleEndpointGraph_of_results_with_inputLayout
#print axioms exists_compactCertificateNodeSimpleEndpointGraph_of_results
#print axioms exists_compactCertificateNodeSimpleEndpointGraph_of_success_with_inputLayout
#print axioms exists_compactCertificateNodeSimpleEndpointGraph_of_success

end FoundationCompactNumericListedDirectCertificateNodeSimpleEndpoint
