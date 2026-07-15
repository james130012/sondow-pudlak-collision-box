import integration.FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula

/-!
# Proof-root success with the decoded tag exposed

The aggregate proof-root success graph exposes the decoded root slice but not
its tag.  This refinement reads the first token of that exact slice.  Token
table determinacy then identifies the public tag with the tag of the root
returned by the public parser.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula

def CompactProofRootTaggedSuccessBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish proofTag endpointBound : Nat) : Prop :=
  CompactProofRootSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish endpointBound ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount rootStart proofTag (rootStart + 1)

def compactProofRootTaggedSuccessBoundedGraphDef :
    𝚺₀.Semisentence 9 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish proofTag endpointBound.
    !(compactProofRootSuccessBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish endpointBound ∧
    !(compactAdditiveTokenCellDef)
      tokenTable width tokenCount rootStart proofTag (rootStart + 1)”

@[simp] theorem compactProofRootTaggedSuccessBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish proofTag endpointBound : Nat) :
    compactProofRootTaggedSuccessBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, proofTag, endpointBound] ↔
      CompactProofRootTaggedSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish proofTag endpointBound := by
  have hsuccessEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, inputStart, inputFinish,
            rootStart, rootFinish, proofTag, endpointBound]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2, #3, #4,
          #5, #6, #8]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          rootStart, rootFinish, endpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htagEnv :
      (Semiterm.val
          ![tokenTable, width, tokenCount, inputStart, inputFinish,
            rootStart, rootFinish, proofTag, endpointBound]
          Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 9), #1, #2, #5, #7,
          ‘(#5 + 1)’]) =
        ![tokenTable, width, tokenCount,
          rootStart, proofTag, rootStart + 1] := by
    funext coordinate
    fin_cases coordinate <;> simp
  simp [compactProofRootTaggedSuccessBoundedGraphDef,
    CompactProofRootTaggedSuccessBoundedGraph, hsuccessEnv, htagEnv]

theorem compactProofRootTaggedSuccessBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootTaggedSuccessBoundedGraphDef.val := by
  simp [compactProofRootTaggedSuccessBoundedGraphDef]

theorem CompactProofRootTaggedSuccessBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish proofTag endpointBound : Nat}
    (hgraph : CompactProofRootTaggedSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish proofTag endpointBound) :
    ∃ input : List Nat, ∃ root : CompactNumericProofRoot,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      compactListedProofNodeFieldsParser input = some root ∧
      root.1 = proofTag := by
  rcases hgraph.1.sound with
    ⟨input, root, hinput, hroot, hparser⟩
  rcases hroot with ⟨fieldsStart, hrootTag, hfields⟩
  have htag : root.1 = proofTag :=
    (CompactAdditiveTokenCell.value_eq_tableValue hrootTag).trans
      (CompactAdditiveTokenCell.value_eq_tableValue hgraph.2).symm
  exact ⟨input, root, hinput, ⟨fieldsStart, hrootTag, hfields⟩,
    hparser, htag⟩

theorem CompactProofRootSuccessBoundedGraph.exists_tagged
    {tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish endpointBound : Nat}
    (hgraph : CompactProofRootSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        rootStart rootFinish endpointBound) :
    ∃ proofTag,
      CompactProofRootTaggedSuccessBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish proofTag endpointBound := by
  rcases hgraph.sound with
    ⟨_input, root, _hinput, hroot, _hparser⟩
  rcases hroot with ⟨fieldsStart, htag, _hfields⟩
  have hfieldsStart : fieldsStart = rootStart + 1 := htag.2.1
  subst fieldsStart
  exact ⟨root.1, hgraph, htag⟩

#print axioms compactProofRootTaggedSuccessBoundedGraphDef_spec
#print axioms compactProofRootTaggedSuccessBoundedGraphDef_sigmaZero
#print axioms CompactProofRootTaggedSuccessBoundedGraph.sound
#print axioms CompactProofRootSuccessBoundedGraph.exists_tagged

end FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
