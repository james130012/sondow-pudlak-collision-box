import integration.FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula
import integration.FoundationCompactNumericListedDirectVerifierTaskFieldRealization
import integration.FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

/-!
# Public task coordinates for a successful proof root

The successful root parser graph already exposes the input and the root slice.
This refinement makes the verifier-task rows inside that slice public arithmetic
coordinates, so leaf and non-leaf verifier state graphs can share them.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootTaggedSuccessExposedFormula

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectProofRootSuccessBoundedFormula
open FoundationCompactNumericListedDirectProofRootTaggedSuccessBoundedFormula

def CompactProofRootTaggedSuccessExposedGraph
    (tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
      proofTag endpointBound gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish
      witnessCount suffixCount gammaBoundarySize : Nat) : Prop :=
  CompactProofRootTaggedSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
        proofTag endpointBound ∧
    CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      (compactNumericVerifierTaskRowCoordinatesOf
        rootStart rootFinish proofTag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount witnessFinish
        witnessCount suffixCount)
      { gammaBoundarySize := gammaBoundarySize }

def compactProofRootTaggedSuccessExposedGraphDef : 𝚺₀.Semisentence 20 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
      proofTag endpointBound gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish
      witnessCount suffixCount gammaBoundarySize.
    !(compactProofRootTaggedSuccessBoundedGraphDef)
      tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
        proofTag endpointBound ∧
    !(compactNumericVerifierTaskCoreGraphDef)
      tokenTable width tokenCount rootStart rootFinish proofTag
      gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize”

@[simp] theorem compactProofRootTaggedSuccessExposedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
      proofTag endpointBound gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish
      witnessCount suffixCount gammaBoundarySize : Nat) :
    compactProofRootTaggedSuccessExposedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish, rootStart,
          rootFinish, proofTag, endpointBound, gammaFinish, gammaCount,
          gammaBoundary, firstFinish, firstCount, secondFinish, secondCount,
          witnessFinish, witnessCount, suffixCount, gammaBoundarySize] ↔
      CompactProofRootTaggedSuccessExposedGraph
        tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
          proofTag endpointBound gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount witnessFinish
          witnessCount suffixCount gammaBoundarySize := by
  let env : Fin 20 → Nat :=
    ![tokenTable, width, tokenCount, inputStart, inputFinish, rootStart,
      rootFinish, proofTag, endpointBound, gammaFinish, gammaCount,
      gammaBoundary, firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount, gammaBoundarySize]
  change compactProofRootTaggedSuccessExposedGraphDef.val.Evalb env ↔ _
  have htaggedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #3, #4, #5, #6, #7, #8]) =
        ![tokenTable, width, tokenCount, inputStart, inputFinish, rootStart,
          rootFinish, proofTag, endpointBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcoreEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2, #5, #6, #7, #9, #10, #11,
          #12, #13, #14, #15, #16, #17, #18, #19]) =
        ![tokenTable, width, tokenCount, rootStart, rootFinish, proofTag,
          gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
          secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
          gammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcore :
      (Semiformula.Eval
          ![tokenTable, width, tokenCount, rootStart, rootFinish, proofTag,
            gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
            secondFinish, secondCount, witnessFinish, witnessCount,
            suffixCount, gammaBoundarySize]
          Empty.elim)
        compactNumericVerifierTaskCoreGraphDef.val ↔
      CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
        (compactNumericVerifierTaskRowCoordinatesOf
          rootStart rootFinish proofTag gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount witnessFinish
          witnessCount suffixCount)
        { gammaBoundarySize := gammaBoundarySize } := by
    simpa [compactNumericVerifierTaskCoreFormulaEnvironment] using
      (compactNumericVerifierTaskCoreGraphDef_spec
        tokenTable width tokenCount rootStart rootFinish proofTag
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize)
  simp [compactProofRootTaggedSuccessExposedGraphDef,
    CompactProofRootTaggedSuccessExposedGraph,
    compactNumericVerifierTaskRowCoordinatesOf, htaggedEnv, hcoreEnv,
    hcore]

theorem compactProofRootTaggedSuccessExposedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactProofRootTaggedSuccessExposedGraphDef.val := by
  simp [compactProofRootTaggedSuccessExposedGraphDef]

theorem CompactProofRootTaggedSuccessExposedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
      proofTag endpointBound gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount witnessFinish
      witnessCount suffixCount gammaBoundarySize : Nat}
    (hgraph : CompactProofRootTaggedSuccessExposedGraph
      tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
        proofTag endpointBound gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount witnessFinish
        witnessCount suffixCount gammaBoundarySize) :
    ∃ input : List Nat,
      ∃ root realizedRoot :
        FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish root ∧
      compactListedProofNodeFieldsParser input = some root ∧
      root.1 = proofTag ∧
      CompactNumericVerifierTaskDirectLayout
        tokenTable width tokenCount rootStart rootFinish realizedRoot ∧
      realizedRoot = root := by
  rcases hgraph.1.sound with ⟨input, root, hinput, hroot, hparser, htag⟩
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hgraph.2 with
    ⟨realizedRoot, hrealized, _htag, _hgammaRows, _hgammaCount,
      _hfirst, _hfirstCount, _hsecond, _hsecondCount, _hwitness,
      _hwitnessCount, _hsuffix, _hsuffixCount⟩
  have hsame : realizedRoot = root :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq hgraph.2 hroot hrealized
  exact ⟨input, root, realizedRoot, hinput, hroot, hparser, htag,
    hrealized, hsame⟩

theorem CompactProofRootTaggedSuccessBoundedGraph.exists_exposed
    {tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
      proofTag endpointBound : Nat}
    (hgraph : CompactProofRootTaggedSuccessBoundedGraph
      tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
        proofTag endpointBound) :
    ∃ gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
      CompactProofRootTaggedSuccessExposedGraph
        tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
          proofTag endpointBound gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount witnessFinish
          witnessCount suffixCount gammaBoundarySize := by
  rcases hgraph.sound with ⟨_input, root, _hinput, hroot, _hparser, hrootTag⟩
  rcases CompactNumericVerifierTaskDirectLayout.toCoreGraph hroot with
    ⟨coordinates, sizeWitness, hstart, hfinish, htag, hcore⟩
  rcases coordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount, witnessFinish,
      witnessCount, suffixCount⟩
  rcases sizeWitness with ⟨gammaBoundarySize⟩
  change start = rootStart at hstart
  change finish = rootFinish at hfinish
  change tag = root.1 at htag
  subst start
  subst finish
  have htag' : tag = proofTag := htag.trans hrootTag
  rw [htag'] at hcore
  exact ⟨gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize, hgraph, hcore⟩

theorem exists_compactProofRootTaggedSuccessExposedGraph_of_parser_success
    {input : List Nat}
    {root : FoundationCompactNumericListedRootFieldsDecomposition.CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root) :
    ∃ tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
      endpointBound gammaFinish gammaCount gammaBoundary firstFinish
      firstCount secondFinish secondCount witnessFinish witnessCount
      suffixCount gammaBoundarySize,
      CompactProofRootTaggedSuccessExposedGraph
        tokenTable width tokenCount inputStart inputFinish rootStart rootFinish
          root.1 endpointBound gammaFinish gammaCount gammaBoundary
          firstFinish firstCount secondFinish secondCount witnessFinish
          witnessCount suffixCount gammaBoundarySize := by
  rcases
      exists_compactProofRootSuccessBoundedGraph_of_parser_success_with_inputLayout
        hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish, rootStart,
      rootFinish, endpointBound, hinput, hsuccess⟩
  rcases CompactProofRootSuccessBoundedGraph.exists_tagged hsuccess with
    ⟨proofTag, htagged⟩
  have hproofTag : proofTag = root.1 := by
    rcases htagged.sound with ⟨parsedInput, parsedRoot, hparsedInput, _hroot,
      hparsed, htag⟩
    have hinputs : parsedInput = input :=
      (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hinput hparsedInput).1
    have hroots : parsedRoot = root := by
      subst parsedInput
      exact Option.some.inj (hparsed.symm.trans hparser)
    simpa [hroots] using htag.symm
  subst proofTag
  rcases
      FoundationCompactNumericListedDirectProofRootTaggedSuccessExposedFormula.CompactProofRootTaggedSuccessBoundedGraph.exists_exposed
        htagged with
    ⟨gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, hexposed⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish, rootStart,
    rootFinish, endpointBound, gammaFinish, gammaCount, gammaBoundary,
    firstFinish, firstCount, secondFinish, secondCount, witnessFinish,
    witnessCount, suffixCount, gammaBoundarySize, hexposed⟩

#print axioms compactProofRootTaggedSuccessExposedGraphDef_spec
#print axioms compactProofRootTaggedSuccessExposedGraphDef_sigmaZero
#print axioms CompactProofRootTaggedSuccessExposedGraph.sound
#print axioms CompactProofRootTaggedSuccessBoundedGraph.exists_exposed
#print axioms exists_compactProofRootTaggedSuccessExposedGraph_of_parser_success

end FoundationCompactNumericListedDirectProofRootTaggedSuccessExposedFormula
