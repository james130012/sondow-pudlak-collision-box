import integration.FoundationCompactNumericListedDirectNatListListWitnessRows
import integration.FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCanonicalCompleteness

/-!
# Self-contained numeric graph for a closed verifier leaf

The public row keeps the context, formula, negated formula, empty-list, and
transform-state boundaries in one token table.  The closed verifier row then
consumes those same boundaries.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafRuleSelfContainedGraph

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectClosedRuleCheck
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCanonicalCompleteness

def CompactNumericVerifierClosedLeafRuleSelfContainedGraph
    (tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      tableWidth valueBound resultBool : Nat) : Prop :=
  CompactAdditiveNatListListWitnessRows
      tokenTable width tokenCount gammaStart gammaCount gammaFinish
      gammaBoundary gammaBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount formulaStart formulaCount formulaFinish
      formulaBoundary formulaBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount negatedStart negatedCount negatedFinish
      negatedBoundary negatedBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
      emptyBoundary emptyBoundarySize ∧
    CompactNumericVerifierClosedLeafRuleRows
      tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool

def compactNumericVerifierClosedLeafRuleSelfContainedGraphDef :
    𝚺₀.Semisentence 29 := .mkSigma
  “tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      tableWidth valueBound resultBool.
    !(compactAdditiveNatListListWitnessRowsDef)
      tokenTable width tokenCount gammaStart gammaCount gammaFinish
      gammaBoundary gammaBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount formulaStart formulaCount formulaFinish
      formulaBoundary formulaBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount negatedStart negatedCount negatedFinish
      negatedBoundary negatedBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount emptyStart 0 emptyFinish
      emptyBoundary emptyBoundarySize ∧
    !(compactNumericVerifierClosedLeafRuleRowsDef)
      tokenTable width tokenCount proofTag certificateTag
      gammaBoundary gammaCount
      formulaStart formulaFinish formulaBoundary formulaCount
      negatedStart negatedFinish negatedBoundary negatedCount
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool”

def compactNumericVerifierClosedLeafRuleSelfContainedGraphEnvironment
    (tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      tableWidth valueBound resultBool : Nat) : Fin 29 → Nat :=
  ![tokenTable, width, tokenCount, proofTag, certificateTag,
    gammaStart, gammaFinish, gammaBoundary, gammaCount, gammaBoundarySize,
    formulaStart, formulaFinish, formulaBoundary, formulaCount,
      formulaBoundarySize,
    negatedStart, negatedFinish, negatedBoundary, negatedCount,
      negatedBoundarySize,
    stateBoundary, stateCount,
    emptyStart, emptyFinish, emptyBoundary, emptyBoundarySize,
    tableWidth, valueBound, resultBool]

@[simp] theorem compactNumericVerifierClosedLeafRuleSelfContainedGraphDef_spec
    (tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      tableWidth valueBound resultBool : Nat) :
    compactNumericVerifierClosedLeafRuleSelfContainedGraphDef.val.Evalb
        (compactNumericVerifierClosedLeafRuleSelfContainedGraphEnvironment
          tokenTable width tokenCount proofTag certificateTag
          gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
          formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
          negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
          stateBoundary stateCount
          emptyStart emptyFinish emptyBoundary emptyBoundarySize
          tableWidth valueBound resultBool) ↔
      CompactNumericVerifierClosedLeafRuleSelfContainedGraph
        tokenTable width tokenCount proofTag certificateTag
        gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
        stateBoundary stateCount
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound resultBool := by
  let env := compactNumericVerifierClosedLeafRuleSelfContainedGraphEnvironment
    tokenTable width tokenCount proofTag certificateTag
    gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
    formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
    negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
    stateBoundary stateCount
    emptyStart emptyFinish emptyBoundary emptyBoundarySize
    tableWidth valueBound resultBool
  have hgammaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #5, #8, #6, #7, #9]) =
      ![tokenTable, width, tokenCount, gammaStart, gammaCount, gammaFinish,
        gammaBoundary, gammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hformulaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #10, #13, #11, #12, #14]) =
      ![tokenTable, width, tokenCount, formulaStart, formulaCount,
        formulaFinish, formulaBoundary, formulaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hnegatedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #15, #18, #16, #17, #19]) =
      ![tokenTable, width, tokenCount, negatedStart, negatedCount,
        negatedFinish, negatedBoundary, negatedBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hemptyEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #22,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 29), #23, #24, #25]) =
      ![tokenTable, width, tokenCount, emptyStart, 0, emptyFinish,
        emptyBoundary, emptyBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hleafEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #3, #4,
          #7, #8, #10, #11, #12, #13, #15, #16, #17, #18, #20, #21,
          #22, #23, #24, #26, #27, #28]) =
      ![tokenTable, width, tokenCount, proofTag, certificateTag,
        gammaBoundary, gammaCount,
        formulaStart, formulaFinish, formulaBoundary, formulaCount,
        negatedStart, negatedFinish, negatedBoundary, negatedCount,
        stateBoundary, stateCount,
        emptyStart, emptyFinish, emptyBoundary,
        tableWidth, valueBound, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierClosedLeafRuleSelfContainedGraphDef,
    CompactNumericVerifierClosedLeafRuleSelfContainedGraph,
    hgammaEnv, hformulaEnv, hnegatedEnv, hemptyEnv, hleafEnv, env]

theorem compactNumericVerifierClosedLeafRuleSelfContainedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierClosedLeafRuleSelfContainedGraphDef.val := by
  simp [compactNumericVerifierClosedLeafRuleSelfContainedGraphDef]

theorem CompactNumericVerifierClosedLeafRuleSelfContainedGraph.sound
    {tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      tableWidth valueBound resultBool : Nat}
    (hgraph : CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      tokenTable width tokenCount proofTag certificateTag
      gammaStart gammaFinish gammaBoundary gammaCount gammaBoundarySize
      formulaStart formulaFinish formulaBoundary formulaCount formulaBoundarySize
      negatedStart negatedFinish negatedBoundary negatedCount negatedBoundarySize
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      tableWidth valueBound resultBool) :
    ∃ Gamma : List (List Nat), ∃ formula negated empty : List Nat,
      Gamma.length = gammaCount ∧
      formula.length = formulaCount ∧
      negated.length = negatedCount ∧
      empty = [] ∧
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount gammaStart gammaFinish Gamma ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          gammaBoundary Gamma ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount formulaStart formulaFinish formula ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          formulaBoundary formula ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount negatedStart negatedFinish negated ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          negatedBoundary negated ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount emptyStart emptyFinish empty ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          emptyBoundary empty ∧
      proofTag = 0 ∧ certificateTag = 0 ∧
      ((∃ parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0,
          formula = compactArithmeticFormulaTokens parsed) →
        resultBool = compactAdditiveBoolTag
          (compactClosedRuleCheck (Gamma, formula))) := by
  rcases hgraph with ⟨hgammaWitness, hformulaWitness, hnegatedWitness,
    hemptyWitness, hleaf⟩
  rcases hgammaWitness.realize with ⟨Gamma, hgammaLength, hgammaLayout,
    hgammaRows⟩
  rcases hformulaWitness.realize with ⟨formula, hformulaLength, hformulaLayout,
    hformulaRows⟩
  rcases hnegatedWitness.realize with ⟨negated, hnegatedLength, hnegatedLayout,
    hnegatedRows⟩
  rcases hemptyWitness.realize with ⟨empty, hemptyLength, hemptyLayout,
    hemptyRows⟩
  have hempty : empty = [] := List.eq_nil_of_length_eq_zero hemptyLength
  subst empty
  rcases hleaf with ⟨hproofTag, hcertificateTag, hcheck⟩
  have hcheck' : CompactAdditiveClosedRuleCheck
      tokenTable width tokenCount
      gammaBoundary Gamma.length
      formulaStart formulaFinish formulaBoundary formula.length
      negatedStart negatedFinish negatedBoundary negated.length
      stateBoundary stateCount
      emptyStart emptyFinish emptyBoundary
      tableWidth valueBound resultBool := by
    simpa [hgammaLength, hformulaLength, hnegatedLength] using hcheck
  refine ⟨Gamma, formula, negated, [], hgammaLength, hformulaLength,
    hnegatedLength, rfl, hgammaLayout, hgammaRows, hformulaLayout,
    hformulaRows, hnegatedLayout, hnegatedRows, hemptyLayout, hemptyRows,
    hproofTag, hcertificateTag, ?_⟩
  intro hparsed
  exact (compactAdditiveClosedRuleCheck_iff
    hcheck'.1 hgammaRows hformulaLayout hformulaRows hnegatedLayout
    hnegatedRows hemptyLayout hemptyRows hparsed).mp hcheck'

theorem CompactNumericVerifierClosedLeafRuleSelfContainedGraph.exists_canonical
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    let formula := compactArithmeticFormulaTokens parsed
    let negated := compactArithmeticFormulaTokens (∼parsed)
    ∃ tokenTable width tokenCount
        gammaStart gammaFinish gammaBoundary gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negatedBoundarySize
        stateBoundary
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound,
      CompactNumericVerifierClosedLeafRuleSelfContainedGraph
        tokenTable width tokenCount 0 0
        gammaStart gammaFinish gammaBoundary Gamma.length gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formula.length formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negated.length negatedBoundarySize
        stateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound
        (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) := by
  dsimp only
  let formula := compactArithmeticFormulaTokens parsed
  let negated := compactArithmeticFormulaTokens (∼parsed)
  let empty : List Nat := []
  let trace := compactFormulaTransformStateTrace (3, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 0 formula)
  let chunks := compactClosedLeafCanonicalChunks Gamma parsed
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let gammaStart := (compactPackedChunkPrefix chunks 0).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let gammaBoundary := compactPackedNatListListBoundary chunks 0 Gamma
  let formulaSlot := compactPackedNatListSlot chunks 1 formula
  let negatedSlot := compactPackedNatListSlot chunks 2 negated
  let emptySlot := compactPackedNatListSlot chunks 3 empty
  let stateBoundary := compactPackedFormulaTransformStateBoundary chunks 4 trace
  have hformulaSlot := compactPackedNatListSlot_canonical chunks 1 formula
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, formula])
  have hnegatedSlot := compactPackedNatListSlot_canonical chunks 2 negated
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, negated])
  have hemptySlot := compactPackedNatListSlot_canonical chunks 3 empty
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, empty])
  have htraceRows := compactPackedFormulaTransformStateRows_canonical
    chunks 4 trace
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, trace, formula])
  dsimp only at hformulaSlot hnegatedSlot hemptySlot htraceRows
  let gammaFront := compactPackedChunkPrefix chunks 0
  let gammaBack := compactPackedChunkSuffix chunks 0
  have hgammaTokens : gammaFront ++ compactAdditiveEncode Gamma ++ gammaBack =
      chunks.flatten := by
    simp only [gammaFront, gammaBack]
    exact compactPackedChunkPrefix_append_getElem_append_suffix chunks 0
      (by simp [chunks, compactClosedLeafCanonicalChunks])
  have hgammaRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactAdditiveNatListDirectLayout compactAdditiveNatListDirectLayout_canonical
      gammaFront Gamma gammaBack
  dsimp only at hgammaRaw
  rw [hgammaTokens] at hgammaRaw
  have hgammaStructure : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length gammaStart Gamma.length gammaFinish
        gammaBoundary := by
    simpa [tokenTable, width, tokens, gammaStart, gammaFinish, gammaBoundary,
      compactPackedNatListListBoundary, gammaFront] using hgammaRaw.1
  have hgammaSize : Nat.size gammaBoundary ≤
      (Gamma.length + 1) * tokens.length := by
    simpa [tokens, gammaStart, gammaBoundary,
      compactPackedNatListListBoundary, gammaFront] using hgammaRaw.2.2
  have hgammaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        gammaBoundary Gamma := by
    simpa [tokenTable, width, tokens, gammaStart, gammaBoundary, gammaFront,
      compactPackedNatListListBoundary] using hgammaRaw.2.1
  have hgammaWitness : CompactAdditiveNatListListWitnessRows
      tokenTable width tokens.length gammaStart Gamma.length gammaFinish
      gammaBoundary (Nat.size gammaBoundary) :=
    ⟨hgammaStructure,
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hgammaRows,
      rfl, hgammaSize⟩
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length formulaSlot.start formulaSlot.finish formula :=
    hformulaSlot.layout
  have hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokens.length
        formulaSlot.boundary formula :=
    hformulaSlot.elements
  have hnegatedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length negatedSlot.start negatedSlot.finish negated :=
    hnegatedSlot.layout
  have hnegatedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokens.length
        negatedSlot.boundary negated :=
    hnegatedSlot.elements
  have hemptyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length emptySlot.start emptySlot.finish empty :=
    hemptySlot.layout
  have hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokens.length
        emptySlot.boundary empty :=
    hemptySlot.elements
  have htraceRows' : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokens.length stateBoundary trace := by
    simpa [tokenTable, width, tokens, stateBoundary] using htraceRows
  have hnegatedExact : compactFormulaNegationExact 0 formula = some negated := by
    simp [formula, negated]
  rcases CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
      htraceRows' hemptyLayout rfl hformulaRows hnegatedRows hemptyRows
      (by
        rw [compactFormulaTransformResult_negation]
        change negated = (compactFormulaNegationExact 0 formula).getD []
        rw [hnegatedExact]
        simp) with
    ⟨tableWidth, htransform⟩
  have hleaf : CompactNumericVerifierClosedLeafRuleRows
      tokenTable width tokens.length 0 0
      gammaBoundary Gamma.length
      formulaSlot.start formulaSlot.finish formulaSlot.boundary formula.length
      negatedSlot.start negatedSlot.finish negatedSlot.boundary negated.length
      stateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptySlot.start emptySlot.finish emptySlot.boundary
      tableWidth (2 ^ tableWidth)
      (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) :=
    CompactNumericVerifierClosedLeafRuleRows.of_components
      htransform hgammaRows hformulaLayout hformulaRows hnegatedLayout
      hnegatedRows hemptyLayout hemptyRows ⟨parsed, rfl⟩
  exact ⟨tokenTable, width, tokens.length,
    gammaStart, gammaFinish, gammaBoundary, Nat.size gammaBoundary,
    formulaSlot.start, formulaSlot.finish, formulaSlot.boundary,
      formulaSlot.boundarySize,
    negatedSlot.start, negatedSlot.finish, negatedSlot.boundary,
      negatedSlot.boundarySize,
    stateBoundary,
    emptySlot.start, emptySlot.finish, emptySlot.boundary,
      emptySlot.boundarySize,
    tableWidth, 2 ^ tableWidth,
    hgammaWitness, hformulaSlot.rows, hnegatedSlot.rows,
    hemptySlot.rows, hleaf⟩

#print axioms compactNumericVerifierClosedLeafRuleSelfContainedGraphDef_spec
#print axioms compactNumericVerifierClosedLeafRuleSelfContainedGraphDef_sigmaZero
#print axioms CompactNumericVerifierClosedLeafRuleSelfContainedGraph.sound
#print axioms CompactNumericVerifierClosedLeafRuleSelfContainedGraph.exists_canonical

end FoundationCompactNumericListedDirectVerifierClosedLeafRuleSelfContainedGraph
