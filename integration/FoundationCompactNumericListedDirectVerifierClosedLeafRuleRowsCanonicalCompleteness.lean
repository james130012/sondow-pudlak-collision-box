import integration.FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
import integration.FoundationCompactNumericListedDirectPackedRouteTable

/-!
# Canonical shared-table completeness for closed verifier leaves

The context, input formula, negated formula, empty witness, and public
formula-transform trace occupy one fixed-width token table.  Every boundary
needed by a later verifier-state graph is returned explicitly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCanonicalCompleteness

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness

def compactClosedLeafCanonicalChunks
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) : List (List Nat) :=
  let formula := compactArithmeticFormulaTokens parsed
  let negated := compactArithmeticFormulaTokens (∼parsed)
  let trace := compactFormulaTransformStateTrace (3, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 0 formula)
  [compactAdditiveEncode Gamma,
    compactAdditiveEncode formula,
    compactAdditiveEncode negated,
    compactAdditiveEncode ([] : List Nat),
    compactAdditiveEncode trace]

@[simp] theorem compactClosedLeafCanonicalChunks_gamma
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    (compactClosedLeafCanonicalChunks Gamma parsed).getI 0 =
      compactAdditiveEncode Gamma := by
  rfl

@[simp] theorem compactClosedLeafCanonicalChunks_formula
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    (compactClosedLeafCanonicalChunks Gamma parsed).getI 1 =
      compactAdditiveEncode (compactArithmeticFormulaTokens parsed) := by
  rfl

@[simp] theorem compactClosedLeafCanonicalChunks_negated
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    (compactClosedLeafCanonicalChunks Gamma parsed).getI 2 =
      compactAdditiveEncode (compactArithmeticFormulaTokens (∼parsed)) := by
  rfl

@[simp] theorem compactClosedLeafCanonicalChunks_empty
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    (compactClosedLeafCanonicalChunks Gamma parsed).getI 3 =
      compactAdditiveEncode ([] : List Nat) := by
  rfl

@[simp] theorem compactClosedLeafCanonicalChunks_trace
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    (compactClosedLeafCanonicalChunks Gamma parsed).getI 4 =
      compactAdditiveEncode
        (compactFormulaTransformStateTrace (3, [])
          (compactSyntaxRunFuelBound
            (compactArithmeticFormulaTokens parsed))
          (compactFormulaTransformInitialState 0
            (compactArithmeticFormulaTokens parsed))) := by
  rfl

def compactPackedNatListListBoundary
    (chunks : List (List Nat)) (index : Nat)
    (values : List (List Nat)) : Nat :=
  let tokens := chunks.flatten
  let start := (compactPackedChunkPrefix chunks index).length
  compactAdditiveStructuredListElementBoundaryTable
    tokens.length (start + 1) values

theorem compactPackedNatListListLayouts_canonical
    (chunks : List (List Nat)) (index : Nat)
    (values : List (List Nat))
    (hindex : index < chunks.length)
    (hchunk : chunks[index] = compactAdditiveEncode values) :
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let start := (compactPackedChunkPrefix chunks index).length
    let finish := start + (compactAdditiveEncode values).length
    let boundary := compactPackedNatListListBoundary chunks index values
    CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length start finish values /\
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout
          tokenTable width tokens.length boundary values := by
  let front := compactPackedChunkPrefix chunks index
  let back := compactPackedChunkSuffix chunks index
  have htokens : front ++ compactAdditiveEncode values ++ back =
      chunks.flatten := by
    rw [← hchunk]
    exact compactPackedChunkPrefix_append_getElem_append_suffix
      chunks index hindex
  have hraw := compactAdditiveStructuredListElementLayouts_canonical
    CompactAdditiveNatListDirectLayout
    compactAdditiveNatListDirectLayout_canonical front values back
  dsimp only at hraw
  rw [htokens] at hraw
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let start := (compactPackedChunkPrefix chunks index).length
  let finish := start + (compactAdditiveEncode values).length
  let boundary := compactPackedNatListListBoundary chunks index values
  have hstructure : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length start values.length finish boundary := by
    simpa [tokenTable, width, tokens, start, finish, boundary,
      compactPackedNatListListBoundary, front] using hraw.1
  have hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout
        tokenTable width tokens.length boundary values := by
    simpa [tokenTable, width, tokens, start, boundary,
      compactPackedNatListListBoundary, front] using hraw.2.1
  have hsize : Nat.size boundary ≤ (values.length + 1) * tokens.length := by
    simpa [tokens, start, boundary, compactPackedNatListListBoundary,
      front] using hraw.2.2
  exact ⟨⟨boundary, hstructure, hrows, hsize⟩, hrows⟩

theorem CompactNumericVerifierClosedLeafRuleRows.exists_canonical
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    let formula := compactArithmeticFormulaTokens parsed
    let negated := compactArithmeticFormulaTokens (∼parsed)
    let empty : List Nat := []
    let trace := compactFormulaTransformStateTrace (3, [])
      (compactSyntaxRunFuelBound formula)
      (compactFormulaTransformInitialState 0 formula)
    let chunks := compactClosedLeafCanonicalChunks Gamma parsed
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let canonicalTokenTable := compactFixedWidthTableCode width tokens
    ∃ tokenTable width' tokenCount
        gammaStart gammaFinish gammaBoundary
        formulaStart formulaFinish formulaBoundary
        negatedStart negatedFinish negatedBoundary
        emptyStart emptyFinish emptyBoundary stateBoundary
        tableWidth valueBound,
      tokenTable = canonicalTokenTable /\
      width' = width /\
      tokenCount = tokens.length /\
      valueBound = 2 ^ tableWidth /\
      CompactAdditiveNatListListDirectLayout
        tokenTable width' tokenCount gammaStart gammaFinish Gamma /\
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout
          tokenTable width' tokenCount gammaBoundary Gamma /\
      CompactAdditiveNatListDirectLayout
        tokenTable width' tokenCount formulaStart formulaFinish formula /\
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout
          tokenTable width' tokenCount formulaBoundary formula /\
      CompactAdditiveNatListDirectLayout
        tokenTable width' tokenCount negatedStart negatedFinish negated /\
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout
          tokenTable width' tokenCount negatedBoundary negated /\
      CompactAdditiveNatListDirectLayout
        tokenTable width' tokenCount emptyStart emptyFinish empty /\
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout
          tokenTable width' tokenCount emptyBoundary empty /\
      CompactFormulaTransformStateListRowLayouts
        tokenTable width' tokenCount stateBoundary trace /\
      CompactFormulaTransformTotalExactBoundedGraph
        tokenTable width' tokenCount stateBoundary
          (compactSyntaxRunFuelBound formula + 1) 3
        emptyStart emptyFinish 0
        formulaBoundary formula.length negatedBoundary negated.length
        emptyBoundary 0 tableWidth valueBound /\
      CompactNumericVerifierClosedLeafRuleRows
        tokenTable width' tokenCount 0 0
        gammaBoundary Gamma.length
        formulaStart formulaFinish formulaBoundary formula.length
        negatedStart negatedFinish negatedBoundary negated.length
        stateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary
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
  have hgamma := compactPackedNatListListLayouts_canonical chunks 0 Gamma
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks])
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
  dsimp only at hgamma hformulaSlot hnegatedSlot hemptySlot htraceRows
  have hGammaLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length gammaStart gammaFinish Gamma := by
    simpa [tokenTable, width, tokens, gammaStart, gammaFinish,
      gammaBoundary] using hgamma.1
  have hGammaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout
        tokenTable width tokens.length gammaBoundary Gamma := by
    simpa [tokenTable, width, tokens, gammaStart, gammaBoundary] using hgamma.2
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length formulaSlot.start formulaSlot.finish formula :=
    hformulaSlot.layout
  have hformulaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokens.length formulaSlot.boundary formula :=
    hformulaSlot.elements
  have hnegatedLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length negatedSlot.start negatedSlot.finish negated :=
    hnegatedSlot.layout
  have hnegatedRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokens.length negatedSlot.boundary negated :=
    hnegatedSlot.elements
  have hemptyLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length emptySlot.start emptySlot.finish empty :=
    hemptySlot.layout
  have hemptyRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout
        tokenTable width tokens.length emptySlot.boundary empty :=
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
      htransform hGammaRows hformulaLayout hformulaRows hnegatedLayout
      hnegatedRows hemptyLayout hemptyRows ⟨parsed, rfl⟩
  exact ⟨tokenTable, width, tokens.length,
    gammaStart, gammaFinish, gammaBoundary,
    formulaSlot.start, formulaSlot.finish, formulaSlot.boundary,
    negatedSlot.start, negatedSlot.finish, negatedSlot.boundary,
    emptySlot.start, emptySlot.finish, emptySlot.boundary, stateBoundary,
    tableWidth, 2 ^ tableWidth,
    rfl, rfl, rfl, rfl,
    hGammaLayout, hGammaRows, hformulaLayout, hformulaRows,
    hnegatedLayout, hnegatedRows, hemptyLayout, hemptyRows,
    htraceRows', htransform, hleaf⟩

#print axioms compactPackedNatListListLayouts_canonical
#print axioms CompactNumericVerifierClosedLeafRuleRows.exists_canonical

end FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCanonicalCompleteness
