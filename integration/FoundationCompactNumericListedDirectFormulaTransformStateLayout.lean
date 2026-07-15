import integration.FoundationCompactNumericFormulaTransformTrace
import integration.FoundationCompactNumericListedDirectParserStateLayout
import integration.FoundationCompactNumericListedDirectVerifierValueLayouts

/-!
# Direct layouts for formula-transform trace states

Each row is the genuine product of a unified syntax-parser state and the
output tokens emitted so far.  The canonical theorem places both parts in one
fixed-width token table and exposes exact row boundaries for later bounded
step formulas.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStateLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectParserStateLayout
open FoundationCompactNumericListedDirectVerifierValueLayouts

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def CompactFormulaTransformStateDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (state : CompactFormulaTransformState) : Prop :=
  ∃ parserFinish,
    CompactAdditiveProductSplit tokenCount start parserFinish finish ∧
    CompactUnifiedParserStateDirectLayout
      tokenTable width tokenCount start parserFinish state.1 ∧
    CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount parserFinish finish state.2

theorem compactFormulaTransformStateDirectLayout_canonical
    (frontTokens : List Nat) (state : CompactFormulaTransformState)
    (backTokens : List Nat) :
    let stateTokens := compactAdditiveEncode state
    let tokens := frontTokens ++ stateTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + stateTokens.length
    CompactFormulaTransformStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish state := by
  let parserState := state.1
  let output := state.2
  let stateTokens := compactAdditiveEncode state
  let tokens := frontTokens ++ stateTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let parserFinish := start + (compactAdditiveEncode parserState).length
  let finish := start + stateTokens.length
  let afterParser := frontTokens ++ compactAdditiveEncode parserState
  have hstateTokens : stateTokens =
      compactAdditiveEncode parserState ++ compactAdditiveEncode output := by
    change compactAdditiveEncode state = _
    rw [show state = (parserState, output) by rfl]
    exact compactAdditiveEncode_prod (parserState, output)
  have hcommonTokens : tokens =
      frontTokens ++ compactAdditiveEncode parserState ++
        compactAdditiveEncode output ++ backTokens := by
    rw [show tokens = frontTokens ++ stateTokens ++ backTokens by rfl]
    rw [hstateTokens]
    simp [List.append_assoc]
  have hparserFull :
      frontTokens ++ compactAdditiveEncode parserState ++
          (compactAdditiveEncode output ++ backTokens) = tokens := by
    simpa [List.append_assoc] using hcommonTokens.symm
  have houtputFull :
      afterParser ++ compactAdditiveEncode output ++ backTokens = tokens := by
    simpa [afterParser, List.append_assoc] using hcommonTokens.symm
  have hproductRaw := compactAdditiveProductSplit_canonical
    frontTokens parserState output backTokens
  have hparserRaw := compactUnifiedParserStateDirectLayout_canonical
    frontTokens parserState (compactAdditiveEncode output ++ backTokens)
  have houtputRaw := compactAdditiveNatListDirectLayout_canonical
    afterParser output backTokens
  dsimp only at hproductRaw hparserRaw houtputRaw
  rw [hparserFull] at hparserRaw
  rw [houtputFull] at houtputRaw
  have hafterParser : afterParser.length = parserFinish := by
    simp [afterParser, parserFinish, start]
  have hfinish : finish =
      parserFinish + (compactAdditiveEncode output).length := by
    dsimp only [finish, parserFinish, start]
    rw [hstateTokens]
    simp only [List.length_append]
    omega
  have hproduct : CompactAdditiveProductSplit
      tokens.length start parserFinish finish := by
    simpa only [start, parserFinish, hfinish] using hproductRaw
  have hparser : CompactUnifiedParserStateDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start parserFinish parserState := by
    simpa only [width, parserFinish] using hparserRaw
  have houtput : CompactAdditiveNatListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length parserFinish finish output := by
    simpa only [width, hafterParser, hfinish] using houtputRaw
  exact ⟨parserFinish, hproduct, hparser, houtput⟩

def CompactFormulaTransformStateListRowLayouts
    (tokenTable width tokenCount boundaryTable : Nat)
    (states : List CompactFormulaTransformState) : Prop :=
  CompactAdditiveStructuredListElementRowLayouts
    CompactFormulaTransformStateDirectLayout
      tokenTable width tokenCount boundaryTable states

def compactFormulaTransformStateBoundaryTable
    (tokenCount bodyStart : Nat)
    (states : List CompactFormulaTransformState) : Nat :=
  compactAdditiveStructuredListElementBoundaryTable
    tokenCount bodyStart states

theorem compactFormulaTransformStateListDirectLayout_canonical
    (frontTokens : List Nat) (states : List CompactFormulaTransformState)
    (backTokens : List Nat) :
    let listTokens := compactAdditiveEncode states
    let tokens := frontTokens ++ listTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let bodyStart := start + 1
    let finish := start + listTokens.length
    let boundaryTable :=
      compactFormulaTransformStateBoundaryTable
        tokens.length bodyStart states
    CompactAdditiveStructuredListLayout
        (compactFixedWidthTableCode width tokens)
        width tokens.length start states.length finish boundaryTable ∧
      CompactFormulaTransformStateListRowLayouts
        (compactFixedWidthTableCode width tokens)
        width tokens.length boundaryTable states ∧
      Nat.size boundaryTable ≤ (states.length + 1) * tokens.length := by
  simpa [CompactFormulaTransformStateListRowLayouts,
    compactFormulaTransformStateBoundaryTable] using
    compactAdditiveStructuredListElementLayouts_canonical
      CompactFormulaTransformStateDirectLayout
      compactFormulaTransformStateDirectLayout_canonical
      frontTokens states backTokens

#print axioms compactFormulaTransformStateDirectLayout_canonical
#print axioms compactFormulaTransformStateListDirectLayout_canonical

end FoundationCompactNumericListedDirectFormulaTransformStateLayout
