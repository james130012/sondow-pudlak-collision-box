import integration.FoundationCompactNumericListedDirectFormulaTransformStateLayout

/-!
# Direct layouts for finite lists of formula-transform traces

The outer structured list packs any finite family of canonical transform
traces into one token table.  Each outer row exposes the complete inner trace
layout and its state-row boundary table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformTraceListLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectStructuredListCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

def CompactFormulaTransformTraceDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (trace : List CompactFormulaTransformState) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start trace.length finish boundaryTable ∧
    CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount boundaryTable trace ∧
    Nat.size boundaryTable ≤ (trace.length + 1) * tokenCount

theorem compactFormulaTransformTraceDirectLayout_canonical
    (frontTokens : List Nat) (trace : List CompactFormulaTransformState)
    (backTokens : List Nat) :
    let traceTokens := compactAdditiveEncode trace
    let tokens := frontTokens ++ traceTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + traceTokens.length
    CompactFormulaTransformTraceDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish trace := by
  rcases compactFormulaTransformStateListDirectLayout_canonical
      frontTokens trace backTokens with ⟨hlayout, hrows, hsize⟩
  exact ⟨_, hlayout, hrows, hsize⟩

def CompactFormulaTransformTraceListRowLayouts
    (tokenTable width tokenCount boundaryTable : Nat)
    (traces : List (List CompactFormulaTransformState)) : Prop :=
  CompactAdditiveStructuredListElementRowLayouts
    CompactFormulaTransformTraceDirectLayout
      tokenTable width tokenCount boundaryTable traces

def CompactFormulaTransformTraceListDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (traces : List (List CompactFormulaTransformState)) : Prop :=
  ∃ boundaryTable,
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start traces.length finish boundaryTable ∧
    CompactFormulaTransformTraceListRowLayouts
      tokenTable width tokenCount boundaryTable traces ∧
    Nat.size boundaryTable ≤ (traces.length + 1) * tokenCount

theorem compactFormulaTransformTraceListDirectLayout_canonical
    (frontTokens : List Nat)
    (traces : List (List CompactFormulaTransformState))
    (backTokens : List Nat) :
    let traceListTokens := compactAdditiveEncode traces
    let tokens := frontTokens ++ traceListTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + traceListTokens.length
    CompactFormulaTransformTraceListDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish traces := by
  rcases compactAdditiveStructuredListElementLayouts_canonical
      CompactFormulaTransformTraceDirectLayout
      compactFormulaTransformTraceDirectLayout_canonical
      frontTokens traces backTokens with ⟨hlayout, hrows, hsize⟩
  exact ⟨_, hlayout, hrows, hsize⟩

theorem CompactFormulaTransformTraceListRowLayouts.trace_rows
    {tokenTable width tokenCount boundaryTable : Nat}
    {traces : List (List CompactFormulaTransformState)}
    (hrows : CompactFormulaTransformTraceListRowLayouts
      tokenTable width tokenCount boundaryTable traces)
    (index : Nat) (hindex : index < traces.length) :
    ∃ stateBoundary,
      CompactFormulaTransformStateListRowLayouts
        tokenTable width tokenCount stateBoundary (traces.getI index) := by
  rcases hrows index hindex with
    ⟨_start, _hstart, _finish, _hfinish,
      _hstartEntry, _hfinishEntry, hlayout⟩
  rcases hlayout with ⟨stateBoundary, _hstructure, hstateRows, _hsize⟩
  exact ⟨stateBoundary, hstateRows⟩

theorem CompactFormulaTransformTraceListRowLayouts.trace_rows_with_size
    {tokenTable width tokenCount boundaryTable : Nat}
    {traces : List (List CompactFormulaTransformState)}
    (hrows : CompactFormulaTransformTraceListRowLayouts
      tokenTable width tokenCount boundaryTable traces)
    (index : Nat) (hindex : index < traces.length) :
    ∃ stateBoundary,
      CompactFormulaTransformStateListRowLayouts
          tokenTable width tokenCount stateBoundary (traces.getI index) ∧
        Nat.size stateBoundary ≤
          ((traces.getI index).length + 1) * tokenCount := by
  rcases hrows index hindex with
    ⟨_start, _hstart, _finish, _hfinish,
      _hstartEntry, _hfinishEntry, hlayout⟩
  rcases hlayout with ⟨stateBoundary, _hstructure, hstateRows, hsize⟩
  exact ⟨stateBoundary, hstateRows, hsize⟩

#print axioms compactFormulaTransformTraceDirectLayout_canonical
#print axioms compactFormulaTransformTraceListDirectLayout_canonical
#print axioms CompactFormulaTransformTraceListRowLayouts.trace_rows
#print axioms CompactFormulaTransformTraceListRowLayouts.trace_rows_with_size

end FoundationCompactNumericListedDirectFormulaTransformTraceListLayout
