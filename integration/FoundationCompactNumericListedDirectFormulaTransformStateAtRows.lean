import integration.FoundationCompactNumericListedDirectFormulaTransformStateFormula

/-!
# Bounded lookup of one formula-transform trace row

The trace boundary table fixes the selected state's physical interval.  The
seventeen-variable state core then exposes its parser and emitted-output
fields.  Canonical typed traces construct every witness directly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStateAtRows

open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateFormula

def CompactFormulaTransformStateAtRows
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Prop :=
  index < stateCount ∧
    CompactFixedWidthEntry
      stateBoundary tokenCount index coordinates.start ∧
    CompactFixedWidthEntry
      stateBoundary tokenCount (index + 1) coordinates.finish ∧
    CompactFormulaTransformStateCoreGraph
      tokenTable width tokenCount coordinates sizeWitness

def compactFormulaTransformStateAtRowsDef :
    𝚺₀.Semisentence 20 := .mkSigma
  “tokenTable width tokenCount stateBoundary stateCount index
      start finish parserFinish
      parserTokensFinish parserTasksFinish
      parserTokensBoundary parserTokensCount
      parserTasksBoundary parserTasksCount
      outputBoundary outputCount
      parserTokensBoundarySize parserTasksBoundarySize outputBoundarySize.
    index < stateCount ∧
    !(compactFixedWidthEntryDef)
      stateBoundary tokenCount index start ∧
    !(compactFixedWidthEntryDef)
      stateBoundary tokenCount (index + 1) finish ∧
    !(compactFormulaTransformStateCoreGraphDef)
      tokenTable width tokenCount
      start finish parserFinish
      parserTokensFinish parserTasksFinish
      parserTokensBoundary parserTokensCount
      parserTasksBoundary parserTasksCount
      outputBoundary outputCount
      parserTokensBoundarySize parserTasksBoundarySize outputBoundarySize”

def compactFormulaTransformStateAtRowsEnvironment
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    Fin 20 → Nat :=
  ![tokenTable, width, tokenCount, stateBoundary, stateCount, index,
    coordinates.start, coordinates.finish, coordinates.parserFinish,
    coordinates.parserTokensFinish, coordinates.parserTasksFinish,
    coordinates.parserTokensBoundary, coordinates.parserTokensCount,
    coordinates.parserTasksBoundary, coordinates.parserTasksCount,
    coordinates.outputBoundary, coordinates.outputCount,
    sizeWitness.parserTokensBoundarySize,
    sizeWitness.parserTasksBoundarySize,
    sizeWitness.outputBoundarySize]

@[simp] theorem compactFormulaTransformStateAtRowsDef_spec
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    compactFormulaTransformStateAtRowsDef.val.Evalb
        (compactFormulaTransformStateAtRowsEnvironment
          tokenTable width tokenCount stateBoundary stateCount index
            coordinates sizeWitness) ↔
      CompactFormulaTransformStateAtRows
        tokenTable width tokenCount stateBoundary stateCount index
          coordinates sizeWitness := by
  let env := compactFormulaTransformStateAtRowsEnvironment
    tokenTable width tokenCount stateBoundary stateCount index
      coordinates sizeWitness
  change compactFormulaTransformStateAtRowsDef.val.Evalb env ↔ _
  have hleftEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 20), #2, #5, #6]) =
        ![stateBoundary, tokenCount, index, coordinates.start] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrightEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#3 : Semiterm ℒₒᵣ Empty 20), #2,
          (‘(#5 + 1)’ : Semiterm ℒₒᵣ Empty 20), #7]) =
        ![stateBoundary, tokenCount, index + 1, coordinates.finish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcoreEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 20), #1, #2,
          #6, #7, #8, #9, #10, #11, #12, #13, #14, #15, #16,
          #17, #18, #19]) =
        compactFormulaTransformStateCoreFormulaEnvironment
          tokenTable width tokenCount coordinates sizeWitness := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hindexValue : env 5 = index := rfl
  have hstateCountValue : env 4 = stateCount := rfl
  simp [compactFormulaTransformStateAtRowsDef,
    CompactFormulaTransformStateAtRows,
    hleftEnv, hrightEnv, hcoreEnv,
    hindexValue, hstateCountValue]

theorem compactFormulaTransformStateAtRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactFormulaTransformStateAtRowsDef.val := by
  simp [compactFormulaTransformStateAtRowsDef]

theorem exists_compactFormulaTransformStateAtRows_with_fixed_layout
    {tokenTable width tokenCount stateBoundary index : Nat}
    {states : List CompactFormulaTransformState}
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states)
    (hindex : index < states.length) :
    ∃ coordinates sizeWitness,
      CompactFormulaTransformStateAtRows
        tokenTable width tokenCount stateBoundary states.length index
          coordinates sizeWitness ∧
      CompactFormulaTransformStateFixedLayout
        tokenTable width tokenCount coordinates (states.getI index) := by
  rcases hrows index hindex with
    ⟨left, hleft, right, hright,
      hleftEntry, hrightEntry, hlayout⟩
  rcases (compactFormulaTransformStateDirectLayout_iff_fixedCoordinates
      tokenTable width tokenCount left right (states.getI index)).mp hlayout with
    ⟨coordinates, hstart, hfinish, hfixed⟩
  rcases hfixed.toCoreGraph with ⟨sizeWitness, hcore⟩
  refine ⟨coordinates, sizeWitness,
    ⟨hindex, ?_, ?_, hcore⟩, hfixed⟩
  · simpa only [hstart] using hleftEntry
  · simpa only [hfinish] using hrightEntry

theorem exists_compactFormulaTransformStateAtRows_iff
    {tokenTable width tokenCount stateBoundary stateCount index : Nat}
    {states : List CompactFormulaTransformState}
    (hcount : states.length = stateCount)
    (hrows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary states) :
    (∃ coordinates sizeWitness,
        CompactFormulaTransformStateAtRows
          tokenTable width tokenCount stateBoundary stateCount index
            coordinates sizeWitness) ↔
      index < states.length := by
  constructor
  · rintro ⟨coordinates, sizeWitness, hindex, _hleft, _hright, _hcore⟩
    simpa only [hcount] using hindex
  · intro hindex
    rcases exists_compactFormulaTransformStateAtRows_with_fixed_layout
        hrows hindex with
      ⟨coordinates, sizeWitness, hat, _hfixed⟩
    refine ⟨coordinates, sizeWitness, ?_⟩
    simpa only [hcount] using hat

#print axioms compactFormulaTransformStateAtRowsDef_spec
#print axioms compactFormulaTransformStateAtRowsDef_sigmaZero
#print axioms exists_compactFormulaTransformStateAtRows_with_fixed_layout
#print axioms exists_compactFormulaTransformStateAtRows_iff

end FoundationCompactNumericListedDirectFormulaTransformStateAtRows
