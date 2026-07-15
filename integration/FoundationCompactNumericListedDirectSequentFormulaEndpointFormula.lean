import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation

/-!
# Bounded arithmetic formula for exact sequent-parser endpoints

The formula exposes the input, first suffix, final suffix, parsed value table,
and exact repeated-parser trace in one 27-column row.  A second formula bounds
all eighteen local witnesses by one public value bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation

def compactSequentFormulaEndpointGraphDef : 𝚺₀.Semisentence 27 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish
      inputBoundary inputCount inputBoundarySize
      firstStart firstFinish firstBoundary firstCount firstBoundarySize
      suffixBoundary suffixCount valueBoundary valueCount valueBoundarySize
      finalBoundary finalCount finalBoundarySize
      traceTableWidth traceValueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
      inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount firstStart firstCount firstFinish
      firstBoundary firstBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount finalStart finalCount finalFinish
      finalBoundary finalBoundarySize ∧
    !(compactSequentFormulaTraceBoundedGraphDef)
      tokenTable width tokenCount suffixBoundary suffixCount
      valueBoundary valueCount traceTableWidth traceValueBound ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount 0 firstStart ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount 1 firstFinish ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount valueCount finalStart ∧
    !(compactFixedWidthEntryDef)
      suffixBoundary tokenCount (valueCount + 1) finalFinish ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount firstBoundary firstCount
      inputBoundary inputCount valueCount ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount valueStart valueCount valueFinish
      valueBoundary ∧
    !(compactNatSizeDef) valueBoundarySize valueBoundary ∧
    valueBoundarySize ≤ (valueCount + 1) * tokenCount”

def compactSequentFormulaEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) : Fin 27 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    valueStart, valueFinish, finalStart, finalFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.firstStart, coordinates.firstFinish,
    coordinates.firstBoundary, coordinates.firstCount,
    coordinates.firstBoundarySize,
    coordinates.suffixBoundary, coordinates.suffixCount,
    coordinates.valueBoundary, coordinates.valueCount,
    coordinates.valueBoundarySize,
    coordinates.finalBoundary, coordinates.finalCount,
    coordinates.finalBoundarySize,
    coordinates.traceTableWidth, coordinates.traceValueBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish : Nat)
    (coordinates : CompactSequentFormulaEndpointCoordinates) :
    compactSequentFormulaEndpointGraphDef.val.Evalb
        (compactSequentFormulaEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish
            valueStart valueFinish finalStart finalFinish coordinates) ↔
      CompactSequentFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish coordinates := by
  let env := compactSequentFormulaEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish coordinates
  change compactSequentFormulaEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #3, #10, #4,
          #9, #11]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfirstEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #12, #15, #13,
          #14, #16]) =
        ![tokenTable, width, tokenCount, coordinates.firstStart,
          coordinates.firstCount, coordinates.firstFinish,
          coordinates.firstBoundary, coordinates.firstBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hfinalEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #7, #23, #8,
          #22, #24]) =
        ![tokenTable, width, tokenCount, finalStart,
          coordinates.finalCount, finalFinish,
          coordinates.finalBoundary, coordinates.finalBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htraceEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #17, #18,
          #19, #20, #25, #26]) =
        ![tokenTable, width, tokenCount, coordinates.suffixBoundary,
          coordinates.suffixCount, coordinates.valueBoundary,
          coordinates.valueCount, coordinates.traceTableWidth,
          coordinates.traceValueBound] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #14, #15,
          #9, #10, #20]) =
        ![tokenTable, width, tokenCount, coordinates.firstBoundary,
          coordinates.firstCount, coordinates.inputBoundary,
          coordinates.inputCount, coordinates.valueCount] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvalueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 27), #1, #2, #5, #20, #6,
          #19]) =
        ![tokenTable, width, tokenCount, valueStart,
          coordinates.valueCount, valueFinish,
          coordinates.valueBoundary] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hfinalStartValue : env 7 = finalStart := rfl
  have hfinalFinishValue : env 8 = finalFinish := rfl
  have hfirstStartValue : env 12 = coordinates.firstStart := rfl
  have hfirstFinishValue : env 13 = coordinates.firstFinish := rfl
  have hsuffixBoundaryValue :
      env 17 = coordinates.suffixBoundary := rfl
  have hvalueBoundaryValue : env 19 = coordinates.valueBoundary := rfl
  have hvalueCountValue : env 20 = coordinates.valueCount := rfl
  have hvalueBoundarySizeValue :
      env 21 = coordinates.valueBoundarySize := rfl
  simp [compactSequentFormulaEndpointGraphDef,
    CompactSequentFormulaEndpointGraph,
    hinputEnv, hfirstEnv, hfinalEnv, htraceEnv, hconsEnv, hvalueEnv,
    htokenCountValue, hfinalStartValue, hfinalFinishValue,
    hfirstStartValue, hfirstFinishValue, hsuffixBoundaryValue,
    hvalueBoundaryValue, hvalueCountValue, hvalueBoundarySizeValue]

theorem compactSequentFormulaEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaEndpointGraphDef.val := by
  simp [compactSequentFormulaEndpointGraphDef]

def compactSequentFormulaEndpointCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      firstStart firstFinish firstBoundary firstCount firstBoundarySize
      suffixBoundary suffixCount valueBoundary valueCount valueBoundarySize
      finalBoundary finalCount finalBoundarySize
      traceTableWidth traceValueBound : Nat) :
    CompactSequentFormulaEndpointCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    firstStart := firstStart
    firstFinish := firstFinish
    firstBoundary := firstBoundary
    firstCount := firstCount
    firstBoundarySize := firstBoundarySize
    suffixBoundary := suffixBoundary
    suffixCount := suffixCount
    valueBoundary := valueBoundary
    valueCount := valueCount
    valueBoundarySize := valueBoundarySize
    finalBoundary := finalBoundary
    finalCount := finalCount
    finalBoundarySize := finalBoundarySize
    traceTableWidth := traceTableWidth
    traceValueBound := traceValueBound }

def CompactSequentFormulaEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish endpointBound : Nat) : Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ firstStart, firstStart ≤ endpointBound ∧
  ∃ firstFinish, firstFinish ≤ endpointBound ∧
  ∃ firstBoundary, firstBoundary ≤ endpointBound ∧
  ∃ firstCount, firstCount ≤ endpointBound ∧
  ∃ firstBoundarySize, firstBoundarySize ≤ endpointBound ∧
  ∃ suffixBoundary, suffixBoundary ≤ endpointBound ∧
  ∃ suffixCount, suffixCount ≤ endpointBound ∧
  ∃ valueBoundary, valueBoundary ≤ endpointBound ∧
  ∃ valueCount, valueCount ≤ endpointBound ∧
  ∃ valueBoundarySize, valueBoundarySize ≤ endpointBound ∧
  ∃ finalBoundary, finalBoundary ≤ endpointBound ∧
  ∃ finalCount, finalCount ≤ endpointBound ∧
  ∃ finalBoundarySize, finalBoundarySize ≤ endpointBound ∧
  ∃ traceTableWidth, traceTableWidth ≤ endpointBound ∧
  ∃ traceValueBound, traceValueBound ≤ endpointBound ∧
    CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish
        (compactSequentFormulaEndpointCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          firstStart firstFinish firstBoundary firstCount firstBoundarySize
          suffixBoundary suffixCount valueBoundary valueCount valueBoundarySize
          finalBoundary finalCount finalBoundarySize
          traceTableWidth traceValueBound)

def compactSequentFormulaEndpointBoundedGraphDef : 𝚺₀.Semisentence 10 :=
  .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ firstStart <⁺ endpointBound,
    ∃ firstFinish <⁺ endpointBound,
    ∃ firstBoundary <⁺ endpointBound,
    ∃ firstCount <⁺ endpointBound,
    ∃ firstBoundarySize <⁺ endpointBound,
    ∃ suffixBoundary <⁺ endpointBound,
    ∃ suffixCount <⁺ endpointBound,
    ∃ valueBoundary <⁺ endpointBound,
    ∃ valueCount <⁺ endpointBound,
    ∃ valueBoundarySize <⁺ endpointBound,
    ∃ finalBoundary <⁺ endpointBound,
    ∃ finalCount <⁺ endpointBound,
    ∃ finalBoundarySize <⁺ endpointBound,
    ∃ traceTableWidth <⁺ endpointBound,
    ∃ traceValueBound <⁺ endpointBound,
      !(compactSequentFormulaEndpointGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish
        inputBoundary inputCount inputBoundarySize
        firstStart firstFinish firstBoundary firstCount firstBoundarySize
        suffixBoundary suffixCount valueBoundary valueCount valueBoundarySize
        finalBoundary finalCount finalBoundarySize
        traceTableWidth traceValueBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish endpointBound : Nat) :
    compactSequentFormulaEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          valueStart, valueFinish, finalStart, finalFinish, endpointBound] ↔
      CompactSequentFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish endpointBound := by
  have hrow
      (traceValueBound traceTableWidth finalBoundarySize finalCount
        finalBoundary valueBoundarySize valueCount valueBoundary
        suffixCount suffixBoundary firstBoundarySize firstCount
        firstBoundary firstFinish firstStart inputBoundarySize
        inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![traceValueBound, traceTableWidth, finalBoundarySize,
                finalCount, finalBoundary, valueBoundarySize, valueCount,
                valueBoundary, suffixCount, suffixBoundary,
                firstBoundarySize, firstCount, firstBoundary, firstFinish,
                firstStart, inputBoundarySize, inputCount, inputBoundary,
                tokenTable, width, tokenCount, inputStart, inputFinish,
                valueStart, valueFinish, finalStart, finalFinish,
                endpointBound]
              Empty.elim ∘
            ![(#18 : Semiterm ℒₒᵣ Empty 28), #19, #20, #21, #22,
              #23, #24, #25, #26, #17, #16, #15, #14, #13, #12,
              #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactSequentFormulaEndpointGraphDef.val ↔
        CompactSequentFormulaEndpointGraph
          tokenTable width tokenCount inputStart inputFinish
            valueStart valueFinish finalStart finalFinish
            (compactSequentFormulaEndpointCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              firstStart firstFinish firstBoundary firstCount firstBoundarySize
              suffixBoundary suffixCount valueBoundary valueCount
              valueBoundarySize finalBoundary finalCount finalBoundarySize
              traceTableWidth traceValueBound) := by
    have henv :
        (Semiterm.val
            ![traceValueBound, traceTableWidth, finalBoundarySize,
              finalCount, finalBoundary, valueBoundarySize, valueCount,
              valueBoundary, suffixCount, suffixBoundary,
              firstBoundarySize, firstCount, firstBoundary, firstFinish,
              firstStart, inputBoundarySize, inputCount, inputBoundary,
              tokenTable, width, tokenCount, inputStart, inputFinish,
              valueStart, valueFinish, finalStart, finalFinish,
              endpointBound]
            Empty.elim ∘
          ![(#18 : Semiterm ℒₒᵣ Empty 28), #19, #20, #21, #22,
            #23, #24, #25, #26, #17, #16, #15, #14, #13, #12,
            #11, #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactSequentFormulaEndpointEnvironment
            tokenTable width tokenCount inputStart inputFinish
              valueStart valueFinish finalStart finalFinish
              (compactSequentFormulaEndpointCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                firstStart firstFinish firstBoundary firstCount
                firstBoundarySize suffixBoundary suffixCount valueBoundary
                valueCount valueBoundarySize finalBoundary finalCount
                finalBoundarySize traceTableWidth traceValueBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactSequentFormulaEndpointGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish _
  simp [compactSequentFormulaEndpointBoundedGraphDef,
    CompactSequentFormulaEndpointBoundedGraph, hrow]

theorem compactSequentFormulaEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaEndpointBoundedGraphDef.val := by
  simp [compactSequentFormulaEndpointBoundedGraphDef]

theorem CompactSequentFormulaEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish endpointBound : Nat}
    (hbounded : CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish endpointBound) :
    ∃ coordinates : CompactSequentFormulaEndpointCoordinates,
      CompactSequentFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish coordinates := by
  unfold CompactSequentFormulaEndpointBoundedGraph at hbounded
  rcases hbounded with
    ⟨inputBoundary, _hinputBoundary,
      inputCount, _hinputCount,
      inputBoundarySize, _hinputBoundarySize,
      firstStart, _hfirstStart,
      firstFinish, _hfirstFinish,
      firstBoundary, _hfirstBoundary,
      firstCount, _hfirstCount,
      firstBoundarySize, _hfirstBoundarySize,
      suffixBoundary, _hsuffixBoundary,
      suffixCount, _hsuffixCount,
      valueBoundary, _hvalueBoundary,
      valueCount, _hvalueCount,
      valueBoundarySize, _hvalueBoundarySize,
      finalBoundary, _hfinalBoundary,
      finalCount, _hfinalCount,
      finalBoundarySize, _hfinalBoundarySize,
      traceTableWidth, _htraceTableWidth,
      traceValueBound, _htraceValueBound, hgraph⟩
  exact ⟨compactSequentFormulaEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    firstStart firstFinish firstBoundary firstCount firstBoundarySize
    suffixBoundary suffixCount valueBoundary valueCount valueBoundarySize
    finalBoundary finalCount finalBoundarySize
    traceTableWidth traceValueBound, hgraph⟩

theorem CompactSequentFormulaEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish endpointBound : Nat}
    (hbounded : CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish endpointBound) :
    ∃ input : List Nat,
    ∃ values : List (List Nat),
    ∃ suffix : List Nat,
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount valueStart valueFinish values ∧
      FoundationCompactNumericListedDirectVerifierValueLayouts.CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount finalStart finalFinish suffix ∧
      FoundationCompactNumericSyntaxValueParser.compactSequentTokenValueParser
        input = some (values, suffix) := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

#print axioms compactSequentFormulaEndpointGraphDef_spec
#print axioms compactSequentFormulaEndpointGraphDef_sigmaZero
#print axioms compactSequentFormulaEndpointBoundedGraphDef_spec
#print axioms compactSequentFormulaEndpointBoundedGraphDef_sigmaZero
#print axioms CompactSequentFormulaEndpointBoundedGraph.exists_coordinates
#print axioms CompactSequentFormulaEndpointBoundedGraph.sound

end FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
