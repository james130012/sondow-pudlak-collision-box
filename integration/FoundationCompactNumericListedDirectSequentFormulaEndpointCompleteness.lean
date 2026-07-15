import integration.FoundationCompactNumericListedDirectSequentFormulaCanonicalData
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointFormula

/-!
# Completeness of the exact sequent-parser endpoint graph

Every successful public sequent parse constructs the full direct bounded
endpoint graph.  No suffix table, parser trace, or common token table is an
input to the theorem.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness

open FoundationCompactProofTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectSequentFormulaTraceFormula
open FoundationCompactNumericListedDirectSequentFormulaTraceCompleteness
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaCanonicalLayouts
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData

/-- Install a complete sequent formula-list trace already laid out in an
arbitrary shared token table. -/
theorem exists_compactSequentFormulaEndpointGraph_of_rows
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish suffixBoundary valueBoundary : Nat}
    {input suffix : List Nat}
    {suffixes values : List (List Nat)}
    {parserTraces : List FoundationCompactParserDirectTrace.CompactFormulaTokenParserDirectTrace}
    (hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount inputStart inputFinish input)
    (hsuffixRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        suffixBoundary suffixes)
    (hvalueStructure : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount valueStart values.length valueFinish
        valueBoundary)
    (hvalueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        valueBoundary values)
    (hvalueBoundarySize :
      Nat.size valueBoundary ≤ (values.length + 1) * tokenCount)
    (hparserRows : ∀ index < values.length,
      ∃ parserStateBoundary,
        FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
          tokenTable width tokenCount parserStateBoundary
            (parserTraces.getI index))
    (hsuffixCount : suffixes.length = values.length + 1)
    (hparserCount : parserTraces.length = values.length)
    (hsteps : ∀ index < values.length,
      FoundationCompactParserDirectTrace.CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          values.getI index ++ suffixes.getI (index + 1))
    (hinputEq : input = values.length :: suffixes.getI 0)
    (hfinalEq : suffixes.getI values.length = suffix) :
    ∃ finalStart finalFinish,
    ∃ coordinates : CompactSequentFormulaEndpointCoordinates,
      CompactSequentFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish coordinates := by
  rcases exists_compactSequentFormulaTraceBoundedGraph_of_directData
      hsuffixCount hparserCount hsuffixRows hvalueRows hparserRows hsteps with
    ⟨traceTableWidth, htrace⟩
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputBoundarySize⟩
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputBoundarySize⟩
  have hfirstIndex : 0 < suffixes.length := by
    rw [hsuffixCount]
    omega
  rcases hsuffixRows 0 hfirstIndex with
    ⟨firstStart, _hfirstStartBound,
      firstFinish, _hfirstFinishBound,
      hfirstStartEntry, hfirstFinishEntry, hfirstLayout⟩
  rcases hfirstLayout with
    ⟨firstBoundary, hfirstStructure, hfirstRows, hfirstBoundarySize⟩
  have hfirstWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount firstStart (suffixes.getI 0).length
        firstFinish firstBoundary (Nat.size firstBoundary) :=
    ⟨hfirstStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfirstRows,
      rfl, hfirstBoundarySize⟩
  have hfinalIndex : values.length < suffixes.length := by
    rw [hsuffixCount]
    omega
  rcases hsuffixRows values.length hfinalIndex with
    ⟨finalStart, _hfinalStartBound,
      finalFinish, _hfinalFinishBound,
      hfinalStartEntry, hfinalFinishEntry, hfinalLayout⟩
  rw [hfinalEq] at hfinalLayout
  rcases hfinalLayout with
    ⟨finalBoundary, hfinalStructure, hfinalRows, hfinalBoundarySize⟩
  have hfinalWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount finalStart suffix.length finalFinish
        finalBoundary (Nat.size finalBoundary) :=
    ⟨hfinalStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfinalRows,
      rfl, hfinalBoundarySize⟩
  have hcons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount firstBoundary (suffixes.getI 0).length
        inputBoundary input.length values.length :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hfirstRows hinputRows hinputEq
  let coordinates : CompactSequentFormulaEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      firstStart := firstStart
      firstFinish := firstFinish
      firstBoundary := firstBoundary
      firstCount := (suffixes.getI 0).length
      firstBoundarySize := Nat.size firstBoundary
      suffixBoundary := suffixBoundary
      suffixCount := suffixes.length
      valueBoundary := valueBoundary
      valueCount := values.length
      valueBoundarySize := Nat.size valueBoundary
      finalBoundary := finalBoundary
      finalCount := suffix.length
      finalBoundarySize := Nat.size finalBoundary
      traceTableWidth := traceTableWidth
      traceValueBound := 2 ^ traceTableWidth }
  refine ⟨finalStart, finalFinish, coordinates, ?_⟩
  unfold CompactSequentFormulaEndpointGraph
  dsimp only [coordinates]
  exact ⟨hinputWitness, hfirstWitness, hfinalWitness, htrace,
    hfirstStartEntry, hfirstFinishEntry,
    hfinalStartEntry, hfinalFinishEntry, hcons,
    hvalueStructure, rfl, hvalueBoundarySize⟩

/-- A successful public parser run constructs an exact endpoint graph in one
canonical token table. -/
theorem exists_compactSequentFormulaEndpointGraph_of_success
    {input : List Nat} {values : List (List Nat)} {suffix : List Nat}
    (hparser : compactSequentTokenValueParser input =
      some (values, suffix)) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ valueStart valueFinish finalStart finalFinish,
    ∃ coordinates : CompactSequentFormulaEndpointCoordinates,
      CompactSequentFormulaEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish coordinates := by
  rcases compactSequentTokenValueParser_sound hparser with
    ⟨Gamma, hinput, hvalues⟩
  subst input
  subst values
  rcases exists_compactSequentFormulaCanonicalDirectData Gamma suffix with
    ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
      hfirst, hfinal, hsteps⟩
  rcases exists_compactSequentFormulaCanonicalEndpointLayouts
      (compactSequentListTokens Gamma ++ suffix)
      suffixes (Gamma.map compactArithmeticFormulaTokens) parserTraces with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      suffixBoundary, valueStart, valueFinish, valueBoundary,
      hinputLayout, hsuffixRows, hvalueStructure, hvalueRows,
      hvalueBoundarySize, hparserRows⟩
  have hsuffixCount' : suffixes.length =
      (Gamma.map compactArithmeticFormulaTokens).length + 1 := by
    simpa using hsuffixCount
  have hparserCount' : parserTraces.length =
      (Gamma.map compactArithmeticFormulaTokens).length := by
    simpa using hparserCount
  have hparserRows' : ∀ index <
      (Gamma.map compactArithmeticFormulaTokens).length,
      ∃ parserStateBoundary,
        FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
          tokenTable width tokenCount parserStateBoundary
            (parserTraces.getI index) := by
    intro index hindex
    apply hparserRows index
    rw [hparserCount']
    exact hindex
  have hsteps' : ∀ index <
      (Gamma.map compactArithmeticFormulaTokens).length,
      FoundationCompactParserDirectTrace.CompactFormulaTokenParserDirectTraceValid
          0 (suffixes.getI index) (suffixes.getI (index + 1))
            (parserTraces.getI index) ∧
        suffixes.getI index =
          (Gamma.map compactArithmeticFormulaTokens).getI index ++
            suffixes.getI (index + 1) := by
    intro index hindex
    apply hsteps index
    simpa using hindex
  rcases exists_compactSequentFormulaTraceBoundedGraph_of_directData
      hsuffixCount' hparserCount' hsuffixRows hvalueRows hparserRows' hsteps' with
    ⟨traceTableWidth, htrace⟩
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputRows, hinputBoundarySize⟩
  have hinputWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart
        (compactSequentListTokens Gamma ++ suffix).length inputFinish
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputRows,
      rfl, hinputBoundarySize⟩
  have hfirstIndex : 0 < suffixes.length := by
    rw [hsuffixCount]
    omega
  rcases hsuffixRows 0 hfirstIndex with
    ⟨firstStart, _hfirstStartBound,
      firstFinish, _hfirstFinishBound,
      hfirstStartEntry, hfirstFinishEntry, hfirstLayout⟩
  rw [hfirst] at hfirstLayout
  rcases hfirstLayout with
    ⟨firstBoundary, hfirstStructure, hfirstRows, hfirstBoundarySize⟩
  have hfirstWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount firstStart
        (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix).length
        firstFinish firstBoundary (Nat.size firstBoundary) :=
    ⟨hfirstStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfirstRows,
      rfl, hfirstBoundarySize⟩
  have hfinalIndex : Gamma.length < suffixes.length := by
    rw [hsuffixCount]
    omega
  rcases hsuffixRows Gamma.length hfinalIndex with
    ⟨finalStart, _hfinalStartBound,
      finalFinish, _hfinalFinishBound,
      hfinalStartEntry, hfinalFinishEntry, hfinalLayout⟩
  rw [hfinal] at hfinalLayout
  rcases hfinalLayout with
    ⟨finalBoundary, hfinalStructure, hfinalRows, hfinalBoundarySize⟩
  have hfinalWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount finalStart suffix.length finalFinish
        finalBoundary (Nat.size finalBoundary) :=
    ⟨hfinalStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hfinalRows,
      rfl, hfinalBoundarySize⟩
  have hinputCons :
      compactSequentListTokens Gamma ++ suffix =
        (Gamma.map compactArithmeticFormulaTokens).length ::
          (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix) := by
    simp [compactSequentListTokens]
  have hcons : CompactAdditiveNatListConsRows
      tokenTable width tokenCount firstBoundary
        (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix).length
        inputBoundary (compactSequentListTokens Gamma ++ suffix).length
        (Gamma.map compactArithmeticFormulaTokens).length :=
    CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hfirstRows hinputRows hinputCons
  let coordinates : CompactSequentFormulaEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := (compactSequentListTokens Gamma ++ suffix).length
      inputBoundarySize := Nat.size inputBoundary
      firstStart := firstStart
      firstFinish := firstFinish
      firstBoundary := firstBoundary
      firstCount :=
        (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix).length
      firstBoundarySize := Nat.size firstBoundary
      suffixBoundary := suffixBoundary
      suffixCount := suffixes.length
      valueBoundary := valueBoundary
      valueCount := (Gamma.map compactArithmeticFormulaTokens).length
      valueBoundarySize := Nat.size valueBoundary
      finalBoundary := finalBoundary
      finalCount := suffix.length
      finalBoundarySize := Nat.size finalBoundary
      traceTableWidth := traceTableWidth
      traceValueBound := 2 ^ traceTableWidth }
  refine ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    valueStart, valueFinish, finalStart, finalFinish, coordinates, ?_⟩
  change
    CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount inputStart
          (compactSequentListTokens Gamma ++ suffix).length inputFinish
          inputBoundary (Nat.size inputBoundary) ∧
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount firstStart
          (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix).length
          firstFinish firstBoundary (Nat.size firstBoundary) ∧
      CompactAdditiveNatListWitnessRows
        tokenTable width tokenCount finalStart suffix.length finalFinish
          finalBoundary (Nat.size finalBoundary) ∧
      CompactSequentFormulaTraceBoundedGraph
        tokenTable width tokenCount suffixBoundary suffixes.length
          valueBoundary (Gamma.map compactArithmeticFormulaTokens).length
          traceTableWidth (2 ^ traceTableWidth) ∧
      CompactFixedWidthEntry suffixBoundary tokenCount 0 firstStart ∧
      CompactFixedWidthEntry suffixBoundary tokenCount 1 firstFinish ∧
      CompactFixedWidthEntry suffixBoundary tokenCount
        (Gamma.map compactArithmeticFormulaTokens).length finalStart ∧
      CompactFixedWidthEntry suffixBoundary tokenCount
        ((Gamma.map compactArithmeticFormulaTokens).length + 1)
          finalFinish ∧
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount firstBoundary
          (Gamma.flatMap compactArithmeticFormulaTokens ++ suffix).length
          inputBoundary (compactSequentListTokens Gamma ++ suffix).length
          (Gamma.map compactArithmeticFormulaTokens).length ∧
      CompactAdditiveStructuredListLayout
        tokenTable width tokenCount valueStart
          (Gamma.map compactArithmeticFormulaTokens).length valueFinish
          valueBoundary ∧
      Nat.size valueBoundary = Nat.size valueBoundary ∧
      Nat.size valueBoundary ≤
        ((Gamma.map compactArithmeticFormulaTokens).length + 1) *
          tokenCount
  refine ⟨hinputWitness, hfirstWitness, hfinalWitness, htrace,
    hfirstStartEntry, hfirstFinishEntry, ?_, ?_, hcons,
    hvalueStructure, rfl, hvalueBoundarySize⟩
  · simpa using hfinalStartEntry
  · simpa using hfinalFinishEntry

/-- Every exact endpoint graph has one explicit bound for all eighteen local
witnesses. -/
theorem CompactSequentFormulaEndpointGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish
      valueStart valueFinish finalStart finalFinish : Nat}
    {coordinates : CompactSequentFormulaEndpointCoordinates}
    (hgraph : CompactSequentFormulaEndpointGraph
      tokenTable width tokenCount inputStart inputFinish
        valueStart valueFinish finalStart finalFinish coordinates) :
    ∃ endpointBound,
      CompactSequentFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.firstStart +
    coordinates.firstFinish + coordinates.firstBoundary +
    coordinates.firstCount + coordinates.firstBoundarySize +
    coordinates.suffixBoundary + coordinates.suffixCount +
    coordinates.valueBoundary + coordinates.valueCount +
    coordinates.valueBoundarySize + coordinates.finalBoundary +
    coordinates.finalCount + coordinates.finalBoundarySize +
    coordinates.traceTableWidth + coordinates.traceValueBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactSequentFormulaEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_,
      coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_,
      coordinates.firstStart, ?_,
      coordinates.firstFinish, ?_,
      coordinates.firstBoundary, ?_,
      coordinates.firstCount, ?_,
      coordinates.firstBoundarySize, ?_,
      coordinates.suffixBoundary, ?_,
      coordinates.suffixCount, ?_,
      coordinates.valueBoundary, ?_,
      coordinates.valueCount, ?_,
      coordinates.valueBoundarySize, ?_,
      coordinates.finalBoundary, ?_,
      coordinates.finalCount, ?_,
      coordinates.finalBoundarySize, ?_,
      coordinates.traceTableWidth, ?_,
      coordinates.traceValueBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

/-- Bidirectional closure of the successful public sequent-parser endpoint:
success constructs a bounded arithmetic witness, while the existing soundness
theorem reconstructs the same public parser run from such a witness. -/
theorem exists_compactSequentFormulaEndpointBoundedGraph_of_success
    {input : List Nat} {values : List (List Nat)} {suffix : List Nat}
    (hparser : compactSequentTokenValueParser input =
      some (values, suffix)) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ valueStart valueFinish finalStart finalFinish endpointBound,
      CompactSequentFormulaEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          valueStart valueFinish finalStart finalFinish endpointBound := by
  rcases exists_compactSequentFormulaEndpointGraph_of_success hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      valueStart, valueFinish, finalStart, finalFinish,
      coordinates, hgraph⟩
  rcases CompactSequentFormulaEndpointGraph.exists_bounded hgraph with
    ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    valueStart, valueFinish, finalStart, finalFinish,
    endpointBound, hbounded⟩

#print axioms exists_compactSequentFormulaEndpointGraph_of_success
#print axioms exists_compactSequentFormulaEndpointGraph_of_rows
#print axioms CompactSequentFormulaEndpointGraph.exists_bounded
#print axioms exists_compactSequentFormulaEndpointBoundedGraph_of_success

end FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
