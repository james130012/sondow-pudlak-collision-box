import integration.FoundationCompactNumericListedDirectSequentFormulaFailureEndpointCompleteness

/-!
# Bounded arithmetic formula for failed sequent parses

The arithmetic graph keeps explicit rows for the original input, its shared
tail, and the successful-prefix input.  Existing bounded endpoint formulas
then certify the prefix success and the first formula-parser no-output trace.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSequentFormulaFailureBoundedFormula

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectSequentFormulaEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
open FoundationCompactNumericListedDirectSequentFormulaFailureSemantics
open FoundationCompactNumericListedDirectSequentFormulaFailureEndpoint
open FoundationCompactNumericListedDirectSequentFormulaFailureEndpointCompleteness

structure CompactSequentFormulaFailureArithmeticCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailStart : Nat
  tailFinish : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  prefixInputStart : Nat
  prefixInputFinish : Nat
  prefixInputBoundary : Nat
  prefixInputCount : Nat
  prefixInputBoundarySize : Nat
  count : Nat
  failedIndex : Nat
  valueStart : Nat
  valueFinish : Nat
  failedStart : Nat
  failedFinish : Nat
  prefixBound : Nat
  failureBound : Nat

def CompactSequentFormulaFailureArithmeticGraph
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactSequentFormulaFailureArithmeticCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
        coordinates.tailFinish coordinates.tailBoundary
        coordinates.tailBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount coordinates.prefixInputStart
        coordinates.prefixInputCount coordinates.prefixInputFinish
        coordinates.prefixInputBoundary coordinates.prefixInputBoundarySize ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary
        coordinates.tailCount coordinates.inputBoundary coordinates.inputCount
        coordinates.count ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary
        coordinates.tailCount coordinates.prefixInputBoundary
        coordinates.prefixInputCount coordinates.failedIndex ∧
    coordinates.failedIndex < coordinates.count ∧
    CompactSequentFormulaEndpointBoundedGraph
      tokenTable width tokenCount coordinates.prefixInputStart
        coordinates.prefixInputFinish coordinates.valueStart
        coordinates.valueFinish coordinates.failedStart
        coordinates.failedFinish coordinates.prefixBound ∧
    CompactParserSyntaxNoOutputExactEndpointBoundedGraph
      tokenTable width tokenCount coordinates.failedStart
        coordinates.failedFinish 1 0 0 coordinates.failureBound

def compactSequentFormulaFailureArithmeticGraphDef :
    𝚺₀.Semisentence 26 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      prefixInputStart prefixInputFinish prefixInputBoundary
      prefixInputCount prefixInputBoundarySize
      count failedIndex valueStart valueFinish failedStart failedFinish
      prefixBound failureBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
      inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount tailStart tailCount tailFinish
      tailBoundary tailBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount prefixInputStart prefixInputCount
      prefixInputFinish prefixInputBoundary prefixInputBoundarySize ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount tailBoundary tailCount
      inputBoundary inputCount count ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount tailBoundary tailCount
      prefixInputBoundary prefixInputCount failedIndex ∧
    failedIndex < count ∧
    !(compactSequentFormulaEndpointBoundedGraphDef)
      tokenTable width tokenCount prefixInputStart prefixInputFinish
      valueStart valueFinish failedStart failedFinish prefixBound ∧
    !(compactParserSyntaxNoOutputExactEndpointBoundedGraphDef)
      tokenTable width tokenCount failedStart failedFinish 1 0 0 failureBound”

def compactSequentFormulaFailureArithmeticEnvironment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactSequentFormulaFailureArithmeticCoordinates) :
    Fin 26 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailStart, coordinates.tailFinish,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize,
    coordinates.prefixInputStart, coordinates.prefixInputFinish,
    coordinates.prefixInputBoundary, coordinates.prefixInputCount,
    coordinates.prefixInputBoundarySize,
    coordinates.count, coordinates.failedIndex,
    coordinates.valueStart, coordinates.valueFinish,
    coordinates.failedStart, coordinates.failedFinish,
    coordinates.prefixBound, coordinates.failureBound]

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaFailureArithmeticGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactSequentFormulaFailureArithmeticCoordinates) :
    compactSequentFormulaFailureArithmeticGraphDef.val.Evalb
        (compactSequentFormulaFailureArithmeticEnvironment
          tokenTable width tokenCount inputStart inputFinish coordinates) ↔
      CompactSequentFormulaFailureArithmeticGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  let env := compactSequentFormulaFailureArithmeticEnvironment
    tokenTable width tokenCount inputStart inputFinish coordinates
  change compactSequentFormulaFailureArithmeticGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #3, #6, #4, #5, #7]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #8, #11, #9, #10, #12]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hprefixInputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #13, #16, #14,
          #15, #17]) =
        ![tokenTable, width, tokenCount, coordinates.prefixInputStart,
          coordinates.prefixInputCount, coordinates.prefixInputFinish,
          coordinates.prefixInputBoundary,
          coordinates.prefixInputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have hinputConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #10, #11,
          #5, #6, #18]) =
        ![tokenTable, width, tokenCount, coordinates.tailBoundary,
          coordinates.tailCount, coordinates.inputBoundary,
          coordinates.inputCount, coordinates.count] := by
    funext index
    fin_cases index <;> rfl
  have hprefixConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #10, #11,
          #15, #16, #19]) =
        ![tokenTable, width, tokenCount, coordinates.tailBoundary,
          coordinates.tailCount, coordinates.prefixInputBoundary,
          coordinates.prefixInputCount, coordinates.failedIndex] := by
    funext index
    fin_cases index <;> rfl
  have hprefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #13, #14,
          #20, #21, #22, #23, #24]) =
        ![tokenTable, width, tokenCount,
          coordinates.prefixInputStart, coordinates.prefixInputFinish,
          coordinates.valueStart, coordinates.valueFinish,
          coordinates.failedStart, coordinates.failedFinish,
          coordinates.prefixBound] := by
    funext index
    fin_cases index <;> rfl
  have hfailureEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 26), #1, #2, #22, #23,
          ‘1’, ‘0’, ‘0’, #25]) =
        ![tokenTable, width, tokenCount,
          coordinates.failedStart, coordinates.failedFinish,
          1, 0, 0, coordinates.failureBound] := by
    funext index
    fin_cases index <;> simp [env,
      compactSequentFormulaFailureArithmeticEnvironment]
  have hfailedIndexValue : env 19 = coordinates.failedIndex := rfl
  have hcountValue : env 18 = coordinates.count := rfl
  simp [compactSequentFormulaFailureArithmeticGraphDef,
    CompactSequentFormulaFailureArithmeticGraph,
    hinputEnv, htailEnv, hprefixInputEnv,
    hinputConsEnv, hprefixConsEnv, hprefixEnv, hfailureEnv,
    hfailedIndexValue, hcountValue]

theorem compactSequentFormulaFailureArithmeticGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaFailureArithmeticGraphDef.val := by
  simp [compactSequentFormulaFailureArithmeticGraphDef]

theorem CompactSequentFormulaFailureArithmeticGraph.sound
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactSequentFormulaFailureArithmeticCoordinates}
    (hgraph : CompactSequentFormulaFailureArithmeticGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactSequentTokenValueParser input = none := by
  rcases hgraph with
    ⟨hinputWitness, htailWitness, hprefixInputWitness,
      hinputCons, hprefixCons, hfailedIndex, hprefix, hfailure⟩
  rcases hinputWitness.realize with
    ⟨input, hinputCount, hinputLayout, hinputRows⟩
  rcases htailWitness.realize with
    ⟨tail, htailCount, _htailLayout, htailRows⟩
  rcases hprefixInputWitness.realize with
    ⟨prefixInput, hprefixInputCount, hprefixInputLayout, hprefixInputRows⟩
  have hinputCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary tail.length
        coordinates.inputBoundary input.length coordinates.count := by
    simpa only [htailCount, hinputCount] using hinputCons
  have hinputEq : input = coordinates.count :: tail :=
    hinputCons'.eq_cons_of_rows htailRows hinputRows
  have hprefixCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary tail.length
        coordinates.prefixInputBoundary prefixInput.length
        coordinates.failedIndex := by
    simpa only [htailCount, hprefixInputCount] using hprefixCons
  have hprefixInputEq :
      prefixInput = coordinates.failedIndex :: tail :=
    hprefixCons'.eq_cons_of_rows htailRows hprefixInputRows
  rcases hprefix.sound with
    ⟨decodedPrefixInput, values, failedTokens,
      hdecodedPrefixLayout, _hvaluesLayout,
      hfailedLayout, hprefixParser⟩
  have hdecodedPrefixEq : decodedPrefixInput = prefixInput :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hprefixInputLayout hdecodedPrefixLayout).1
  rw [hdecodedPrefixEq, hprefixInputEq] at hprefixParser
  have hprefixRepeat :
      compactFormulaTokenValuesRepeat coordinates.failedIndex tail =
        some (values, failedTokens) := by
    simpa [compactSequentTokenValueParser] using hprefixParser
  rcases hfailure.sound_formula with
    ⟨failureInput, hfailureLayout, hfailureParser⟩
  have hfailureInputEq : failureInput = failedTokens :=
    (CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hfailedLayout hfailureLayout).1
  rw [hfailureInputEq] at hfailureParser
  have hfailureValueParser :
      compactFormulaTokenValueParser 0 failedTokens = none := by
    simp [compactFormulaTokenValueParser, hfailureParser]
  have hparser : compactSequentTokenValueParser
      (coordinates.count :: tail) = none :=
    (compactSequentTokenValueParser_cons_eq_none_iff
      coordinates.count tail).mpr
        ⟨coordinates.failedIndex, hfailedIndex,
          values, failedTokens, hprefixRepeat, hfailureValueParser⟩
  exact ⟨input, hinputLayout, by simpa only [hinputEq] using hparser⟩

theorem exists_compactSequentFormulaFailureArithmeticGraph_of_exact
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactSequentFormulaFailureEndpointCoordinates}
    (hgraph : CompactSequentFormulaFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ arithmeticCoordinates : CompactSequentFormulaFailureArithmeticCoordinates,
      CompactSequentFormulaFailureArithmeticGraph
        tokenTable width tokenCount inputStart inputFinish
          arithmeticCoordinates := by
  rcases hgraph with
    ⟨hinputWitness, hprefix, hfailedIndex, hinputCons, hfailure⟩
  have hprefixParts := hprefix
  rcases hprefixParts with
    ⟨hprefixInputWitness, hfirstWitness, _hfinalWitness,
      _htrace, _hfirstStartEntry, _hfirstFinishEntry,
      _hfinalStartEntry, _hfinalFinishEntry, hprefixCons,
      _hvalueStructure, _hvalueSizeEq, _hvalueSize⟩
  rcases
      FoundationCompactNumericListedDirectSequentFormulaEndpointCompleteness.CompactSequentFormulaEndpointGraph.exists_bounded
        hprefix with
    ⟨prefixBound, hprefixBounded⟩
  rcases
      FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula.CompactParserSyntaxNoOutputExactEndpointGraph.exists_bounded
        hfailure with
    ⟨failureBound, hfailureBounded⟩
  let arithmeticCoordinates :
      CompactSequentFormulaFailureArithmeticCoordinates :=
    { inputBoundary := coordinates.inputBoundary
      inputCount := coordinates.inputCount
      inputBoundarySize := coordinates.inputBoundarySize
      tailStart := coordinates.prefixEndpoint.firstStart
      tailFinish := coordinates.prefixEndpoint.firstFinish
      tailBoundary := coordinates.prefixEndpoint.firstBoundary
      tailCount := coordinates.prefixEndpoint.firstCount
      tailBoundarySize := coordinates.prefixEndpoint.firstBoundarySize
      prefixInputStart := coordinates.prefixInputStart
      prefixInputFinish := coordinates.prefixInputFinish
      prefixInputBoundary := coordinates.prefixEndpoint.inputBoundary
      prefixInputCount := coordinates.prefixEndpoint.inputCount
      prefixInputBoundarySize :=
        coordinates.prefixEndpoint.inputBoundarySize
      count := coordinates.count
      failedIndex := coordinates.prefixEndpoint.valueCount
      valueStart := coordinates.valueStart
      valueFinish := coordinates.valueFinish
      failedStart := coordinates.failedStart
      failedFinish := coordinates.failedFinish
      prefixBound := prefixBound
      failureBound := failureBound }
  exact ⟨arithmeticCoordinates, hinputWitness, hfirstWitness,
    hprefixInputWitness, hinputCons, hprefixCons,
    hfailedIndex, hprefixBounded, hfailureBounded⟩

theorem exists_compactSequentFormulaFailureArithmeticGraph_of_cons_none
    (count : Nat) (inputTail : List Nat)
    (hparser : compactSequentTokenValueParser (count :: inputTail) = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactSequentFormulaFailureArithmeticCoordinates,
      CompactSequentFormulaFailureArithmeticGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases exists_compactSequentFormulaFailureEndpointGraph_of_cons_none
      count inputTail hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      exactCoordinates, hexact⟩
  rcases exists_compactSequentFormulaFailureArithmeticGraph_of_exact
      hexact with
    ⟨coordinates, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates, hgraph⟩

def compactSequentFormulaFailureArithmeticCoordinatesOfValues
    (inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      prefixInputStart prefixInputFinish prefixInputBoundary
      prefixInputCount prefixInputBoundarySize count failedIndex
      valueStart valueFinish failedStart failedFinish
      prefixBound failureBound : Nat) :
    CompactSequentFormulaFailureArithmeticCoordinates :=
  { inputBoundary := inputBoundary
    inputCount := inputCount
    inputBoundarySize := inputBoundarySize
    tailStart := tailStart
    tailFinish := tailFinish
    tailBoundary := tailBoundary
    tailCount := tailCount
    tailBoundarySize := tailBoundarySize
    prefixInputStart := prefixInputStart
    prefixInputFinish := prefixInputFinish
    prefixInputBoundary := prefixInputBoundary
    prefixInputCount := prefixInputCount
    prefixInputBoundarySize := prefixInputBoundarySize
    count := count
    failedIndex := failedIndex
    valueStart := valueStart
    valueFinish := valueFinish
    failedStart := failedStart
    failedFinish := failedFinish
    prefixBound := prefixBound
    failureBound := failureBound }

def CompactSequentFormulaFailureEndpointBoundedGraph
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    Prop :=
  ∃ inputBoundary, inputBoundary ≤ endpointBound ∧
  ∃ inputCount, inputCount ≤ endpointBound ∧
  ∃ inputBoundarySize, inputBoundarySize ≤ endpointBound ∧
  ∃ tailStart, tailStart ≤ endpointBound ∧
  ∃ tailFinish, tailFinish ≤ endpointBound ∧
  ∃ tailBoundary, tailBoundary ≤ endpointBound ∧
  ∃ tailCount, tailCount ≤ endpointBound ∧
  ∃ tailBoundarySize, tailBoundarySize ≤ endpointBound ∧
  ∃ prefixInputStart, prefixInputStart ≤ endpointBound ∧
  ∃ prefixInputFinish, prefixInputFinish ≤ endpointBound ∧
  ∃ prefixInputBoundary, prefixInputBoundary ≤ endpointBound ∧
  ∃ prefixInputCount, prefixInputCount ≤ endpointBound ∧
  ∃ prefixInputBoundarySize, prefixInputBoundarySize ≤ endpointBound ∧
  ∃ count, count ≤ endpointBound ∧
  ∃ failedIndex, failedIndex ≤ endpointBound ∧
  ∃ valueStart, valueStart ≤ endpointBound ∧
  ∃ valueFinish, valueFinish ≤ endpointBound ∧
  ∃ failedStart, failedStart ≤ endpointBound ∧
  ∃ failedFinish, failedFinish ≤ endpointBound ∧
  ∃ prefixBound, prefixBound ≤ endpointBound ∧
  ∃ failureBound, failureBound ≤ endpointBound ∧
    CompactSequentFormulaFailureArithmeticGraph
      tokenTable width tokenCount inputStart inputFinish
        (compactSequentFormulaFailureArithmeticCoordinatesOfValues
          inputBoundary inputCount inputBoundarySize
          tailStart tailFinish tailBoundary tailCount tailBoundarySize
          prefixInputStart prefixInputFinish prefixInputBoundary
          prefixInputCount prefixInputBoundarySize count failedIndex
          valueStart valueFinish failedStart failedFinish
          prefixBound failureBound)

def compactSequentFormulaFailureEndpointBoundedGraphDef :
    𝚺₀.Semisentence 6 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish endpointBound.
    ∃ inputBoundary <⁺ endpointBound,
    ∃ inputCount <⁺ endpointBound,
    ∃ inputBoundarySize <⁺ endpointBound,
    ∃ tailStart <⁺ endpointBound,
    ∃ tailFinish <⁺ endpointBound,
    ∃ tailBoundary <⁺ endpointBound,
    ∃ tailCount <⁺ endpointBound,
    ∃ tailBoundarySize <⁺ endpointBound,
    ∃ prefixInputStart <⁺ endpointBound,
    ∃ prefixInputFinish <⁺ endpointBound,
    ∃ prefixInputBoundary <⁺ endpointBound,
    ∃ prefixInputCount <⁺ endpointBound,
    ∃ prefixInputBoundarySize <⁺ endpointBound,
    ∃ count <⁺ endpointBound,
    ∃ failedIndex <⁺ endpointBound,
    ∃ valueStart <⁺ endpointBound,
    ∃ valueFinish <⁺ endpointBound,
    ∃ failedStart <⁺ endpointBound,
    ∃ failedFinish <⁺ endpointBound,
    ∃ prefixBound <⁺ endpointBound,
    ∃ failureBound <⁺ endpointBound,
      !(compactSequentFormulaFailureArithmeticGraphDef)
        tokenTable width tokenCount inputStart inputFinish
        inputBoundary inputCount inputBoundarySize
        tailStart tailFinish tailBoundary tailCount tailBoundarySize
        prefixInputStart prefixInputFinish prefixInputBoundary
        prefixInputCount prefixInputBoundarySize count failedIndex
        valueStart valueFinish failedStart failedFinish
        prefixBound failureBound”

set_option maxRecDepth 4096 in
@[simp] theorem compactSequentFormulaFailureEndpointBoundedGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish endpointBound : Nat) :
    compactSequentFormulaFailureEndpointBoundedGraphDef.val.Evalb
        ![tokenTable, width, tokenCount, inputStart, inputFinish,
          endpointBound] ↔
      CompactSequentFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  have hrow
      (failureBound prefixBound failedFinish failedStart
        valueFinish valueStart failedIndex count
        prefixInputBoundarySize prefixInputCount prefixInputBoundary
        prefixInputFinish prefixInputStart tailBoundarySize tailCount
        tailBoundary tailFinish tailStart inputBoundarySize
        inputCount inputBoundary : Nat) :
      (Semiformula.Eval
          (Semiterm.val
              ![failureBound, prefixBound, failedFinish, failedStart,
                valueFinish, valueStart, failedIndex, count,
                prefixInputBoundarySize, prefixInputCount,
                prefixInputBoundary, prefixInputFinish, prefixInputStart,
                tailBoundarySize, tailCount, tailBoundary,
                tailFinish, tailStart, inputBoundarySize,
                inputCount, inputBoundary, tokenTable, width, tokenCount,
                inputStart, inputFinish, endpointBound]
              Empty.elim ∘
            ![(#21 : Semiterm ℒₒᵣ Empty 27), #22, #23, #24, #25,
              #20, #19, #18, #17, #16, #15, #14, #13, #12, #11,
              #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0])
          Empty.elim) compactSequentFormulaFailureArithmeticGraphDef.val ↔
        CompactSequentFormulaFailureArithmeticGraph
          tokenTable width tokenCount inputStart inputFinish
            (compactSequentFormulaFailureArithmeticCoordinatesOfValues
              inputBoundary inputCount inputBoundarySize
              tailStart tailFinish tailBoundary tailCount tailBoundarySize
              prefixInputStart prefixInputFinish prefixInputBoundary
              prefixInputCount prefixInputBoundarySize count failedIndex
              valueStart valueFinish failedStart failedFinish
              prefixBound failureBound) := by
    have henv :
        (Semiterm.val
            ![failureBound, prefixBound, failedFinish, failedStart,
              valueFinish, valueStart, failedIndex, count,
              prefixInputBoundarySize, prefixInputCount,
              prefixInputBoundary, prefixInputFinish, prefixInputStart,
              tailBoundarySize, tailCount, tailBoundary,
              tailFinish, tailStart, inputBoundarySize,
              inputCount, inputBoundary, tokenTable, width, tokenCount,
              inputStart, inputFinish, endpointBound]
            Empty.elim ∘
          ![(#21 : Semiterm ℒₒᵣ Empty 27), #22, #23, #24, #25,
            #20, #19, #18, #17, #16, #15, #14, #13, #12, #11,
            #10, #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]) =
          compactSequentFormulaFailureArithmeticEnvironment
            tokenTable width tokenCount inputStart inputFinish
              (compactSequentFormulaFailureArithmeticCoordinatesOfValues
                inputBoundary inputCount inputBoundarySize
                tailStart tailFinish tailBoundary tailCount tailBoundarySize
                prefixInputStart prefixInputFinish prefixInputBoundary
                prefixInputCount prefixInputBoundarySize count failedIndex
                valueStart valueFinish failedStart failedFinish
                prefixBound failureBound) := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [henv]
    exact compactSequentFormulaFailureArithmeticGraphDef_spec
      tokenTable width tokenCount inputStart inputFinish _
  simp [compactSequentFormulaFailureEndpointBoundedGraphDef,
    CompactSequentFormulaFailureEndpointBoundedGraph, hrow]

theorem compactSequentFormulaFailureEndpointBoundedGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactSequentFormulaFailureEndpointBoundedGraphDef.val := by
  simp [compactSequentFormulaFailureEndpointBoundedGraphDef]

theorem CompactSequentFormulaFailureEndpointBoundedGraph.exists_coordinates
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactSequentFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ coordinates : CompactSequentFormulaFailureArithmeticCoordinates,
      CompactSequentFormulaFailureArithmeticGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases hbounded with
    ⟨inputBoundary, _, inputCount, _, inputBoundarySize, _,
      tailStart, _, tailFinish, _, tailBoundary, _, tailCount, _,
      tailBoundarySize, _, prefixInputStart, _, prefixInputFinish, _,
      prefixInputBoundary, _, prefixInputCount, _,
      prefixInputBoundarySize, _, count, _, failedIndex, _,
      valueStart, _, valueFinish, _, failedStart, _, failedFinish, _,
      prefixBound, _, failureBound, _, hgraph⟩
  exact ⟨compactSequentFormulaFailureArithmeticCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize
    tailStart tailFinish tailBoundary tailCount tailBoundarySize
    prefixInputStart prefixInputFinish prefixInputBoundary
    prefixInputCount prefixInputBoundarySize count failedIndex
    valueStart valueFinish failedStart failedFinish
    prefixBound failureBound, hgraph⟩

theorem CompactSequentFormulaFailureEndpointBoundedGraph.sound
    {tokenTable width tokenCount inputStart inputFinish endpointBound : Nat}
    (hbounded : CompactSequentFormulaFailureEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish endpointBound) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactSequentTokenValueParser input = none := by
  rcases hbounded.exists_coordinates with ⟨coordinates, hgraph⟩
  exact hgraph.sound

theorem CompactSequentFormulaFailureArithmeticGraph.exists_bounded
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactSequentFormulaFailureArithmeticCoordinates}
    (hgraph : CompactSequentFormulaFailureArithmeticGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ endpointBound,
      CompactSequentFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  let endpointBound :=
    coordinates.inputBoundary + coordinates.inputCount +
    coordinates.inputBoundarySize + coordinates.tailStart +
    coordinates.tailFinish + coordinates.tailBoundary +
    coordinates.tailCount + coordinates.tailBoundarySize +
    coordinates.prefixInputStart + coordinates.prefixInputFinish +
    coordinates.prefixInputBoundary + coordinates.prefixInputCount +
    coordinates.prefixInputBoundarySize + coordinates.count +
    coordinates.failedIndex + coordinates.valueStart +
    coordinates.valueFinish + coordinates.failedStart +
    coordinates.failedFinish + coordinates.prefixBound +
    coordinates.failureBound
  refine ⟨endpointBound, ?_⟩
  unfold CompactSequentFormulaFailureEndpointBoundedGraph
  refine
    ⟨coordinates.inputBoundary, ?_, coordinates.inputCount, ?_,
      coordinates.inputBoundarySize, ?_, coordinates.tailStart, ?_,
      coordinates.tailFinish, ?_, coordinates.tailBoundary, ?_,
      coordinates.tailCount, ?_, coordinates.tailBoundarySize, ?_,
      coordinates.prefixInputStart, ?_, coordinates.prefixInputFinish, ?_,
      coordinates.prefixInputBoundary, ?_,
      coordinates.prefixInputCount, ?_,
      coordinates.prefixInputBoundarySize, ?_, coordinates.count, ?_,
      coordinates.failedIndex, ?_, coordinates.valueStart, ?_,
      coordinates.valueFinish, ?_, coordinates.failedStart, ?_,
      coordinates.failedFinish, ?_, coordinates.prefixBound, ?_,
      coordinates.failureBound, ?_, hgraph⟩ <;>
    dsimp only [endpointBound] <;> omega

theorem exists_compactSequentFormulaFailureEndpointBoundedGraph_of_cons_none
    (count : Nat) (inputTail : List Nat)
    (hparser : compactSequentTokenValueParser (count :: inputTail) = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactSequentFormulaFailureEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish endpointBound := by
  rcases exists_compactSequentFormulaFailureArithmeticGraph_of_cons_none
      count inputTail hparser with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, hgraph⟩
  rcases hgraph.exists_bounded with ⟨endpointBound, hbounded⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    endpointBound, hbounded⟩

#print axioms compactSequentFormulaFailureArithmeticGraphDef_spec
#print axioms compactSequentFormulaFailureArithmeticGraphDef_sigmaZero
#print axioms CompactSequentFormulaFailureArithmeticGraph.sound
#print axioms exists_compactSequentFormulaFailureArithmeticGraph_of_exact
#print axioms exists_compactSequentFormulaFailureArithmeticGraph_of_cons_none
#print axioms compactSequentFormulaFailureEndpointBoundedGraphDef_spec
#print axioms compactSequentFormulaFailureEndpointBoundedGraphDef_sigmaZero
#print axioms CompactSequentFormulaFailureEndpointBoundedGraph.sound
#print axioms CompactSequentFormulaFailureArithmeticGraph.exists_bounded
#print axioms exists_compactSequentFormulaFailureEndpointBoundedGraph_of_cons_none

end FoundationCompactNumericListedDirectSequentFormulaFailureBoundedFormula
