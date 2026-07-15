import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint

/-!
# Exact endpoint for failed induction PA certificates

PA tag 22 delegates to the formula parser at binder arity one.  This endpoint
puts the outer structural tag, PA tag, formula input, and complete no-output
parser trace in one fixed-width table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointCompleteness
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointFormula

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

structure CompactCertificateNodeInductionPAFailureEndpointCoordinates where
  inputBoundary : Nat
  inputCount : Nat
  inputBoundarySize : Nat
  tailStart : Nat
  tailFinish : Nat
  tailBoundary : Nat
  tailCount : Nat
  tailBoundarySize : Nat
  formulaStart : Nat
  formulaFinish : Nat
  parser : CompactParserSyntaxNoOutputExactEndpointCoordinates

def CompactCertificateNodeInductionPAFailureEndpointGraph
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates) : Prop :=
  CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart coordinates.inputCount inputFinish
        coordinates.inputBoundary coordinates.inputBoundarySize ∧
    CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount coordinates.tailStart coordinates.tailCount
        coordinates.tailFinish coordinates.tailBoundary
        coordinates.tailBoundarySize ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.tailBoundary coordinates.tailCount
        coordinates.inputBoundary coordinates.inputCount 1 ∧
    CompactAdditiveNatListConsRows
      tokenTable width tokenCount
        coordinates.parser.inputBoundary coordinates.parser.inputCount
        coordinates.tailBoundary coordinates.tailCount 22 ∧
    CompactParserSyntaxNoOutputExactEndpointGraph
      tokenTable width tokenCount coordinates.formulaStart coordinates.formulaFinish
        1 1 0 coordinates.parser

def compactCertificateNodeInductionPAFailureEndpointGraphDef :
    𝚺₀.Semisentence 22 := .mkSigma
  “tokenTable width tokenCount inputStart inputFinish
      inputBoundary inputCount inputBoundarySize
      tailStart tailFinish tailBoundary tailCount tailBoundarySize
      formulaStart formulaFinish
      formulaBoundary formulaCount formulaBoundarySize
      stateBoundary stateCount tableWidth valueBound.
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount inputStart inputCount inputFinish
        inputBoundary inputBoundarySize ∧
    !(compactAdditiveNatListWitnessRowsDef)
      tokenTable width tokenCount tailStart tailCount tailFinish
        tailBoundary tailBoundarySize ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        tailBoundary tailCount inputBoundary inputCount 1 ∧
    !(compactAdditiveNatListConsRowsDef)
      tokenTable width tokenCount
        formulaBoundary formulaCount tailBoundary tailCount 22 ∧
    !(compactParserSyntaxNoOutputExactEndpointGraphDef)
      tokenTable width tokenCount formulaStart formulaFinish 1 1 0
        formulaBoundary formulaCount formulaBoundarySize
        stateBoundary stateCount tableWidth valueBound”

def compactCertificateNodeInductionPAFailureEndpointEnvironment
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates) :
    Fin 22 → Nat :=
  ![tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates.inputBoundary, coordinates.inputCount,
    coordinates.inputBoundarySize,
    coordinates.tailStart, coordinates.tailFinish,
    coordinates.tailBoundary, coordinates.tailCount,
    coordinates.tailBoundarySize,
    coordinates.formulaStart, coordinates.formulaFinish,
    coordinates.parser.inputBoundary, coordinates.parser.inputCount,
    coordinates.parser.inputBoundarySize,
    coordinates.parser.stateBoundary, coordinates.parser.stateCount,
    coordinates.parser.tableWidth, coordinates.parser.valueBound]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
@[simp] theorem compactCertificateNodeInductionPAFailureEndpointGraphDef_spec
    (tokenTable width tokenCount inputStart inputFinish : Nat)
    (coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates) :
    compactCertificateNodeInductionPAFailureEndpointGraphDef.val.Evalb
        (compactCertificateNodeInductionPAFailureEndpointEnvironment
          tokenTable width tokenCount inputStart inputFinish coordinates) ↔
      CompactCertificateNodeInductionPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  let env := compactCertificateNodeInductionPAFailureEndpointEnvironment
    tokenTable width tokenCount inputStart inputFinish coordinates
  change compactCertificateNodeInductionPAFailureEndpointGraphDef.val.Evalb env ↔ _
  have hinputEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #3, #6, #4, #5, #7]) =
        ![tokenTable, width, tokenCount, inputStart,
          coordinates.inputCount, inputFinish,
          coordinates.inputBoundary, coordinates.inputBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have htailEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #8, #11, #9, #10, #12]) =
        ![tokenTable, width, tokenCount, coordinates.tailStart,
          coordinates.tailCount, coordinates.tailFinish,
          coordinates.tailBoundary, coordinates.tailBoundarySize] := by
    funext index
    fin_cases index <;> rfl
  have houterConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #10, #11, #5, #6, ‘1’]) =
        ![tokenTable, width, tokenCount,
          coordinates.tailBoundary, coordinates.tailCount,
          coordinates.inputBoundary, coordinates.inputCount, 1] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeInductionPAFailureEndpointEnvironment]
  have hinnerConsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #15, #16, #10, #11, ‘22’]) =
        ![tokenTable, width, tokenCount,
          coordinates.parser.inputBoundary, coordinates.parser.inputCount,
          coordinates.tailBoundary, coordinates.tailCount, 22] := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeInductionPAFailureEndpointEnvironment]
  have hparserEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 22), #1, #2, #13, #14,
          ‘1’, ‘1’, ‘0’, #15, #16, #17, #18, #19, #20, #21]) =
        compactParserSyntaxNoOutputExactEndpointEnvironment
          tokenTable width tokenCount coordinates.formulaStart
            coordinates.formulaFinish 1 1 0 coordinates.parser := by
    funext index
    fin_cases index <;> simp [env,
      compactCertificateNodeInductionPAFailureEndpointEnvironment,
      compactParserSyntaxNoOutputExactEndpointEnvironment]
  simp [compactCertificateNodeInductionPAFailureEndpointGraphDef,
    CompactCertificateNodeInductionPAFailureEndpointGraph,
    hinputEnv, htailEnv, houterConsEnv, hinnerConsEnv, hparserEnv]

theorem compactCertificateNodeInductionPAFailureEndpointGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactCertificateNodeInductionPAFailureEndpointGraphDef.val := by
  simp [compactCertificateNodeInductionPAFailureEndpointGraphDef]

theorem CompactCertificateNodeInductionPAFailureEndpointGraph.sound
    {tokenTable width tokenCount inputStart inputFinish : Nat}
    {coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates}
    (hgraph : CompactCertificateNodeInductionPAFailureEndpointGraph
      tokenTable width tokenCount inputStart inputFinish coordinates) :
    ∃ input : List Nat,
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount inputStart inputFinish input ∧
      compactStructuralCertificateNodeParser input = none := by
  rcases hgraph with
    ⟨hinputRows, htailRows, houterCons, hinnerCons, hparser⟩
  rcases hinputRows.realize with
    ⟨input, hinputCount, hinputLayout, hinputElementRows⟩
  rcases htailRows.realize with
    ⟨tail, htailCount, _htailLayout, htailElementRows⟩
  rcases hparser.sound_formula with
    ⟨formulaInput, hformulaLayout, hformulaParser⟩
  rcases hparser.1.realize with
    ⟨formulaRowsInput, hformulaRowsInputCount,
      hformulaRowsInputLayout, hformulaInputRows⟩
  have hformulaRowsInputEq : formulaRowsInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hformulaRowsInputLayout hformulaLayout).1.symm
  subst formulaRowsInput
  have houterCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.tailBoundary tail.length
        coordinates.inputBoundary input.length 1 := by
    simpa only [hinputCount, htailCount] using houterCons
  have hinnerCons' : CompactAdditiveNatListConsRows
      tokenTable width tokenCount coordinates.parser.inputBoundary
        formulaInput.length coordinates.tailBoundary tail.length 22 := by
    simpa only [hformulaRowsInputCount, htailCount] using hinnerCons
  have hinput : input = 1 :: tail :=
    houterCons'.eq_cons_of_rows htailElementRows hinputElementRows
  have htail : tail = 22 :: formulaInput :=
    hinnerCons'.eq_cons_of_rows hformulaInputRows htailElementRows
  have hpa : compactPAAxiomCertificateTokenParser tail = none := by
    rw [htail]
    simpa [compactPAAxiomCertificateTokenParser] using hformulaParser
  refine ⟨input, hinputLayout, ?_⟩
  rw [hinput]
  simp [compactStructuralCertificateNodeParser, hpa]

theorem exists_compactCertificateNodeInductionPAFailureEndpointGraph_with_inputLayout
    (formulaInput : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish
            (1 :: 22 :: formulaInput) ∧
        CompactCertificateNodeInductionPAFailureEndpointGraph
          tokenTable width tokenCount inputStart inputFinish coordinates := by
  have houtput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound formulaInput])
        (compactFormulaParserInitialState 1 formulaInput)) = none := by
    simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using hformula
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound formulaInput)
      (compactFormulaParserInitialState 1 formulaInput) none).mp houtput with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound formulaInput)
      (formulaInput, [(1, 1, 0)], none) none states := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using hvalid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 1, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  let tail := 22 :: formulaInput
  let input := 1 :: tail
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let formulaTokens := compactAdditiveEncode formulaInput
  let stateTokens := compactAdditiveEncode states
  let tokens := inputTokens ++ tailTokens ++ formulaTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ formulaTokens ++ stateTokens)
  dsimp only at hinputRaw
  have hinputTokenEq : [] ++ compactAdditiveEncode input ++
      (tailTokens ++ formulaTokens ++ stateTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail (formulaTokens ++ stateTokens)
  dsimp only at htailRaw
  have htailTokenEq : inputTokens ++ compactAdditiveEncode tail ++
      (formulaTokens ++ stateTokens) = tokens := by
    simp [tailTokens, tokens, List.append_assoc]
  rw [htailTokenEq] at htailRaw
  have hformulaRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens) formulaInput stateTokens
  dsimp only at hformulaRaw
  have hformulaTokenEq : (inputTokens ++ tailTokens) ++
      compactAdditiveEncode formulaInput ++ stateTokens = tokens := by
    simp [formulaTokens, tokens, List.append_assoc]
  rw [hformulaTokenEq] at hformulaRaw
  have hstatesRaw := compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ formulaTokens) states []
  dsimp only at hstatesRaw
  have hstateTokenEq : (inputTokens ++ tailTokens ++ formulaTokens) ++
      compactAdditiveEncode states ++ [] = tokens := by
    simp [stateTokens, tokens, List.append_assoc]
  rw [hstateTokenEq] at hstatesRaw
  have hinputLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length 0 inputTokens.length input := by
    simpa only [tokenTable, width, inputTokens,
      List.length_nil, Nat.zero_add] using hinputRaw
  have htailLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length inputTokens.length
        (inputTokens.length + tailTokens.length) tail := by
    simpa only [tokenTable, width, tailTokens,
      List.length_append] using htailRaw
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + formulaTokens.length)
        formulaInput := by
    simpa only [tokenTable, width, formulaTokens,
      List.length_append, List.append_assoc] using hformulaRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  rcases hformulaLayout with
    ⟨formulaBoundary, hformulaStructure, hformulaElementRows, hformulaSize⟩
  rcases hstatesRaw with
    ⟨_hstateStructure, hstateRows, _hstateSize⟩
  have hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length 0 input.length inputTokens.length
        inputBoundary (Nat.size inputBoundary) :=
    ⟨hinputStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hinputElementRows,
      rfl, hinputSize⟩
  have htailRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length inputTokens.length tail.length
        (inputTokens.length + tailTokens.length)
        tailBoundary (Nat.size tailBoundary) :=
    ⟨htailStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        htailElementRows,
      rfl, htailSize⟩
  have houterCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length tailBoundary tail.length
        inputBoundary input.length 1 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      htailElementRows hinputElementRows
    rfl
  have hinnerCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length formulaBoundary formulaInput.length
        tailBoundary tail.length 22 := by
    apply CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hformulaElementRows htailElementRows
    rfl
  let stateBoundary := compactUnifiedParserStateBoundaryTable
    tokens.length
      ((inputTokens ++ tailTokens ++ formulaTokens).length + 1) states
  have hstateRows' : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokens.length stateBoundary states := by
    simpa only [tokenTable, width, stateBoundary] using hstateRows
  rcases exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + formulaTokens.length)
        formulaInput from
        ⟨formulaBoundary, hformulaStructure, hformulaElementRows, hformulaSize⟩)
      hstateRows' hstartWell hlocal with
    ⟨parserCoordinates, hparserGraph⟩
  rcases hparserGraph.1.realize with
    ⟨parserInput, hparserInputCount,
      hparserInputLayout, hparserInputRows⟩
  have hparserInputEq : parserInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hparserInputLayout
        (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
          (inputTokens.length + tailTokens.length)
          (inputTokens.length + tailTokens.length + formulaTokens.length)
          formulaInput from
          ⟨formulaBoundary, hformulaStructure,
            hformulaElementRows, hformulaSize⟩)).1.symm
  subst parserInput
  have hinnerConsParser : CompactAdditiveNatListConsRows
      tokenTable width tokens.length parserCoordinates.inputBoundary
        parserCoordinates.inputCount tailBoundary tail.length 22 := by
    have hraw := CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hparserInputRows htailElementRows (show tail = 22 :: formulaInput by rfl)
    simpa only [hparserInputCount] using hraw
  let coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := inputTokens.length + tailTokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      formulaStart := inputTokens.length + tailTokens.length
      formulaFinish := inputTokens.length + tailTokens.length + formulaTokens.length
      parser := parserCoordinates }
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    coordinates, by simpa [input, tail] using hinputLayoutExact,
    hinputRows, htailRows, houterCons, hinnerConsParser, ?_⟩
  simpa only [coordinates] using hparserGraph

theorem exists_compactCertificateNodeInductionPAFailureEndpointGraph
    (formulaInput : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = none) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ coordinates : CompactCertificateNodeInductionPAFailureEndpointCoordinates,
      CompactCertificateNodeInductionPAFailureEndpointGraph
        tokenTable width tokenCount inputStart inputFinish coordinates := by
  rcases
      exists_compactCertificateNodeInductionPAFailureEndpointGraph_with_inputLayout
        formulaInput hformula with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      coordinates, _hinputLayout, hgraph⟩
  exact ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
    coordinates, hgraph⟩

#print axioms compactCertificateNodeInductionPAFailureEndpointGraphDef_spec
#print axioms compactCertificateNodeInductionPAFailureEndpointGraphDef_sigmaZero
#print axioms CompactCertificateNodeInductionPAFailureEndpointGraph.sound
#print axioms exists_compactCertificateNodeInductionPAFailureEndpointGraph

end FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint
