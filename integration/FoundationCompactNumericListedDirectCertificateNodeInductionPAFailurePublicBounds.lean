import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public bounds for failed induction PA certificates

The tag-22 PA branch runs the binder-one formula parser.  A failed parse still
has a complete deterministic no-output trace.  This file constructs the
shared table, installs that trace, and bounds every public and hidden endpoint
coordinate from the original certificate-input weight.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPAFailurePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
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
open FoundationCompactNumericListedDirectParserSyntaxNoOutputExactEndpointPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointPublicBounds
open FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPAFailureBoundedFormula
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactNatListPrimcodable
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec
  FoundationCompactNumericListedDirectTraceCode.compactUnifiedParserStateAdditiveCodec

private theorem compactAdditiveTokenList_length_le_weight
    (tokens : List Nat) :
    tokens.length <= compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

private theorem nat_le_two_pow_of_size_le
    {value bound : Nat} (hsize : Nat.size value <= bound) :
    value <= 2 ^ bound := by
  have hvalue : value < 2 ^ Nat.size value := Nat.lt_size_self value
  have hpower : 2 ^ Nat.size value <= 2 ^ bound :=
    Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) hsize
  exact (Nat.le_of_lt hvalue).trans hpower

private theorem compactFormulaParserNoOutputLocalTrace_weight_le_rootBound
    {binderArity : Nat}
    {tokens : List Nat} {states : CompactFormulaTokenParserDirectTrace}
    (hvalid : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound tokens)
      (compactFormulaParserInitialState binderArity tokens) none states)
    {streamWeight : Nat}
    (hstream : compactAdditiveValueWeight tokens <= streamWeight)
    (hbinder : binderArity <= 1) :
    compactAdditiveValueWeight states <=
      compactNumericRootSyntaxParserTraceWeightBound streamWeight := by
  have hlocal := hvalid.1
  have hrows := compactAdditiveValueWeight_list_le states
    (compactNumericFormulaParserStateWeightBound
      (compactAdditiveValueWeight tokens)
      (binderArity + compactSyntaxRunFuelBound tokens)
      (compactSyntaxRunFuelBound tokens))
    (fun state hstate =>
      compactFormulaParserLocalTrace_member_state_weight_le
        hlocal hstate)
  have hraw :
      compactAdditiveValueWeight states <=
        compactNumericFormulaParserTraceWeightBound
          (compactAdditiveValueWeight tokens) binderArity
            (compactSyntaxRunFuelBound tokens) := by
    unfold compactNumericFormulaParserTraceWeightBound
    rw [hlocal.1] at hrows
    exact hrows
  have hfuel := compactSyntaxRunFuelBound_le_weightBound hstream
  unfold compactNumericRootSyntaxParserTraceWeightBound
  exact hraw.trans
    (compactNumericFormulaParserTraceWeightBound_mono
      hstream hbinder hfuel)

def compactCertificateNodeInductionPAFailureTraceWeightBound
    (inputWeight : Nat) : Nat :=
  compactNumericRootSyntaxParserTraceWeightBound inputWeight

def compactCertificateNodeInductionPAFailureTokenWeightBound
    (inputWeight : Nat) : Nat :=
  3 * inputWeight +
    compactCertificateNodeInductionPAFailureTraceWeightBound inputWeight

def compactCertificateNodeInductionPAFailureWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight

def compactCertificateNodeInductionPAFailureTableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight *
    compactCertificateNodeInductionPAFailureWidthBound inputWeight

def compactCertificateNodeInductionPAFailureListBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight

def compactCertificateNodeInductionPAFailureParserCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
    (compactCertificateNodeInductionPAFailureWidthBound inputWeight)
    (compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight)

def compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAFailureListBoundarySizeBound inputWeight +
    compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight +
    compactCertificateNodeInductionPAFailureParserCoordinateSizeBound
      inputWeight +
    inputWeight + 16

def compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAFailureTableSizeBound inputWeight +
    compactCertificateNodeInductionPAFailureWidthBound inputWeight +
    compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight +
    compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
      inputWeight +
    inputWeight + 8

structure CompactCertificateNodeInductionPAFailurePublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish endpointBound
      bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width : Nat.size width <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

theorem
    exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph_with_publicBounds
    (formulaInput : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = none) :
    let input := 1 :: 22 :: formulaInput
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish endpointBound ∧
        CompactCertificateNodeInductionPAFailurePublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish endpointBound
            (compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
              inputWeight) := by
  have houtput : compactSyntaxParserStateOutput
      ((compactSyntaxParserStep^[compactSyntaxRunFuelBound formulaInput])
        (compactFormulaParserInitialState 1 formulaInput)) = none := by
    simpa [compactFormulaTokenParser, compactFormulaTokenParserRun] using
      hformula
  rcases (compactParserOutput_eq_iff_exists_localTrace
      compactSyntaxParserStep (compactSyntaxRunFuelBound formulaInput)
      (compactFormulaParserInitialState 1 formulaInput) none).mp houtput with
    ⟨states, hvalid⟩
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound formulaInput)
      (formulaInput, [(1, 1, 0)], none) none states := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using hvalid
  have hformulaLocal : CompactParserOutputLocalTraceValid
      compactSyntaxParserStep (compactSyntaxRunFuelBound formulaInput)
      (compactFormulaParserInitialState 1 formulaInput) none states := by
    simpa [compactFormulaParserInitialState, compactFormulaTask] using hlocal
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 1, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  let tail := 22 :: formulaInput
  let input := 1 :: tail
  let inputWeight := compactAdditiveValueWeight input
  have htailWeight :
      compactAdditiveValueWeight tail <= inputWeight :=
    compactAdditiveValueWeight_suffix_le
      (show tail <:+ input from by simp [input])
  have hformulaSuffix : formulaInput <:+ input :=
    ⟨[1, 22], by simp [input, tail]⟩
  have hformulaWeight :
      compactAdditiveValueWeight formulaInput <= inputWeight :=
    compactAdditiveValueWeight_suffix_le hformulaSuffix
  have hstatesWeight :
      compactAdditiveValueWeight states <=
        compactCertificateNodeInductionPAFailureTraceWeightBound
          inputWeight := by
    exact compactFormulaParserNoOutputLocalTrace_weight_le_rootBound
      hformulaLocal hformulaWeight (by omega)
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let formulaTokens := compactAdditiveEncode formulaInput
  let stateTokens := compactAdditiveEncode states
  let tokens := inputTokens ++ tailTokens ++ formulaTokens ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodeInductionPAFailureTokenWeightBound
          inputWeight := by
    simp only [tokens, compactAdditiveTokenWeight_append]
    change compactAdditiveValueWeight input +
        compactAdditiveValueWeight tail +
        compactAdditiveValueWeight formulaInput +
        compactAdditiveValueWeight states <= _
    unfold compactCertificateNodeInductionPAFailureTraceWeightBound at hstatesWeight
    unfold compactCertificateNodeInductionPAFailureTokenWeightBound
      compactCertificateNodeInductionPAFailureTraceWeightBound
    calc
      _ <= inputWeight + inputWeight + inputWeight +
          compactNumericRootSyntaxParserTraceWeightBound inputWeight :=
        Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add (Nat.le_refl inputWeight) htailWeight)
            hformulaWeight)
          hstatesWeight
      _ = 3 * inputWeight +
          compactNumericRootSyntaxParserTraceWeightBound inputWeight := by
        omega
  have htokenCount :
      tokens.length <=
        compactCertificateNodeInductionPAFailureTokenWeightBound
          inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <=
        compactCertificateNodeInductionPAFailureWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodeInductionPAFailureWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodeInductionPAFailureTableSizeBound
          inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
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
  have hstateTokenEq :
      (inputTokens ++ tailTokens ++ formulaTokens) ++
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
    ⟨_hstateStructure, hstateRows, hstateSize⟩
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
  let stateBoundary := compactUnifiedParserStateBoundaryTable
    tokens.length
      ((inputTokens ++ tailTokens ++ formulaTokens).length + 1) states
  have hstateRows' : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokens.length stateBoundary states := by
    simpa only [tokenTable, width, stateBoundary] using hstateRows
  have hstateBoundarySize :
      Nat.size stateBoundary <= (states.length + 1) * tokens.length := by
    simpa only [stateBoundary] using hstateSize
  rcases
      exists_compactParserSyntaxNoOutputExactEndpointGraph_of_rows_with_publicBounds
        (show CompactAdditiveNatListDirectLayout
          tokenTable width tokens.length
            (inputTokens.length + tailTokens.length)
            (inputTokens.length + tailTokens.length + formulaTokens.length)
            formulaInput from
          ⟨formulaBoundary, hformulaStructure,
            hformulaElementRows, hformulaSize⟩)
        hstateRows' hstateBoundarySize hstartWell hlocal with
    ⟨parserCoordinates, hparserGraph, hparserPublic, _hstateBoundaryEq⟩
  rcases hparserGraph.1.realize with
    ⟨parserInput, hparserInputCount,
      hparserInputLayout, hparserInputRows⟩
  have hparserInputEq : parserInput = formulaInput :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hparserInputLayout
        (show CompactAdditiveNatListDirectLayout
          tokenTable width tokens.length
            (inputTokens.length + tailTokens.length)
            (inputTokens.length + tailTokens.length + formulaTokens.length)
            formulaInput from
          ⟨formulaBoundary, hformulaStructure,
            hformulaElementRows, hformulaSize⟩)).1.symm
  subst parserInput
  have hinnerCons : CompactAdditiveNatListConsRows
      tokenTable width tokens.length parserCoordinates.inputBoundary
        parserCoordinates.inputCount tailBoundary tail.length 22 := by
    have hraw := CompactAdditiveStructuredListElementRowLayouts.natConsRows
      hparserInputRows htailElementRows
        (show tail = 22 :: formulaInput by rfl)
    simpa only [hparserInputCount] using hraw
  let coordinates :
      CompactCertificateNodeInductionPAFailureEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := inputTokens.length + tailTokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      formulaStart := inputTokens.length + tailTokens.length
      formulaFinish :=
        inputTokens.length + tailTokens.length + formulaTokens.length
      parser := parserCoordinates }
  have hgraph : CompactCertificateNodeInductionPAFailureEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length coordinates := by
    unfold CompactCertificateNodeInductionPAFailureEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputRows, htailRows, houterCons, hinnerCons, hparserGraph⟩
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le tail).trans htailWeight
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodeInductionPAFailureListBoundarySizeBound
          inputWeight :=
    hinputSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodeInductionPAFailureListBoundarySizeBound
          inputWeight :=
    htailSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  have hparserCoordinateBound :
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound
          width tokens.length <=
        compactCertificateNodeInductionPAFailureParserCoordinateSizeBound
          inputWeight := by
    dsimp only [
      compactCertificateNodeInductionPAFailureParserCoordinateSizeBound,
      compactParserSyntaxNoOutputExactEndpointPublicCoordinateSizeBound,
      compactParserSyntaxExactEndpointPublicCoordinateSizeBound]
    exact compactSequentFormulaStepPublicCoordinateSizeBound_mono
      hwidth htokenCount
  let hiddenBound :=
    compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
      inputWeight
  have hboundaryToHidden :
      compactCertificateNodeInductionPAFailureListBoundarySizeBound
          inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
    omega
  have htokenToHidden :
      compactCertificateNodeInductionPAFailureTokenWeightBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
    omega
  have hparserToHidden :
      compactCertificateNodeInductionPAFailureParserCoordinateSizeBound
          inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
    omega
  have hinputToHidden : inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
    omega
  have hinputBoundaryHidden :=
    hinputBoundaryPublic.trans hboundaryToHidden
  have htailBoundaryHidden :=
    htailBoundaryPublic.trans hboundaryToHidden
  have hboundarySizeHidden
      {boundary : Nat} (hboundary : Nat.size boundary <= hiddenBound) :
      Nat.size (Nat.size boundary) <= hiddenBound :=
    (natSize_le_of_le (Nat.le_refl (Nat.size boundary))).trans hboundary
  have hinputCountHidden :
      Nat.size input.length <= hiddenBound :=
    (natSize_le_of_le hinputLength).trans hinputToHidden
  have htailCountHidden :
      Nat.size tail.length <= hiddenBound :=
    (natSize_le_of_le htailLength).trans hinputToHidden
  have hinputFinishValue :
      inputTokens.length <=
        compactCertificateNodeInductionPAFailureTokenWeightBound
          inputWeight :=
    (Nat.le_add_right inputTokens.length
      (tailTokens.length + formulaTokens.length + stateTokens.length)).trans
      (by simpa only [tokens, List.length_append, Nat.add_assoc]
        using htokenCount)
  have htailFinishValue :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodeInductionPAFailureTokenWeightBound
          inputWeight := by
    have hraw :
        inputTokens.length + tailTokens.length <= tokens.length := by
      simp [tokens]
    exact hraw.trans htokenCount
  have hformulaFinishValue :
      inputTokens.length + tailTokens.length + formulaTokens.length <=
        compactCertificateNodeInductionPAFailureTokenWeightBound
          inputWeight := by
    have hraw :
        inputTokens.length + tailTokens.length + formulaTokens.length <=
          tokens.length := by
      dsimp only [tokens]
      simp only [List.length_append]
      omega
    exact hraw.trans htokenCount
  have hinputFinishHidden :
      Nat.size inputTokens.length <= hiddenBound :=
    (natSize_le_of_le hinputFinishValue).trans htokenToHidden
  have htailFinishHidden :
      Nat.size (inputTokens.length + tailTokens.length) <= hiddenBound :=
    (natSize_le_of_le htailFinishValue).trans htokenToHidden
  have hformulaFinishHidden :
      Nat.size
          (inputTokens.length + tailTokens.length + formulaTokens.length) <=
        hiddenBound :=
    (natSize_le_of_le hformulaFinishValue).trans htokenToHidden
  have hparserSize
      {value : Nat}
      (hvalue :
        value ∈
          compactParserSyntaxNoOutputExactEndpointCoordinateValues
            parserCoordinates) :
      Nat.size value <= hiddenBound :=
    (hparserPublic.value_size_le value hvalue).trans
      (hparserCoordinateBound.trans hparserToHidden)
  let endpointBound := 2 ^ hiddenBound
  have hbounded :
      CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
        tokenTable width tokens.length 0 inputTokens.length endpointBound := by
    unfold CompactCertificateNodeInductionPAFailureEndpointBoundedGraph
    refine
      ⟨inputBoundary,
          nat_le_two_pow_of_size_le hinputBoundaryHidden,
        input.length,
          nat_le_two_pow_of_size_le hinputCountHidden,
        Nat.size inputBoundary,
          nat_le_two_pow_of_size_le
            (hboundarySizeHidden hinputBoundaryHidden),
        inputTokens.length,
          nat_le_two_pow_of_size_le hinputFinishHidden,
        inputTokens.length + tailTokens.length,
          nat_le_two_pow_of_size_le htailFinishHidden,
        tailBoundary,
          nat_le_two_pow_of_size_le htailBoundaryHidden,
        tail.length,
          nat_le_two_pow_of_size_le htailCountHidden,
        Nat.size tailBoundary,
          nat_le_two_pow_of_size_le
            (hboundarySizeHidden htailBoundaryHidden),
        inputTokens.length + tailTokens.length,
          nat_le_two_pow_of_size_le htailFinishHidden,
        inputTokens.length + tailTokens.length + formulaTokens.length,
          nat_le_two_pow_of_size_le hformulaFinishHidden,
        parserCoordinates.inputBoundary,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        parserCoordinates.inputCount,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        parserCoordinates.inputBoundarySize,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        parserCoordinates.stateBoundary,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        parserCoordinates.stateCount,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        parserCoordinates.tableWidth,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        parserCoordinates.valueBound,
          nat_le_two_pow_of_size_le
            (hparserSize (by
              simp [compactParserSyntaxNoOutputExactEndpointCoordinateValues])),
        by simpa only [coordinates,
          compactCertificateNodeInductionPAFailureEndpointCoordinatesOfValues]
            using hgraph⟩
  let publicBound :=
    compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
      inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound :=
    htable.trans (by
      unfold publicBound
        compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound :=
    (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound :=
    (natSize_le_of_le htokenCount).trans (by
      unfold publicBound
        compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
      omega)
  have hinputFinishPublic :
      Nat.size inputTokens.length <= publicBound :=
    hinputFinishHidden.trans (by
      unfold publicBound hiddenBound
        compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
        compactCertificateNodeInductionPAFailureHiddenCoordinateSizeBound
      omega)
  have hendpointPublic : Nat.size endpointBound <= publicBound := by
    rw [Nat.size_pow]
    dsimp only [publicBound, hiddenBound]
    unfold
      compactCertificateNodeInductionPAFailurePublicCoordinateSizeBound
    omega
  refine ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
    endpointBound, by simpa [input, tail] using hinputLayoutExact,
    hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      endpointBound := hendpointPublic }

#print axioms
  exists_compactCertificateNodeInductionPAFailureEndpointBoundedGraph_with_publicBounds

end FoundationCompactNumericListedDirectCertificateNodeInductionPAFailurePublicBounds
