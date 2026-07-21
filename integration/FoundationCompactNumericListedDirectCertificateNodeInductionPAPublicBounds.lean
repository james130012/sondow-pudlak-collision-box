import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
import integration.FoundationCompactNumericListedDirectParserSyntaxTraceBounds
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public quantitative bounds for induction PA-axiom certificate parsing

The tag-22 branch carries a complete binder-one formula-parser trace.  This file
constructs the shared canonical table and bounds its parser width, state table,
all twenty-one existential endpoint coordinates, and all thirteen public
coordinates from the additive input weight alone.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
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
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectParserStateListLayout
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactEndpointCompleteness
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxTraceBounds
open FoundationCompactNumericListedDirectTraceBounds

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

def compactCertificateNodeInductionPAFuelBound
    (inputWeight : Nat) : Nat :=
  compactNumericCertificateParserFuelWeightBound inputWeight

def compactCertificateNodeInductionPATraceWeightBound
    (inputWeight : Nat) : Nat :=
  compactNumericRootSyntaxParserTraceWeightBound inputWeight

def compactCertificateNodeInductionPATokenWeightBound
    (inputWeight : Nat) : Nat :=
  5 * inputWeight +
    compactCertificateNodeInductionPATraceWeightBound inputWeight

def compactCertificateNodeInductionPAWidthBound
    (inputWeight : Nat) : Nat :=
  2 * compactCertificateNodeInductionPATokenWeightBound inputWeight

def compactCertificateNodeInductionPATableSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPATokenWeightBound inputWeight *
    compactCertificateNodeInductionPAWidthBound inputWeight

def compactCertificateNodeInductionPAListBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (inputWeight + 1) *
    compactCertificateNodeInductionPATokenWeightBound inputWeight

def compactCertificateNodeInductionPAStateBoundarySizeBound
    (inputWeight : Nat) : Nat :=
  (compactCertificateNodeInductionPAFuelBound inputWeight + 2) *
    compactCertificateNodeInductionPATokenWeightBound inputWeight

def compactCertificateNodeInductionPAParserStepWidthBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAWidthBound inputWeight +
    (compactCertificateNodeInductionPATokenWeightBound inputWeight + 1) *
      compactCertificateNodeInductionPATokenWeightBound inputWeight + 8

def compactCertificateNodeInductionPAParserTableWidthBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAFuelBound inputWeight *
      compactParserSyntaxAdjacentStepWitnessColumnCount *
      compactCertificateNodeInductionPAParserStepWidthBound inputWeight +
    (compactCertificateNodeInductionPATokenWeightBound inputWeight + 1) *
      compactCertificateNodeInductionPATokenWeightBound inputWeight +
    23 * compactCertificateNodeInductionPAParserStepWidthBound inputWeight

/-- A bit-size budget for all twenty-one existential endpoint coordinates. -/
def compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAListBoundarySizeBound inputWeight +
    compactCertificateNodeInductionPAStateBoundarySizeBound inputWeight +
    compactCertificateNodeInductionPATokenWeightBound inputWeight +
    inputWeight +
    compactCertificateNodeInductionPAFuelBound inputWeight +
    compactCertificateNodeInductionPAParserTableWidthBound inputWeight + 32

def compactCertificateNodeInductionPAEndpointSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPAHiddenCoordinateSizeBound inputWeight + 1

/-- One common bit-size budget for all thirteen public endpoint coordinates. -/
def compactCertificateNodeInductionPAPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactCertificateNodeInductionPATableSizeBound inputWeight +
    compactCertificateNodeInductionPAWidthBound inputWeight +
    compactCertificateNodeInductionPATokenWeightBound inputWeight +
    compactCertificateNodeInductionPAEndpointSizeBound inputWeight +
    inputWeight + 24

theorem compactCertificateNodeInductionPAPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactCertificateNodeInductionPAPublicCoordinateSizeBound left <=
      compactCertificateNodeInductionPAPublicCoordinateSizeBound right := by
  have hfuel := compactNumericCertificateParserFuelWeightBound_mono h
  have htrace := compactNumericRootSyntaxParserTraceWeightBound_mono h
  have htoken :
      compactCertificateNodeInductionPATokenWeightBound left <=
        compactCertificateNodeInductionPATokenWeightBound right := by
    unfold compactCertificateNodeInductionPATokenWeightBound
      compactCertificateNodeInductionPATraceWeightBound
    omega
  have hwidth :
      compactCertificateNodeInductionPAWidthBound left <=
        compactCertificateNodeInductionPAWidthBound right := by
    unfold compactCertificateNodeInductionPAWidthBound
    omega
  have htable := Nat.mul_le_mul htoken hwidth
  have hlist := Nat.mul_le_mul (Nat.add_le_add_right h 1) htoken
  have hstate := Nat.mul_le_mul (Nat.add_le_add_right hfuel 2) htoken
  have htokenArea := Nat.mul_le_mul
    (Nat.add_le_add_right htoken 1) htoken
  have hparserStep :
      compactCertificateNodeInductionPAParserStepWidthBound left <=
        compactCertificateNodeInductionPAParserStepWidthBound right := by
    unfold compactCertificateNodeInductionPAParserStepWidthBound
    omega
  have hfuelColumns := Nat.mul_le_mul_right
    compactParserSyntaxAdjacentStepWitnessColumnCount hfuel
  have hparserRows := Nat.mul_le_mul hfuelColumns hparserStep
  have hparserTail := Nat.mul_le_mul_left 23 hparserStep
  have hparserTable :
      compactCertificateNodeInductionPAParserTableWidthBound left <=
        compactCertificateNodeInductionPAParserTableWidthBound right := by
    unfold compactCertificateNodeInductionPAParserTableWidthBound
      compactCertificateNodeInductionPAFuelBound
    omega
  unfold compactCertificateNodeInductionPAPublicCoordinateSizeBound
    compactCertificateNodeInductionPAEndpointSizeBound
    compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    compactCertificateNodeInductionPAParserTableWidthBound
    compactCertificateNodeInductionPAParserStepWidthBound
    compactCertificateNodeInductionPAStateBoundarySizeBound
    compactCertificateNodeInductionPAListBoundarySizeBound
    compactCertificateNodeInductionPATableSizeBound
    compactCertificateNodeInductionPAWidthBound
    compactCertificateNodeInductionPATokenWeightBound
    compactCertificateNodeInductionPATraceWeightBound
    compactCertificateNodeInductionPAFuelBound at *
  omega

structure CompactCertificateNodeInductionPAPublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag endpointBound bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  axiomStart : Nat.size axiomStart <= bound
  axiomFinish : Nat.size axiomFinish <= bound
  formulaStart : Nat.size formulaStart <= bound
  formulaFinish : Nat.size formulaFinish <= bound
  suffixStart : Nat.size suffixStart <= bound
  suffixFinish : Nat.size suffixFinish <= bound
  certificateTag : Nat.size certificateTag <= bound
  endpointBound : Nat.size endpointBound <= bound

set_option maxHeartbeats 1500000 in
theorem
    exists_compactCertificateNodeInductionPAEndpointBoundedGraph_with_publicBounds
    (formulaInput suffix : List Nat)
    (hformula : compactFormulaTokenParser 1 formulaInput = some suffix) :
    let input := 1 :: 22 :: formulaInput
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactCertificateNodeInductionPAEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish 1 endpointBound ∧
        CompactCertificateNodeInductionPAPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            axiomStart axiomFinish formulaStart formulaFinish
            suffixStart suffixFinish 1 endpointBound
            (compactCertificateNodeInductionPAPublicCoordinateSizeBound
              inputWeight) := by
  rcases (compactFormulaTokenParser_success_iff
      1 formulaInput suffix).mp hformula with
    ⟨formula, hformulaSplit⟩
  rcases (compactFormulaTokenParser_eq_some_iff_exists_directTrace
      1 formulaInput suffix).mp hformula with
    ⟨states, hformulaValid⟩
  let formulaTokens := compactArithmeticFormulaTokens formula
  let axiomTokens := 22 :: formulaTokens
  let tail := 22 :: formulaInput
  let input := 1 :: tail
  let inputWeight := compactAdditiveValueWeight input
  have htailSplit : tail = axiomTokens ++ suffix := by
    simp [tail, axiomTokens, formulaTokens, hformulaSplit]
  have htailWeight :
      compactAdditiveValueWeight tail <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show tail <:+ input from by simp [input])
  have hformulaInputWeight :
      compactAdditiveValueWeight formulaInput <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show formulaInput <:+ input from by
        refine ⟨[1, 22], ?_⟩
        simp [input, tail])
  have hsuffixWeight :
      compactAdditiveValueWeight suffix <= inputWeight := by
    exact (compactAdditiveValueWeight_suffix_le
      (show suffix <:+ formulaInput from
        ⟨formulaTokens, hformulaSplit.symm⟩)).trans
        hformulaInputWeight
  have haxiomWeight :
      compactAdditiveValueWeight axiomTokens <= inputWeight := by
    exact compactAdditiveValueWeight_infix_le
      (show axiomTokens <:+: input from by
        refine ⟨[1], suffix, ?_⟩
        simp [input, htailSplit])
  have hstatesWeight :
      compactAdditiveValueWeight states <=
        compactCertificateNodeInductionPATraceWeightBound inputWeight := by
    exact compactFormulaTokenParserDirectTraceValid_weight_le_rootBound
      hformulaValid hformulaInputWeight (by omega)
  let inputTokens := compactAdditiveEncode input
  let tailTokens := compactAdditiveEncode tail
  let axiomEncoded := compactAdditiveEncode axiomTokens
  let formulaEncoded := compactAdditiveEncode formulaInput
  let suffixEncoded := compactAdditiveEncode suffix
  let stateTokens := compactAdditiveEncode states
  let tokens := inputTokens ++ tailTokens ++ axiomEncoded ++
    formulaEncoded ++ suffixEncoded ++ stateTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactCertificateNodeInductionPATokenWeightBound inputWeight := by
    calc
      compactAdditiveTokenWeight tokens =
          compactAdditiveValueWeight input +
            compactAdditiveValueWeight tail +
            compactAdditiveValueWeight axiomTokens +
            compactAdditiveValueWeight formulaInput +
            compactAdditiveValueWeight suffix +
            compactAdditiveValueWeight states := by
        simp [tokens, inputTokens, tailTokens, axiomEncoded, formulaEncoded,
          suffixEncoded, stateTokens, compactAdditiveValueWeight,
          Nat.add_assoc]
      _ <= compactCertificateNodeInductionPATokenWeightBound inputWeight := by
        unfold compactCertificateNodeInductionPATokenWeightBound
        omega
  have htokenCount :
      tokens.length <=
        compactCertificateNodeInductionPATokenWeightBound inputWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <= compactCertificateNodeInductionPAWidthBound inputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactCertificateNodeInductionPAWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactCertificateNodeInductionPATableSizeBound inputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (Nat.mul_le_mul htokenCount hwidth)
  have hinputRaw := compactAdditiveNatListDirectLayout_canonical
    [] input (tailTokens ++ axiomEncoded ++ formulaEncoded ++
      suffixEncoded ++ stateTokens)
  dsimp only at hinputRaw
  have hinputTokenEq : [] ++ compactAdditiveEncode input ++
      (tailTokens ++ axiomEncoded ++ formulaEncoded ++
        suffixEncoded ++ stateTokens) = tokens := by
    simp [inputTokens, tokens, List.append_assoc]
  rw [hinputTokenEq] at hinputRaw
  have htailRaw := compactAdditiveNatListDirectLayout_canonical
    inputTokens tail (axiomEncoded ++ formulaEncoded ++
      suffixEncoded ++ stateTokens)
  dsimp only at htailRaw
  have htailTokenEq : inputTokens ++ compactAdditiveEncode tail ++
      (axiomEncoded ++ formulaEncoded ++ suffixEncoded ++ stateTokens) =
        tokens := by
    simp [tailTokens, tokens, List.append_assoc]
  rw [htailTokenEq] at htailRaw
  have haxiomRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens) axiomTokens
      (formulaEncoded ++ suffixEncoded ++ stateTokens)
  dsimp only at haxiomRaw
  have haxiomTokenEq : (inputTokens ++ tailTokens) ++
      compactAdditiveEncode axiomTokens ++
      (formulaEncoded ++ suffixEncoded ++ stateTokens) = tokens := by
    simp [axiomEncoded, tokens, List.append_assoc]
  rw [haxiomTokenEq] at haxiomRaw
  have hformulaRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded) formulaInput
      (suffixEncoded ++ stateTokens)
  dsimp only at hformulaRaw
  have hformulaTokenEq :
      (inputTokens ++ tailTokens ++ axiomEncoded) ++
        compactAdditiveEncode formulaInput ++ (suffixEncoded ++ stateTokens) =
          tokens := by
    simp [formulaEncoded, tokens, List.append_assoc]
  rw [hformulaTokenEq] at hformulaRaw
  have hsuffixRaw := compactAdditiveNatListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded)
      suffix stateTokens
  dsimp only at hsuffixRaw
  have hsuffixTokenEq :
      (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded) ++
        compactAdditiveEncode suffix ++ stateTokens = tokens := by
    simp [suffixEncoded, tokens, List.append_assoc]
  rw [hsuffixTokenEq] at hsuffixRaw
  have hstatesRaw := compactUnifiedParserStateListDirectLayout_canonical
    (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded ++
      suffixEncoded) states []
  dsimp only at hstatesRaw
  have hstateTokenEq :
      (inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded ++
        suffixEncoded) ++ compactAdditiveEncode states ++ [] = tokens := by
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
  have haxiomLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens := by
    simpa only [tokenTable, width, axiomEncoded,
      List.length_append] using haxiomRaw
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) formulaInput := by
    simpa only [tokenTable, width, formulaEncoded,
      List.length_append] using hformulaRaw
  have hsuffixLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) suffix := by
    simpa only [tokenTable, width, suffixEncoded,
      List.length_append] using hsuffixRaw
  have hinputLayoutExact := hinputLayout
  rcases hinputLayout with
    ⟨inputBoundary, hinputStructure, hinputElementRows, hinputSize⟩
  rcases htailLayout with
    ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩
  rcases haxiomLayout with
    ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomSize⟩
  rcases hformulaLayout with
    ⟨formulaBoundary, hformulaStructure, hformulaElementRows, hformulaSize⟩
  rcases hsuffixLayout with
    ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩
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
  have haxiomRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length) axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomBoundary (Nat.size axiomBoundary) :=
    ⟨haxiomStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        haxiomElementRows,
      rfl, haxiomSize⟩
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
  have hlocal : CompactParserOutputLocalTraceValid compactSyntaxParserStep
      (compactSyntaxRunFuelBound formulaInput)
      (formulaInput, [(1, 1, 0)], none) (some suffix) states := by
    simpa [CompactFormulaTokenParserDirectTraceValid,
      compactFormulaParserInitialState, compactFormulaTask] using hformulaValid
  have hstartWell : CompactSyntaxTaskStackFieldsWellFormed
      [(1, 1, 0)] := by
    simp [CompactSyntaxTaskStackFieldsWellFormed,
      CompactSyntaxTaskFieldsWellFormed]
  let stateBoundary := compactUnifiedParserStateBoundaryTable
    tokens.length
      ((inputTokens ++ tailTokens ++ axiomEncoded ++ formulaEncoded ++
        suffixEncoded).length + 1) states
  have hstateRows' : CompactUnifiedParserStateListRowLayouts
      tokenTable width tokens.length stateBoundary states := by
    simpa only [tokenTable, width, stateBoundary] using hstateRows
  rcases
      localTrace_exists_compactParserSyntaxExactBoundedGraph_with_publicWidth
        hstateRows' hformulaElementRows hsuffixElementRows hstartWell hlocal with
    ⟨tableWidth, htableWidthPublic, hexact⟩
  have hformulaWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        formulaInput.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) formulaBoundary (Nat.size formulaBoundary) :=
    ⟨hformulaStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hformulaElementRows,
      rfl, hformulaSize⟩
  have hsuffixWitness : CompactAdditiveNatListWitnessRows
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) suffix.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length)
        suffixBoundary (Nat.size suffixBoundary) :=
    ⟨hsuffixStructure,
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hsuffixElementRows,
      rfl, hsuffixSize⟩
  let parserCoordinates : CompactParserSyntaxExactEndpointCoordinates :=
    { inputBoundary := formulaBoundary
      inputCount := formulaInput.length
      inputBoundarySize := Nat.size formulaBoundary
      expectedBoundary := suffixBoundary
      expectedCount := suffix.length
      expectedBoundarySize := Nat.size suffixBoundary
      stateBoundary := stateBoundary
      stateCount := states.length
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  have hparserGraph : CompactParserSyntaxExactEndpointGraph
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length)
        1 1 0 parserCoordinates := by
    unfold CompactParserSyntaxExactEndpointGraph
    dsimp only [parserCoordinates]
    exact ⟨hformulaWitness, hsuffixWitness, hexact⟩
  have happend : CompactAdditiveNatListAppendSlices
      tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) suffix.length
        inputTokens.length (inputTokens.length + tailTokens.length)
        tail.length := by
    apply (compactAdditiveNatListAppendSlices_iff_append
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        axiomTokens from
        ⟨axiomBoundary, haxiomStructure, haxiomElementRows, haxiomSize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) suffix from
        ⟨suffixBoundary, hsuffixStructure, hsuffixElementRows, hsuffixSize⟩)
      (show CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        inputTokens.length (inputTokens.length + tailTokens.length) tail from
        ⟨tailBoundary, htailStructure, htailElementRows, htailSize⟩)).2
    exact htailSplit
  let coordinates : CompactCertificateNodeInductionPAEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := Nat.size inputBoundary
      tailStart := inputTokens.length
      tailFinish := inputTokens.length + tailTokens.length
      tailBoundary := tailBoundary
      tailCount := tail.length
      tailBoundarySize := Nat.size tailBoundary
      axiomBoundary := axiomBoundary
      axiomCount := axiomTokens.length
      axiomBoundarySize := Nat.size axiomBoundary
      parser := parserCoordinates }
  have hgraph : CompactCertificateNodeInductionPAEndpointGraph
      tokenTable width tokens.length 0 inputTokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length)
        1 coordinates := by
    unfold CompactCertificateNodeInductionPAEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputRows, htailRows, haxiomRows, rfl,
      houterCons, hinnerCons, hparserGraph, by
        simpa only [parserCoordinates] using happend⟩
  have hfuel :
      compactSyntaxRunFuelBound formulaInput <=
        compactCertificateNodeInductionPAFuelBound inputWeight := by
    exact compactSyntaxRunFuelBound_le_weightBound hformulaInputWeight
  have hstepWidth :
      compactParserSyntaxAdjacentStepPublicWidth width tokens.length <=
        compactCertificateNodeInductionPAParserStepWidthBound inputWeight := by
    have harea :
        (tokens.length + 1) * tokens.length <=
          (compactCertificateNodeInductionPATokenWeightBound inputWeight + 1) *
            compactCertificateNodeInductionPATokenWeightBound inputWeight :=
      Nat.mul_le_mul (Nat.add_le_add_right htokenCount 1) htokenCount
    unfold compactParserSyntaxAdjacentStepPublicWidth
      compactFormulaTransformAdjacentStepPublicWidth
      compactBinaryNatStreamStepWitnessPublicWidth
      compactCertificateNodeInductionPAParserStepWidthBound
    omega
  have hcanonicalWidth :
      compactParserSyntaxCanonicalTableWidthBound width tokens.length
          (compactSyntaxRunFuelBound formulaInput) <=
        compactCertificateNodeInductionPAParserTableWidthBound inputWeight := by
    have hrow :
        compactSyntaxRunFuelBound formulaInput *
              compactParserSyntaxAdjacentStepWitnessColumnCount *
              compactParserSyntaxAdjacentStepPublicWidth width tokens.length <=
          compactCertificateNodeInductionPAFuelBound inputWeight *
              compactParserSyntaxAdjacentStepWitnessColumnCount *
              compactCertificateNodeInductionPAParserStepWidthBound
                inputWeight :=
      Nat.mul_le_mul
        (Nat.mul_le_mul hfuel
          (Nat.le_refl compactParserSyntaxAdjacentStepWitnessColumnCount))
        hstepWidth
    have harea :
        (tokens.length + 1) * tokens.length <=
          (compactCertificateNodeInductionPATokenWeightBound inputWeight + 1) *
            compactCertificateNodeInductionPATokenWeightBound inputWeight :=
      Nat.mul_le_mul (Nat.add_le_add_right htokenCount 1) htokenCount
    have hendpoint := Nat.mul_le_mul_left 23 hstepWidth
    unfold compactParserSyntaxCanonicalTableWidthBound
      compactCertificateNodeInductionPAParserTableWidthBound
    omega
  have htableWidth :
      tableWidth <=
        compactCertificateNodeInductionPAParserTableWidthBound inputWeight :=
    htableWidthPublic.trans hcanonicalWidth
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have htailLength : tail.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le tail).trans htailWeight
  have haxiomLength : axiomTokens.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le axiomTokens).trans haxiomWeight
  have hformulaLength : formulaInput.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le formulaInput).trans
      hformulaInputWeight
  have hsuffixLength : suffix.length <= inputWeight :=
    (compactAdditiveValueWeight_natList_length_le suffix).trans hsuffixWeight
  have hstatesLength :
      states.length <=
        compactCertificateNodeInductionPAFuelBound inputWeight + 1 := by
    calc
      states.length = compactSyntaxRunFuelBound formulaInput + 1 := hlocal.1.1
      _ <= compactCertificateNodeInductionPAFuelBound inputWeight + 1 :=
        Nat.add_le_add_right hfuel 1
  have hinputBoundaryPublic :
      Nat.size inputBoundary <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight :=
    hinputSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hinputLength 1) htokenCount)
  have htailBoundaryPublic :
      Nat.size tailBoundary <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight :=
    htailSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right htailLength 1) htokenCount)
  have haxiomBoundaryPublic :
      Nat.size axiomBoundary <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight :=
    haxiomSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right haxiomLength 1) htokenCount)
  have hformulaBoundaryPublic :
      Nat.size formulaBoundary <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight :=
    hformulaSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hformulaLength 1) htokenCount)
  have hsuffixBoundaryPublic :
      Nat.size suffixBoundary <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight :=
    hsuffixSize.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hsuffixLength 1) htokenCount)
  have hstateBoundaryPublic :
      Nat.size stateBoundary <=
        compactCertificateNodeInductionPAStateBoundarySizeBound inputWeight := by
    have hraw : Nat.size stateBoundary <=
        (states.length + 1) * tokens.length := by
      simpa only [stateBoundary] using hstateSize
    exact hraw.trans
      (Nat.mul_le_mul
        (Nat.add_le_add_right hstatesLength 1) htokenCount)
  have hinputCountSize : Nat.size input.length <= inputWeight :=
    natSize_le_of_le hinputLength
  have htailCountSize : Nat.size tail.length <= inputWeight :=
    natSize_le_of_le htailLength
  have haxiomCountSize : Nat.size axiomTokens.length <= inputWeight :=
    natSize_le_of_le haxiomLength
  have hformulaCountSize : Nat.size formulaInput.length <= inputWeight :=
    natSize_le_of_le hformulaLength
  have hsuffixCountSize : Nat.size suffix.length <= inputWeight :=
    natSize_le_of_le hsuffixLength
  have hstateCountSize :
      Nat.size states.length <=
        compactCertificateNodeInductionPAFuelBound inputWeight + 1 :=
    natSize_le_of_le hstatesLength
  have hboundarySizeSize
      {boundary : Nat}
      (hboundary : Nat.size boundary <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight) :
      Nat.size (Nat.size boundary) <=
        compactCertificateNodeInductionPAListBoundarySizeBound inputWeight :=
    (natSize_le_of_le (Nat.le_refl (Nat.size boundary))).trans hboundary
  have hinputBoundarySizeSize := hboundarySizeSize hinputBoundaryPublic
  have htailBoundarySizeSize := hboundarySizeSize htailBoundaryPublic
  have haxiomBoundarySizeSize := hboundarySizeSize haxiomBoundaryPublic
  have hformulaBoundarySizeSize := hboundarySizeSize hformulaBoundaryPublic
  have hsuffixBoundarySizeSize := hboundarySizeSize hsuffixBoundaryPublic
  have htailStartLength :
      inputTokens.length <=
        compactCertificateNodeInductionPATokenWeightBound inputWeight := by
    have hpartial : inputTokens.length <= tokens.length := by
      simp [tokens]
    exact hpartial.trans htokenCount
  have htailFinishLength :
      inputTokens.length + tailTokens.length <=
        compactCertificateNodeInductionPATokenWeightBound inputWeight := by
    have hpartial :
        inputTokens.length + tailTokens.length <= tokens.length := by
      simp only [tokens, List.length_append]
      omega
    exact hpartial.trans htokenCount
  have htailStartSize :=
    natSize_le_of_le htailStartLength
  have htailFinishSize :=
    natSize_le_of_le htailFinishLength
  have htableWidthSize :
      Nat.size tableWidth <=
        compactCertificateNodeInductionPAParserTableWidthBound inputWeight :=
    natSize_le_of_le htableWidth
  have hvalueBoundSize :
      Nat.size (2 ^ tableWidth) <=
        compactCertificateNodeInductionPAParserTableWidthBound inputWeight + 1 := by
    rw [Nat.size_pow]
    omega
  let hiddenBound :=
    compactCertificateNodeInductionPAHiddenCoordinateSizeBound inputWeight
  have hlistBoundaryToHidden :
      compactCertificateNodeInductionPAListBoundarySizeBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    omega
  have hstateBoundaryToHidden :
      compactCertificateNodeInductionPAStateBoundarySizeBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    omega
  have htokenToHidden :
      compactCertificateNodeInductionPATokenWeightBound inputWeight <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    omega
  have hinputToHidden : inputWeight <= hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    omega
  have hfuelToHidden :
      compactCertificateNodeInductionPAFuelBound inputWeight + 1 <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    omega
  have htableToHidden :
      compactCertificateNodeInductionPAParserTableWidthBound inputWeight + 1 <=
        hiddenBound := by
    unfold hiddenBound
      compactCertificateNodeInductionPAHiddenCoordinateSizeBound
    omega
  have htableBaseToHidden :
      compactCertificateNodeInductionPAParserTableWidthBound inputWeight <=
        hiddenBound :=
    (Nat.le_add_right
      (compactCertificateNodeInductionPAParserTableWidthBound inputWeight)
      1).trans htableToHidden
  let endpointBound := 2 ^ hiddenBound
  have hbounded : CompactCertificateNodeInductionPAEndpointBoundedGraph
      tokenTable width tokens.length 0 inputTokens.length
        (inputTokens.length + tailTokens.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length)
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length)
        1 endpointBound := by
    unfold CompactCertificateNodeInductionPAEndpointBoundedGraph
    refine
      ⟨inputBoundary, ?_, input.length, ?_, Nat.size inputBoundary, ?_,
        inputTokens.length, ?_,
        inputTokens.length + tailTokens.length, ?_,
        tailBoundary, ?_, tail.length, ?_, Nat.size tailBoundary, ?_,
        axiomBoundary, ?_, axiomTokens.length, ?_, Nat.size axiomBoundary, ?_,
        formulaBoundary, ?_, formulaInput.length, ?_,
        Nat.size formulaBoundary, ?_,
        suffixBoundary, ?_, suffix.length, ?_, Nat.size suffixBoundary, ?_,
        stateBoundary, ?_, states.length, ?_, tableWidth, ?_,
        2 ^ tableWidth, ?_, ?_⟩
    · exact nat_le_two_pow_of_size_le
        (hinputBoundaryPublic.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hinputCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (hinputBoundarySizeSize.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailStartSize.trans htokenToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailFinishSize.trans htokenToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailBoundaryPublic.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (htailBoundarySizeSize.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (haxiomBoundaryPublic.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (haxiomCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (haxiomBoundarySizeSize.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hformulaBoundaryPublic.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hformulaCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (hformulaBoundarySizeSize.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hsuffixBoundaryPublic.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hsuffixCountSize.trans hinputToHidden)
    · exact nat_le_two_pow_of_size_le
        (hsuffixBoundarySizeSize.trans hlistBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hstateBoundaryPublic.trans hstateBoundaryToHidden)
    · exact nat_le_two_pow_of_size_le
        (hstateCountSize.trans hfuelToHidden)
    · exact nat_le_two_pow_of_size_le
        (htableWidthSize.trans htableBaseToHidden)
    · exact nat_le_two_pow_of_size_le
        (hvalueBoundSize.trans htableToHidden)
    · simpa only [coordinates, parserCoordinates,
        compactCertificateNodeInductionPAEndpointCoordinatesOfValues] using hgraph
  have hendpoint :
      Nat.size endpointBound <=
        compactCertificateNodeInductionPAEndpointSizeBound inputWeight := by
    dsimp only [endpointBound]
    rw [Nat.size_pow]
    unfold hiddenBound compactCertificateNodeInductionPAEndpointSizeBound
    exact Nat.le_refl _
  let publicBound :=
    compactCertificateNodeInductionPAPublicCoordinateSizeBound inputWeight
  have htablePublic : Nat.size tokenTable <= publicBound :=
    htable.trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size width <= publicBound :=
    (natSize_le_of_le hwidth).trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  have hwidthValuePublic : width <= publicBound :=
    hwidth.trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= publicBound :=
    (natSize_le_of_le htokenCount).trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  have htokenCountValuePublic : tokens.length <= publicBound :=
    htokenCount.trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  have hpositionPublic
      {position : Nat} (hposition : position <= tokens.length) :
      Nat.size position <= publicBound :=
    (natSize_le_of_le (hposition.trans htokenCount)).trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  have hinputFinishPublic : Nat.size inputTokens.length <= publicBound :=
    hpositionPublic (by simp [tokens])
  have haxiomStartPublic :
      Nat.size (inputTokens.length + tailTokens.length) <= publicBound :=
    hpositionPublic (by
      simp only [tokens, List.length_append]
      omega)
  have haxiomFinishPublic :
      Nat.size
        (inputTokens.length + tailTokens.length + axiomEncoded.length) <=
          publicBound :=
    hpositionPublic (by
      simp only [tokens, List.length_append]
      omega)
  have hformulaFinishPublic :
      Nat.size
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length) <= publicBound :=
    hpositionPublic (by
      simp only [tokens, List.length_append]
      omega)
  have hsuffixFinishPublic :
      Nat.size
        (inputTokens.length + tailTokens.length + axiomEncoded.length +
          formulaEncoded.length + suffixEncoded.length) <= publicBound :=
    hpositionPublic (by
      simp only [tokens, List.length_append]
      omega)
  have hcertificateTagPublic : Nat.size 1 <= publicBound := by
    unfold publicBound
      compactCertificateNodeInductionPAPublicCoordinateSizeBound
    simp
  have hendpointPublic : Nat.size endpointBound <= publicBound :=
    hendpoint.trans (by
      unfold publicBound
        compactCertificateNodeInductionPAPublicCoordinateSizeBound
      omega)
  refine
    ⟨tokenTable, width, tokens.length, 0, inputTokens.length,
      inputTokens.length + tailTokens.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length +
        formulaEncoded.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length +
        formulaEncoded.length,
      inputTokens.length + tailTokens.length + axiomEncoded.length +
        formulaEncoded.length + suffixEncoded.length,
      endpointBound, by simpa [input, tail] using hinputLayoutExact,
      hbounded, ?_⟩
  exact
    { tokenTable := htablePublic
      width_value := hwidthValuePublic
      width := hwidthPublic
      tokenCount_value := htokenCountValuePublic
      tokenCount := htokenCountPublic
      inputStart := by simp
      inputFinish := hinputFinishPublic
      axiomStart := haxiomStartPublic
      axiomFinish := haxiomFinishPublic
      formulaStart := haxiomFinishPublic
      formulaFinish := hformulaFinishPublic
      suffixStart := hformulaFinishPublic
      suffixFinish := hsuffixFinishPublic
      certificateTag := hcertificateTagPublic
      endpointBound := hendpointPublic }

#print axioms
  exists_compactCertificateNodeInductionPAEndpointBoundedGraph_with_publicBounds
#print axioms compactCertificateNodeInductionPAPublicCoordinateSizeBound_mono

end FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds
