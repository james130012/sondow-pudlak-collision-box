import integration.FoundationCompactNumericListedDirectVerifierPAAxiomLeafStateGraph
import integration.FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds
import integration.FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
import integration.FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
import integration.FoundationCompactNumericListedDirectVerifierParseStateCompleteness

/-!
# Public coordinate bounds for the PA-axiom leaf state

The PA leaf has two independently canonical tables.  Its rule table contains
the complete guarded-induction work area, while its certificate table contains
one of the fixed, symbol, or induction parser endpoints.  This file retains the
quantitative facts produced by those canonical constructors and gives one
pointwise `Nat.size` bound for all 259 joint coordinates.

The rule input scale below is the additive weight of the deterministic
canonical chunk stream.  It is a function of `Gamma`, `candidate`, and
`certificate`; it is not an environment coordinate or an aggregate over the
259-coordinate environment.  In the induction branch this scale necessarily
includes the explicitly generated universal closure, whose length is governed
by the semantic free-variable supremum rather than the binary size of that
supremum.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactCertificateTokenMachine
open FoundationCompactCertificateTokenMachineInversion
open FoundationCompactSyntaxTokenMachine
open FoundationCompactSyntaxTokenMachineInversion
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactPAAxiomCertificate
open FoundationCompactNumericFormulaListChecks
open FoundationCompactNumericPAAxiomComparator
open FoundationCompactNumericFixedPAAxiomSentence
open FoundationCompactNumericGuardedInductionSentence
open FoundationCompactNumericTokenBitLength
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpoint
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectFormulaTransformTotalExactEndpointCompleteness
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectSuccIndBaseNegationRoute
open FoundationCompactNumericListedDirectSuccIndStepAssemblyRoute
open FoundationCompactNumericListedDirectSuccIndSentenceRoute
open FoundationCompactNumericListedDirectFormulaFvSupTotalEndpoint
open FoundationCompactNumericListedDirectFixedAllClosureTotalEndpoint
open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectGuardedInductionSentenceRouteCompleteness
open FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheckCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomNonInductionLeafRows
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierPAAxiomJointLeafRowsCompleteness
open FoundationCompactNumericListedDirectCertificateNodeFixedPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeInductionPAEndpoint
open FoundationCompactNumericListedDirectCertificateNodeFixedPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeSymbolPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeInductionPABoundedFormula
open FoundationCompactNumericListedDirectCertificateNodeFixedPAPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeSymbolPAPublicBounds
open FoundationCompactNumericListedDirectCertificateNodeInductionPAPublicBounds
open FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
open FoundationCompactNumericListedDirectVerifierParseStateCompleteness

/-- The deterministic flat rule-table stream built from the three actual PA
leaf inputs.  No witness coordinate occurs in this definition. -/
def compactNumericVerifierPAAxiomJointLeafCanonicalRuleTokens
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) : List Nat :=
  (compactPAAxiomLeafRuleRowsCanonicalChunks
    Gamma candidate certificate).flatten

/-- Honest additive scale of the deterministic rule-table serialization. -/
def compactNumericVerifierPAAxiomJointLeafRuleInputWeight
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) : Nat :=
  compactAdditiveTokenWeight
    (compactNumericVerifierPAAxiomJointLeafCanonicalRuleTokens
      Gamma candidate certificate)

/-- Honest additive scale of the structural-certificate endpoint input. -/
def compactNumericVerifierPAAxiomJointLeafEndpointInputWeight
    (certificate : PAAxiomCertificate) : Nat :=
  compactAdditiveValueWeight
    (1 :: compactPAAxiomCertificateTokens certificate)

def compactNumericVerifierPAAxiomJointLeafRuleFuelBound
    (ruleInputWeight : Nat) : Nat :=
  compactNumericCertificateParserFuelWeightBound ruleInputWeight

def compactNumericVerifierPAAxiomJointLeafRuleWidthBound
    (ruleInputWeight : Nat) : Nat :=
  2 * ruleInputWeight

def compactNumericVerifierPAAxiomJointLeafRuleTableSizeBound
    (ruleInputWeight : Nat) : Nat :=
  ruleInputWeight *
    compactNumericVerifierPAAxiomJointLeafRuleWidthBound ruleInputWeight

def compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
    (ruleInputWeight : Nat) : Nat :=
  (ruleInputWeight + 1) * ruleInputWeight

def compactNumericVerifierPAAxiomJointLeafRuleStateBoundarySizeBound
    (ruleInputWeight : Nat) : Nat :=
  (compactNumericVerifierPAAxiomJointLeafRuleFuelBound ruleInputWeight + 2) *
    ruleInputWeight

def compactNumericVerifierPAAxiomJointLeafRuleTransformTableWidthBound
    (ruleInputWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalTableWidthBound
    (compactNumericVerifierPAAxiomJointLeafRuleWidthBound ruleInputWeight)
    ruleInputWeight
    (compactNumericVerifierPAAxiomJointLeafRuleFuelBound ruleInputWeight)

/-- A fixed polynomial envelope for every coordinate contributed by the
canonical rule table, including all twelve guarded-induction traces. -/
def compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    (ruleInputWeight : Nat) : Nat :=
  compactNumericVerifierPAAxiomJointLeafRuleTableSizeBound ruleInputWeight +
    compactNumericVerifierPAAxiomJointLeafRuleWidthBound ruleInputWeight +
    ruleInputWeight +
    compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
      ruleInputWeight +
    compactNumericVerifierPAAxiomJointLeafRuleStateBoundarySizeBound
      ruleInputWeight +
    compactNumericVerifierPAAxiomJointLeafRuleFuelBound ruleInputWeight +
    compactNumericVerifierPAAxiomJointLeafRuleTransformTableWidthBound
      ruleInputWeight + 128

/-- One certificate-table envelope.  Summing the three public endpoint
polynomials makes the bound branch-independent; only one summand is active. -/
def compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
    (endpointInputWeight : Nat) : Nat :=
  compactCertificateNodeFixedPAPublicCoordinateSizeBound endpointInputWeight +
    compactCertificateNodeSymbolPAPublicCoordinateSizeBound endpointInputWeight +
    compactCertificateNodeInductionPAPublicCoordinateSizeBound
      endpointInputWeight

/-- Public pointwise bound for the complete 259-column PA joint environment. -/
def compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) : Nat :=
  compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      (compactNumericVerifierPAAxiomJointLeafRuleInputWeight
        Gamma candidate certificate) +
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      (compactNumericVerifierPAAxiomJointLeafEndpointInputWeight certificate)


private theorem natSize_vecAppend_le
    {leftLength rightLength totalLength bound : Nat}
    (length_eq : totalLength = leftLength + rightLength)
    (left : Fin leftLength -> Nat) (right : Fin rightLength -> Nat)
    (hleft : forall coordinate, Nat.size (left coordinate) <= bound)
    (hright : forall coordinate, Nat.size (right coordinate) <= bound)
    (coordinate : Fin totalLength) :
    Nat.size (Matrix.vecAppend length_eq left right coordinate) <= bound := by
  rw [Matrix.vecAppend_eq_ite]
  dsimp only
  split_ifs with hcoordinate
  · exact hleft ⟨coordinate, hcoordinate⟩
  · exact hright ⟨coordinate - leftLength, by omega⟩

private theorem compactAdditiveTokenList_length_le_weight
    (tokens : List Nat) :
    tokens.length <= compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
      omega

private theorem compactAdditiveValueWeight_le_flatten_of_mem
    (chunks : List (List Nat)) (values : List Nat)
    (hmem : compactAdditiveEncode values ∈ chunks) :
    compactAdditiveValueWeight values <=
      compactAdditiveTokenWeight chunks.flatten := by
  induction chunks with
  | nil => simp at hmem
  | cons head tail ih =>
      rw [List.flatten_cons, compactAdditiveTokenWeight_append]
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        unfold compactAdditiveValueWeight
        omega
      · have := ih htail
        omega

private theorem compactAdditiveStructuredListLayout_coordinates_le
    {tokenTable width tokenCount start count finish boundaryTable : Nat}
    (hlayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start count finish boundaryTable) :
    start <= tokenCount /\ count <= tokenCount /\ finish <= tokenCount := by
  rcases hlayout with ⟨bodyStart, _hbodyStart, hheader, hboundary⟩
  have hstart : start < tokenCount := hheader.1.1
  have hcount : bodyStart + count <= tokenCount := hheader.2
  have hfinish : finish <= tokenCount := hboundary.2.1
  omega

private theorem compactFormulaTransformAdjacentStepPublicWidth_mono
    {widthLeft widthRight tokenLeft tokenRight : Nat}
    (hwidth : widthLeft <= widthRight)
    (htoken : tokenLeft <= tokenRight) :
    compactFormulaTransformAdjacentStepPublicWidth widthLeft tokenLeft <=
      compactFormulaTransformAdjacentStepPublicWidth widthRight tokenRight := by
  have hsucc : tokenLeft + 1 <= tokenRight + 1 :=
    Nat.add_le_add_right htoken 1
  have harea := Nat.mul_le_mul hsucc htoken
  unfold compactFormulaTransformAdjacentStepPublicWidth
    compactBinaryNatStreamStepWitnessPublicWidth
  omega

private theorem compactFormulaTransformCanonicalTableWidthBound_mono
    {widthLeft widthRight tokenLeft tokenRight fuelLeft fuelRight : Nat}
    (hwidth : widthLeft <= widthRight)
    (htoken : tokenLeft <= tokenRight)
    (hfuel : fuelLeft <= fuelRight) :
    compactFormulaTransformCanonicalTableWidthBound
        widthLeft tokenLeft fuelLeft <=
      compactFormulaTransformCanonicalTableWidthBound
        widthRight tokenRight fuelRight := by
  have hadjacent :=
    compactFormulaTransformAdjacentStepPublicWidth_mono hwidth htoken
  have hcolumns := Nat.mul_le_mul_right
    compactFormulaTransformAdjacentStepWitnessColumnCount hfuel
  have hrows := Nat.mul_le_mul hcolumns hadjacent
  have hsucc : tokenLeft + 1 <= tokenRight + 1 :=
    Nat.add_le_add_right htoken 1
  have harea := Nat.mul_le_mul hsucc htoken
  have htail := Nat.mul_le_mul_left 31 hadjacent
  unfold compactFormulaTransformCanonicalTableWidthBound
  omega


structure CompactNatListRowSlotPublicCoordinateBounds
    (slot : CompactNatListRowSlot) (bound : Nat) : Prop where
  start : Nat.size slot.start <= bound
  finish : Nat.size slot.finish <= bound
  boundary : Nat.size slot.boundary <= bound
  count : Nat.size slot.count <= bound
  boundarySize : Nat.size slot.boundarySize <= bound

theorem CompactNatListRowSlotPublicCoordinateBounds.mono
    {slot : CompactNatListRowSlot} {left right : Nat}
    (hbounds : CompactNatListRowSlotPublicCoordinateBounds slot left)
    (h : left <= right) :
    CompactNatListRowSlotPublicCoordinateBounds slot right :=
  { start := hbounds.start.trans h
    finish := hbounds.finish.trans h
    boundary := hbounds.boundary.trans h
    count := hbounds.count.trans h
    boundarySize := hbounds.boundarySize.trans h }

private theorem CompactPackedNatListSlotCanonical.publicCoordinateBounds
    {tokenTable width tokenCount ruleInputWeight : Nat}
    {slot : CompactNatListRowSlot} {values : List Nat}
    (hslot : CompactPackedNatListSlotCanonical
      tokenTable width tokenCount slot values)
    (htokenCount : tokenCount <= ruleInputWeight) :
    CompactNatListRowSlotPublicCoordinateBounds slot
      (compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        ruleInputWeight) := by
  let bound := compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    ruleInputWeight
  have hcoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hslot.2.1.1
  have hposition {value : Nat} (hvalue : value <= tokenCount) :
      Nat.size value <= bound := by
    exact (natSize_le_of_le (hvalue.trans htokenCount)).trans (by
      dsimp only [bound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have harea : (slot.count + 1) * tokenCount <=
      (ruleInputWeight + 1) * ruleInputWeight := by
    exact Nat.mul_le_mul
      (Nat.add_le_add_right (hcoordinates.2.1.trans htokenCount) 1)
      htokenCount
  have hboundary : Nat.size slot.boundary <= bound := by
    rw [← hslot.2.1.2.2.1]
    exact hslot.2.1.2.2.2 |>.trans harea |>.trans (by
      dsimp only [bound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      unfold compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
      omega)
  have hboundarySize : Nat.size slot.boundarySize <= bound := by
    exact (natSize_le_of_le (Nat.le_refl slot.boundarySize)).trans
      (hslot.2.1.2.2.2.trans (harea.trans (by
        dsimp only [bound]
        unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        unfold compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
        omega)))
  exact
    { start := hposition hcoordinates.1
      finish := hposition hcoordinates.2.2
      boundary := hboundary
      count := hposition hcoordinates.2.1
      boundarySize := hboundarySize }

structure CompactFormulaTransformTraceCanonicalNumericBounds
    (trace : CompactFormulaTransformTraceSlot)
    (width tokenCount : Nat) (input : List Nat) : Prop where
  stateBoundary : Nat.size trace.stateBoundary <=
    (compactSyntaxRunFuelBound input + 2) * tokenCount
  stateCount : trace.stateCount = compactSyntaxRunFuelBound input + 1
  tableWidth : trace.tableWidth <=
    compactFormulaTransformCanonicalTableWidthBound width tokenCount
      (compactSyntaxRunFuelBound input)
  valueBound : trace.valueBound = 2 ^ trace.tableWidth

structure CompactFormulaTransformTracePublicCoordinateBounds
    (trace : CompactFormulaTransformTraceSlot) (bound : Nat) : Prop where
  stateBoundary : Nat.size trace.stateBoundary <= bound
  stateCount : Nat.size trace.stateCount <= bound
  tableWidth : Nat.size trace.tableWidth <= bound
  valueBound : Nat.size trace.valueBound <= bound

private theorem
    CompactFormulaTransformTraceCanonicalNumericBounds.publicCoordinateBounds
    {trace : CompactFormulaTransformTraceSlot}
    {width tokenCount ruleInputWeight : Nat} {input : List Nat}
    (htrace : CompactFormulaTransformTraceCanonicalNumericBounds
      trace width tokenCount input)
    (hwidth : width <=
      compactNumericVerifierPAAxiomJointLeafRuleWidthBound ruleInputWeight)
    (htokenCount : tokenCount <= ruleInputWeight)
    (hinputWeight : compactAdditiveValueWeight input <= ruleInputWeight) :
    CompactFormulaTransformTracePublicCoordinateBounds trace
      (compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        ruleInputWeight) := by
  let fuelBound :=
    compactNumericVerifierPAAxiomJointLeafRuleFuelBound ruleInputWeight
  let transformWidthBound :=
    compactNumericVerifierPAAxiomJointLeafRuleTransformTableWidthBound
      ruleInputWeight
  let bound := compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    ruleInputWeight
  have hfuel : compactSyntaxRunFuelBound input <= fuelBound := by
    unfold fuelBound
    exact compactSyntaxRunFuelBound_le_weightBound hinputWeight
  have hstateArea : (compactSyntaxRunFuelBound input + 2) * tokenCount <=
      (fuelBound + 2) * ruleInputWeight :=
    Nat.mul_le_mul (Nat.add_le_add_right hfuel 2) htokenCount
  have htableWidth : trace.tableWidth <= transformWidthBound := by
    exact htrace.tableWidth.trans (by
      unfold transformWidthBound
      exact compactFormulaTransformCanonicalTableWidthBound_mono
        hwidth htokenCount hfuel)
  refine
    { stateBoundary := htrace.stateBoundary.trans (hstateArea.trans ?_)
      stateCount := ?_
      tableWidth := ?_
      valueBound := ?_ }
  · dsimp only [bound, fuelBound, transformWidthBound]
    unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    unfold compactNumericVerifierPAAxiomJointLeafRuleStateBoundarySizeBound
    omega
  · rw [htrace.stateCount]
    exact (natSize_le_of_le (Nat.add_le_add_right hfuel 1)).trans (by
      dsimp only [bound, fuelBound, transformWidthBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  · exact (natSize_le_of_le htableWidth).trans (by
      dsimp only [bound, fuelBound, transformWidthBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  · rw [htrace.valueBound, Nat.size_pow]
    exact (Nat.add_le_add_right htableWidth 1).trans (by
      dsimp only [bound, fuelBound, transformWidthBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)


private theorem
    exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
    {tokenTable width tokenCount stateBoundary mode binderArity : Nat}
    {witnessStart witnessFinish witnessBoundary witnessBoundarySize
      inputStart inputFinish inputBoundary inputBoundarySize
      outputStart outputFinish outputBoundary outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize : Nat}
    {witness input output : List Nat}
    (hwitnessRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount witnessStart witness.length witnessFinish
        witnessBoundary witnessBoundarySize)
    (hinputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount inputStart input.length inputFinish
        inputBoundary inputBoundarySize)
    (houtputRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount outputStart output.length outputFinish
        outputBoundary outputBoundarySize)
    (hemptyRows : CompactAdditiveNatListWitnessRows
      tokenTable width tokenCount emptyStart 0 emptyFinish
        emptyBoundary emptyBoundarySize)
    (hwitnessLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount witnessStart witnessFinish witness)
    (hinputElements : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        inputBoundary input)
    (houtputElements : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        outputBoundary output)
    (hemptyElements : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        emptyBoundary [])
    (hstateRows : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokenCount stateBoundary
        (compactFormulaTransformStateTrace (mode, witness)
          (compactSyntaxRunFuelBound input)
          (compactFormulaTransformInitialState binderArity input)))
    (hstateBoundary : Nat.size stateBoundary <=
      (compactSyntaxRunFuelBound input + 2) * tokenCount)
    (hresult : output =
      (compactExactFormulaTransformResult
        (compactFormulaTransformResult
          (mode, witness) (binderArity, input))).getD []) :
    ∃ trace : CompactFormulaTransformTraceSlot,
      CompactFormulaTransformTotalExactEndpoint
        tokenTable width tokenCount mode binderArity
        witnessStart witnessFinish witnessBoundary witness.length
          witnessBoundarySize
        inputStart inputFinish inputBoundary input.length inputBoundarySize
        outputStart outputFinish outputBoundary output.length
          outputBoundarySize
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        trace.stateBoundary trace.stateCount trace.tableWidth
          trace.valueBound /\
      CompactFormulaTransformTraceCanonicalNumericBounds
        trace width tokenCount input := by
  rcases
      CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
        hstateRows hwitnessLayout rfl hinputElements houtputElements
        hemptyElements hresult with
    ⟨tableWidth, hgraph, htableWidth⟩
  let trace : CompactFormulaTransformTraceSlot :=
    { stateBoundary := stateBoundary
      stateCount := compactSyntaxRunFuelBound input + 1
      tableWidth := tableWidth
      valueBound := 2 ^ tableWidth }
  have hendpoint : CompactFormulaTransformTotalExactEndpoint
      tokenTable width tokenCount mode binderArity
      witnessStart witnessFinish witnessBoundary witness.length
        witnessBoundarySize
      inputStart inputFinish inputBoundary input.length inputBoundarySize
      outputStart outputFinish outputBoundary output.length outputBoundarySize
      emptyStart emptyFinish emptyBoundary emptyBoundarySize
      trace.stateBoundary trace.stateCount trace.tableWidth
        trace.valueBound := by
    refine ⟨hwitnessRows, hinputRows, houtputRows, hemptyRows, ?_⟩
    simpa [trace] using hgraph
  exact ⟨trace, hendpoint,
    { stateBoundary := by simpa [trace] using hstateBoundary
      stateCount := by simp [trace]
      tableWidth := by simpa [trace] using htableWidth
      valueBound := by simp [trace] }⟩


private theorem compactPackedFormulaTransformStateBoundary_size_le
    (chunks : List (List Nat)) (index mode binderArity : Nat)
    (witness input : List Nat)
    (hindex : index < chunks.length)
    (hchunk : chunks[index] = compactAdditiveEncode
      (compactFormulaTransformStateTrace (mode, witness)
        (compactSyntaxRunFuelBound input)
        (compactFormulaTransformInitialState binderArity input))) :
    Nat.size
        (compactPackedFormulaTransformStateBoundary chunks index
          (compactFormulaTransformStateTrace (mode, witness)
            (compactSyntaxRunFuelBound input)
            (compactFormulaTransformInitialState binderArity input))) <=
      (compactSyntaxRunFuelBound input + 2) * chunks.flatten.length := by
  have hcanonical :=
    compactPackedFormulaTransformStateRows_canonical_with_size
      chunks index
      (compactFormulaTransformStateTrace (mode, witness)
        (compactSyntaxRunFuelBound input)
        (compactFormulaTransformInitialState binderArity input))
      hindex hchunk
  simpa only [compactFormulaTransformStateTrace_length, Nat.add_assoc] using
    hcanonical.2


/-- The twelve quantitative trace packages retained by the guarded-induction
constructor. -/
structure CompactGuardedInductionSentenceRouteCanonicalNumericBounds
    (width tokenCount : Nat)
    (chunks : List (List Nat))
    (data : CompactGuardedInductionExecutableData)
    (route : CompactGuardedInductionSentenceRouteCoordinates) : Prop where
  openZeroShifted : route.sentence.openZero.shifted =
    compactPackedNatListSlot chunks 8 data.openZeroShifted
  openZeroSubstituted : route.sentence.openZero.substituted =
    compactPackedNatListSlot chunks 9 data.openZeroSubstituted
  openSuccessorShifted : route.sentence.openSuccessor.shifted =
    compactPackedNatListSlot chunks 11 data.openSuccessorShifted
  openSuccessorSubstituted : route.sentence.openSuccessor.substituted =
    compactPackedNatListSlot chunks 12 data.openSuccessorSubstituted
  base : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.base.baseTrace width tokenCount data.body
  baseNegation : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.base.negationTrace width tokenCount data.base
  openZeroShift : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.openZero.shiftTrace width tokenCount data.body
  openZeroSubstitution : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.openZero.substitutionTrace width tokenCount
      data.openZeroShifted
  openZeroFixitr : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.openZero.fixitrTrace width tokenCount
      data.openZeroSubstituted
  openSuccessorShift : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.openSuccessor.shiftTrace width tokenCount data.body
  openSuccessorSubstitution : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.openSuccessor.substitutionTrace width tokenCount
      data.openSuccessorShifted
  openSuccessorFixitr : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.openSuccessor.fixitrTrace width tokenCount
      data.openSuccessorSubstituted
  stepNegation : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.step.negatedStepZeroTrace width tokenCount data.stepZero
  quantifiedStepNegation : CompactFormulaTransformTraceCanonicalNumericBounds
    route.sentence.step.negatedQuantifiedStepTrace width tokenCount
      data.quantifiedStep
  fvarList : CompactFormulaTransformTraceCanonicalNumericBounds
    route.fvSup.trace width tokenCount data.sentence
  closure : CompactFormulaTransformTraceCanonicalNumericBounds
    route.closure.trace width tokenCount data.sentence

/- Each guarded-induction block is rebuilt independently.  The old canonical
route supplies only the coordinate-free shell facts; every transform endpoint
and every numeric trace fact below comes from the retained bounded constructor. -/
set_option maxHeartbeats 20000 in
private theorem exists_compactGuardedInductionBaseRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∀ oldCoordinates : CompactSuccIndBaseNegationRouteCoordinates,
      CompactSuccIndBaseNegationRoute tokenTable width tokens.length
          (compactPackedNatListSlot chunks 0 data.body)
          (compactPackedNatListSlot chunks 1 data.zeroWitness)
          (compactPackedNatListSlot chunks 6 data.base)
          (compactPackedNatListSlot chunks 7 data.negatedBase)
          (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndBaseNegationRouteCoordinates,
        CompactSuccIndBaseNegationRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 0 data.body)
            (compactPackedNatListSlot chunks 1 data.zeroWitness)
            (compactPackedNatListSlot chunks 6 data.base)
            (compactPackedNatListSlot chunks 7 data.negatedBase)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.baseTrace width tokens.length data.body /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.negationTrace width tokens.length data.base := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∀ oldCoordinates : CompactSuccIndBaseNegationRouteCoordinates,
    CompactSuccIndBaseNegationRoute tokenTable width tokens.length
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndBaseNegationRouteCoordinates,
        CompactSuccIndBaseNegationRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 0 data.body)
            (compactPackedNatListSlot chunks 1 data.zeroWitness)
            (compactPackedNatListSlot chunks 6 data.base)
            (compactPackedNatListSlot chunks 7 data.negatedBase)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.baseTrace width tokens.length data.body /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.negationTrace width tokens.length data.base
  intro oldCoordinates holdRoute
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  rcases holdRoute with
    ⟨hbaseEmpty, hzeroWitnessLiteral, _holdBaseEndpoint,
      _holdBaseNegationEndpoint⟩
  have hbaseStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 25
          (compactGuardedInductionTransformStates
            2 data.zeroWitness 1 data.body)) <=
        (compactSyntaxRunFuelBound data.body + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 25 2 1 data.zeroWitness data.body
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  have hbaseNegationStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 26
          (compactGuardedInductionTransformStates
            3 data.empty 0 data.base)) <=
        (compactSyntaxRunFuelBound data.base + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 26 3 0 data.empty data.base
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.zeroWitness.rows hnat.body.rows hnat.base.rows hnat.empty.rows
      hnat.zeroWitness.layout hnat.body.elements hnat.base.elements
      hnat.empty.elements hstates.base hbaseStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform] using
        compactGuardedInductionBase_eq bodyTokens) with
    ⟨baseTrace, hbaseEndpoint, hbaseBounds⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.empty.rows hnat.base.rows hnat.negatedBase.rows hnat.empty.rows
      hnat.empty.layout hnat.base.elements hnat.negatedBase.elements
      hnat.empty.elements hstates.baseNegation hbaseNegationStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform,
          compactGuardedInductionEmpty] using
        compactGuardedInductionNegatedBase_eq bodyTokens) with
    ⟨negationTrace, hnegationEndpoint, hnegationBounds⟩
  let coordinates : CompactSuccIndBaseNegationRouteCoordinates :=
    { baseTrace := baseTrace
      negationTrace := negationTrace }
  have hroute : CompactSuccIndBaseNegationRoute
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
    refine ⟨hbaseEmpty, hzeroWitnessLiteral, ?_, ?_⟩
    · simpa [coordinates, hnat.zeroWitness.1, hnat.body.1,
        hnat.base.1] using hbaseEndpoint
    · simpa [coordinates, hnat.empty.1, hnat.base.1,
        hnat.negatedBase.1] using hnegationEndpoint
  refine ⟨coordinates, hroute, ?_, ?_⟩
  · simpa [coordinates] using hbaseBounds
  · simpa [coordinates] using hnegationBounds


set_option maxHeartbeats 700000 in
private theorem exists_compactGuardedInductionOpenZeroRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∀ oldCoordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
      CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
          (compactPackedNatListSlot chunks 0 data.body)
          (compactPackedNatListSlot chunks 2 data.openZeroWitness)
          (compactPackedNatListSlot chunks 4 data.captureOne)
          (compactPackedNatListSlot chunks 10 data.stepZero)
          (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
        CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 0 data.body)
            (compactPackedNatListSlot chunks 2 data.openZeroWitness)
            (compactPackedNatListSlot chunks 4 data.captureOne)
            (compactPackedNatListSlot chunks 10 data.stepZero)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          coordinates.shifted =
            compactPackedNatListSlot chunks 8 data.openZeroShifted /\
          coordinates.substituted =
            compactPackedNatListSlot chunks 9 data.openZeroSubstituted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.shiftTrace width tokens.length data.body /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.substitutionTrace width tokens.length
              data.openZeroShifted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.fixitrTrace width tokens.length
              data.openZeroSubstituted := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∀ oldCoordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
    CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
        CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 0 data.body)
            (compactPackedNatListSlot chunks 2 data.openZeroWitness)
            (compactPackedNatListSlot chunks 4 data.captureOne)
            (compactPackedNatListSlot chunks 10 data.stepZero)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          coordinates.shifted =
            compactPackedNatListSlot chunks 8 data.openZeroShifted /\
          coordinates.substituted =
            compactPackedNatListSlot chunks 9 data.openZeroSubstituted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.shiftTrace width tokens.length data.body /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.substitutionTrace width tokens.length
              data.openZeroShifted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.fixitrTrace width tokens.length
              data.openZeroSubstituted
  intro oldCoordinates holdRoute
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  rcases holdRoute with
    ⟨hopenZeroEmpty, hopenZeroCapture, _holdShift,
      _holdSubstitution, _holdFixitr⟩
  have hshiftStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 27
          (compactGuardedInductionTransformStates
            1 data.empty 1 data.body)) <=
        (compactSyntaxRunFuelBound data.body + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 27 1 1 data.empty data.body
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  have hsubstitutionStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 28
          (compactGuardedInductionTransformStates
            2 data.openZeroWitness 1 data.openZeroShifted)) <=
        (compactSyntaxRunFuelBound data.openZeroShifted + 2) *
          tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 28 2 1 data.openZeroWitness data.openZeroShifted
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  have hfixitrStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 29
          (compactGuardedInductionTransformStates
            5 data.captureOne 0 data.openZeroSubstituted)) <=
        (compactSyntaxRunFuelBound data.openZeroSubstituted + 2) *
          tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 29 5 0 data.captureOne data.openZeroSubstituted
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.empty.rows hnat.body.rows hnat.openZeroShifted.rows hnat.empty.rows
      hnat.empty.layout hnat.body.elements hnat.openZeroShifted.elements
      hnat.empty.elements hstates.openZeroShift hshiftStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform,
          compactGuardedInductionEmpty] using
        compactGuardedInductionOpenZeroShifted_eq bodyTokens) with
    ⟨shiftTrace, hshiftEndpoint, hshiftBounds⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.openZeroWitness.rows hnat.openZeroShifted.rows
      hnat.openZeroSubstituted.rows hnat.empty.rows
      hnat.openZeroWitness.layout hnat.openZeroShifted.elements
      hnat.openZeroSubstituted.elements hnat.empty.elements
      hstates.openZeroSubstitution hsubstitutionStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform] using
        compactGuardedInductionOpenZeroSubstituted_eq bodyTokens) with
    ⟨substitutionTrace, hsubstitutionEndpoint, hsubstitutionBounds⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.captureOne.rows hnat.openZeroSubstituted.rows hnat.stepZero.rows
      hnat.empty.rows hnat.captureOne.layout
      hnat.openZeroSubstituted.elements hnat.stepZero.elements
      hnat.empty.elements hstates.openZeroFixitr hfixitrStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform] using
        compactGuardedInductionStepZero_eq bodyTokens) with
    ⟨fixitrTrace, hfixitrEndpoint, hfixitrBounds⟩
  let coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates :=
    { shifted := compactPackedNatListSlot chunks 8 data.openZeroShifted
      substituted :=
        compactPackedNatListSlot chunks 9 data.openZeroSubstituted
      shiftTrace := shiftTrace
      substitutionTrace := substitutionTrace
      fixitrTrace := fixitrTrace }
  have hroute : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
    refine ⟨hopenZeroEmpty, hopenZeroCapture, ?_, ?_, ?_⟩
    · simpa [coordinates, hnat.empty.1, hnat.body.1,
        hnat.openZeroShifted.1] using hshiftEndpoint
    · simpa [coordinates, hnat.openZeroWitness.1,
        hnat.openZeroShifted.1, hnat.openZeroSubstituted.1] using
          hsubstitutionEndpoint
    · simpa [coordinates, hnat.captureOne.1,
        hnat.openZeroSubstituted.1, hnat.stepZero.1] using hfixitrEndpoint
  refine ⟨coordinates, hroute, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [coordinates] using hshiftBounds
  · simpa [coordinates] using hsubstitutionBounds
  · simpa [coordinates] using hfixitrBounds


set_option maxHeartbeats 700000 in
private theorem
    exists_compactGuardedInductionOpenSuccessorRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∀ oldCoordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
      CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
          (compactPackedNatListSlot chunks 0 data.body)
          (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
          (compactPackedNatListSlot chunks 4 data.captureOne)
          (compactPackedNatListSlot chunks 13 data.stepSuccessor)
          (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
        CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 0 data.body)
            (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
            (compactPackedNatListSlot chunks 4 data.captureOne)
            (compactPackedNatListSlot chunks 13 data.stepSuccessor)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          coordinates.shifted =
            compactPackedNatListSlot chunks 11 data.openSuccessorShifted /\
          coordinates.substituted =
            compactPackedNatListSlot chunks 12 data.openSuccessorSubstituted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.shiftTrace width tokens.length data.body /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.substitutionTrace width tokens.length
              data.openSuccessorShifted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.fixitrTrace width tokens.length
              data.openSuccessorSubstituted := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∀ oldCoordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
    CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates,
        CompactSuccIndOpenSubstitutionRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 0 data.body)
            (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
            (compactPackedNatListSlot chunks 4 data.captureOne)
            (compactPackedNatListSlot chunks 13 data.stepSuccessor)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          coordinates.shifted =
            compactPackedNatListSlot chunks 11 data.openSuccessorShifted /\
          coordinates.substituted =
            compactPackedNatListSlot chunks 12 data.openSuccessorSubstituted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.shiftTrace width tokens.length data.body /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.substitutionTrace width tokens.length
              data.openSuccessorShifted /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.fixitrTrace width tokens.length
              data.openSuccessorSubstituted
  intro oldCoordinates holdRoute
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  rcases holdRoute with
    ⟨hopenSuccessorEmpty, hopenSuccessorCapture, _holdShift,
      _holdSubstitution, _holdFixitr⟩
  have hshiftStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 30
          (compactGuardedInductionTransformStates
            1 data.empty 1 data.body)) <=
        (compactSyntaxRunFuelBound data.body + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 30 1 1 data.empty data.body
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  have hsubstitutionStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 31
          (compactGuardedInductionTransformStates
            2 data.openSuccessorWitness 1 data.openSuccessorShifted)) <=
        (compactSyntaxRunFuelBound data.openSuccessorShifted + 2) *
          tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 31 2 1 data.openSuccessorWitness data.openSuccessorShifted
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  have hfixitrStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 32
          (compactGuardedInductionTransformStates
            5 data.captureOne 0 data.openSuccessorSubstituted)) <=
        (compactSyntaxRunFuelBound data.openSuccessorSubstituted + 2) *
          tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 32 5 0 data.captureOne data.openSuccessorSubstituted
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.empty.rows hnat.body.rows hnat.openSuccessorShifted.rows
      hnat.empty.rows hnat.empty.layout hnat.body.elements
      hnat.openSuccessorShifted.elements hnat.empty.elements
      hstates.openSuccessorShift hshiftStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform,
          compactGuardedInductionEmpty] using
        compactGuardedInductionOpenSuccessorShifted_eq bodyTokens) with
    ⟨shiftTrace, hshiftEndpoint, hshiftBounds⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.openSuccessorWitness.rows hnat.openSuccessorShifted.rows
      hnat.openSuccessorSubstituted.rows hnat.empty.rows
      hnat.openSuccessorWitness.layout hnat.openSuccessorShifted.elements
      hnat.openSuccessorSubstituted.elements hnat.empty.elements
      hstates.openSuccessorSubstitution hsubstitutionStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform] using
        compactGuardedInductionOpenSuccessorSubstituted_eq bodyTokens) with
    ⟨substitutionTrace, hsubstitutionEndpoint, hsubstitutionBounds⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.captureOne.rows hnat.openSuccessorSubstituted.rows
      hnat.stepSuccessor.rows hnat.empty.rows hnat.captureOne.layout
      hnat.openSuccessorSubstituted.elements hnat.stepSuccessor.elements
      hnat.empty.elements hstates.openSuccessorFixitr hfixitrStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform] using
        compactGuardedInductionStepSuccessor_eq bodyTokens) with
    ⟨fixitrTrace, hfixitrEndpoint, hfixitrBounds⟩
  let coordinates : CompactSuccIndOpenSubstitutionRouteCoordinates :=
    { shifted :=
        compactPackedNatListSlot chunks 11 data.openSuccessorShifted
      substituted :=
        compactPackedNatListSlot chunks 12 data.openSuccessorSubstituted
      shiftTrace := shiftTrace
      substitutionTrace := substitutionTrace
      fixitrTrace := fixitrTrace }
  have hroute : CompactSuccIndOpenSubstitutionRoute
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
    refine ⟨hopenSuccessorEmpty, hopenSuccessorCapture, ?_, ?_, ?_⟩
    · simpa [coordinates, hnat.empty.1, hnat.body.1,
        hnat.openSuccessorShifted.1] using hshiftEndpoint
    · simpa [coordinates, hnat.openSuccessorWitness.1,
        hnat.openSuccessorShifted.1,
        hnat.openSuccessorSubstituted.1] using hsubstitutionEndpoint
    · simpa [coordinates, hnat.captureOne.1,
        hnat.openSuccessorSubstituted.1, hnat.stepSuccessor.1] using
          hfixitrEndpoint
  refine ⟨coordinates, hroute, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [coordinates] using hshiftBounds
  · simpa [coordinates] using hsubstitutionBounds
  · simpa [coordinates] using hfixitrBounds


set_option maxHeartbeats 500000 in
private theorem exists_compactGuardedInductionStepRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∀ oldCoordinates : CompactSuccIndStepAssemblyRouteCoordinates,
      CompactSuccIndStepAssemblyRoute tokenTable width tokens.length
          (compactPackedNatListSlot chunks 10 data.stepZero)
          (compactPackedNatListSlot chunks 13 data.stepSuccessor)
          (compactPackedNatListSlot chunks 14 data.negatedStepZero)
          (compactPackedNatListSlot chunks 15 data.stepDisjunction)
          (compactPackedNatListSlot chunks 16 data.quantifiedStep)
          (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
          (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
          (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndStepAssemblyRouteCoordinates,
        CompactSuccIndStepAssemblyRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 10 data.stepZero)
            (compactPackedNatListSlot chunks 13 data.stepSuccessor)
            (compactPackedNatListSlot chunks 14 data.negatedStepZero)
            (compactPackedNatListSlot chunks 15 data.stepDisjunction)
            (compactPackedNatListSlot chunks 16 data.quantifiedStep)
            (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
            (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.negatedStepZeroTrace width tokens.length
              data.stepZero /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.negatedQuantifiedStepTrace width tokens.length
              data.quantifiedStep := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∀ oldCoordinates : CompactSuccIndStepAssemblyRouteCoordinates,
    CompactSuccIndStepAssemblyRoute tokenTable width tokens.length
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 5 data.empty) oldCoordinates →
      ∃ coordinates : CompactSuccIndStepAssemblyRouteCoordinates,
        CompactSuccIndStepAssemblyRoute tokenTable width tokens.length
            (compactPackedNatListSlot chunks 10 data.stepZero)
            (compactPackedNatListSlot chunks 13 data.stepSuccessor)
            (compactPackedNatListSlot chunks 14 data.negatedStepZero)
            (compactPackedNatListSlot chunks 15 data.stepDisjunction)
            (compactPackedNatListSlot chunks 16 data.quantifiedStep)
            (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
            (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
            (compactPackedNatListSlot chunks 5 data.empty) coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.negatedStepZeroTrace width tokens.length
              data.stepZero /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.negatedQuantifiedStepTrace width tokens.length
              data.quantifiedStep
  intro oldCoordinates holdRoute
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  rcases holdRoute with
    ⟨hstepEmpty, hstepSuccessorRows, _holdStepNegation,
      hstepDisjunctionRows, hstepDisjunctionSlices,
      hquantifiedStepSlices, _holdQuantifiedStepNegation,
      hquantifiedFinalRows, hquantifiedFinalSlices⟩
  have hstepNegationStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 33
          (compactGuardedInductionTransformStates
            3 data.empty 1 data.stepZero)) <=
        (compactSyntaxRunFuelBound data.stepZero + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 33 3 1 data.empty data.stepZero
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  have hquantifiedStepNegationStateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 34
          (compactGuardedInductionTransformStates
            3 data.empty 0 data.quantifiedStep)) <=
        (compactSyntaxRunFuelBound data.quantifiedStep + 2) *
          tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 34 3 0 data.empty data.quantifiedStep
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.empty.rows hnat.stepZero.rows hnat.negatedStepZero.rows
      hnat.empty.rows hnat.empty.layout hnat.stepZero.elements
      hnat.negatedStepZero.elements hnat.empty.elements hstates.stepNegation
      hstepNegationStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform,
          compactGuardedInductionEmpty] using
        compactGuardedInductionNegatedStepZero_eq bodyTokens) with
    ⟨stepNegationTrace, hstepNegationEndpoint, hstepNegationBounds⟩
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.empty.rows hnat.quantifiedStep.rows
      hnat.negatedQuantifiedStep.rows hnat.empty.rows hnat.empty.layout
      hnat.quantifiedStep.elements hnat.negatedQuantifiedStep.elements
      hnat.empty.elements hstates.quantifiedStepNegation
      hquantifiedStepNegationStateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform,
          compactGuardedInductionEmpty] using
        compactGuardedInductionNegatedQuantifiedStep_eq bodyTokens) with
    ⟨quantifiedStepNegationTrace, hquantifiedStepNegationEndpoint,
      hquantifiedStepNegationBounds⟩
  let coordinates : CompactSuccIndStepAssemblyRouteCoordinates :=
    { negatedStepZeroTrace := stepNegationTrace
      negatedQuantifiedStepTrace := quantifiedStepNegationTrace }
  have hroute : CompactSuccIndStepAssemblyRoute
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 5 data.empty) coordinates := by
    refine ⟨hstepEmpty, hstepSuccessorRows, ?_, hstepDisjunctionRows,
      hstepDisjunctionSlices, hquantifiedStepSlices, ?_,
      hquantifiedFinalRows, hquantifiedFinalSlices⟩
    · simpa [coordinates, hnat.empty.1, hnat.stepZero.1,
        hnat.negatedStepZero.1] using hstepNegationEndpoint
    · simpa [coordinates, hnat.empty.1, hnat.quantifiedStep.1,
        hnat.negatedQuantifiedStep.1] using
          hquantifiedStepNegationEndpoint
  refine ⟨coordinates, hroute, ?_, ?_⟩
  · simpa [coordinates] using hstepNegationBounds
  · simpa [coordinates] using hquantifiedStepNegationBounds


set_option maxHeartbeats 350000 in
private theorem exists_compactGuardedInductionFvSupRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∀ oldCoordinates : CompactFormulaFvSupTotalEndpointCoordinates,
      CompactFormulaFvSupTotalEndpoint tokenTable width tokens.length
          0 data.depth
          (compactPackedNatListSlot chunks 5 data.empty)
          (compactPackedNatListSlot chunks 20 data.sentence)
          (compactPackedNatListSlot chunks 21 data.fvarList)
          oldCoordinates →
      ∃ coordinates : CompactFormulaFvSupTotalEndpointCoordinates,
        CompactFormulaFvSupTotalEndpoint tokenTable width tokens.length
            0 data.depth
            (compactPackedNatListSlot chunks 5 data.empty)
            (compactPackedNatListSlot chunks 20 data.sentence)
            (compactPackedNatListSlot chunks 21 data.fvarList)
            coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.trace width tokens.length data.sentence := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∀ oldCoordinates : CompactFormulaFvSupTotalEndpointCoordinates,
    CompactFormulaFvSupTotalEndpoint tokenTable width tokens.length
        0 data.depth
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        oldCoordinates →
      ∃ coordinates : CompactFormulaFvSupTotalEndpointCoordinates,
        CompactFormulaFvSupTotalEndpoint tokenTable width tokens.length
            0 data.depth
            (compactPackedNatListSlot chunks 5 data.empty)
            (compactPackedNatListSlot chunks 20 data.sentence)
            (compactPackedNatListSlot chunks 21 data.fvarList)
            coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.trace width tokens.length data.sentence
  intro oldCoordinates holdRoute
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  rcases holdRoute with ⟨hfvarEmpty, _holdFvarEndpoint, hfvarMaximum⟩
  have hstateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 35
          (compactGuardedInductionTransformStates
            4 data.empty 0 data.sentence)) <=
        (compactSyntaxRunFuelBound data.sentence + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 35 4 0 data.empty data.sentence
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.empty.rows hnat.sentence.rows hnat.fvarList.rows hnat.empty.rows
      hnat.empty.layout hnat.sentence.elements hnat.fvarList.elements
      hnat.empty.elements hstates.fvarList hstateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform,
          compactGuardedInductionEmpty] using
        compactGuardedInductionFvarList_eq bodyTokens) with
    ⟨trace, hendpoint, hbounds⟩
  let coordinates : CompactFormulaFvSupTotalEndpointCoordinates :=
    { trace := trace }
  have hroute : CompactFormulaFvSupTotalEndpoint
      tokenTable width tokens.length 0 data.depth
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList) coordinates := by
    refine ⟨hfvarEmpty, ?_, hfvarMaximum⟩
    simpa [coordinates, hnat.empty.1, hnat.sentence.1,
      hnat.fvarList.1] using hendpoint
  refine ⟨coordinates, hroute, ?_⟩
  simpa [coordinates] using hbounds


set_option maxHeartbeats 350000 in
private theorem exists_compactGuardedInductionClosureRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∀ oldCoordinates : CompactFixedAllClosureTotalEndpointCoordinates,
      CompactFixedAllClosureTotalEndpoint tokenTable width tokens.length
          data.depth
          (compactPackedNatListSlot chunks 5 data.empty)
          (compactPackedNatListSlot chunks 22 data.depthCapture)
          (compactPackedNatListSlot chunks 20 data.sentence)
          (compactPackedNatListSlot chunks 23 data.fixed)
          (compactPackedNatListSlot chunks 24 data.generated)
          oldCoordinates →
      ∃ coordinates : CompactFixedAllClosureTotalEndpointCoordinates,
        CompactFixedAllClosureTotalEndpoint tokenTable width tokens.length
            data.depth
            (compactPackedNatListSlot chunks 5 data.empty)
            (compactPackedNatListSlot chunks 22 data.depthCapture)
            (compactPackedNatListSlot chunks 20 data.sentence)
            (compactPackedNatListSlot chunks 23 data.fixed)
            (compactPackedNatListSlot chunks 24 data.generated)
            coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.trace width tokens.length data.sentence := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∀ oldCoordinates : CompactFixedAllClosureTotalEndpointCoordinates,
    CompactFixedAllClosureTotalEndpoint tokenTable width tokens.length
        data.depth
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated)
        oldCoordinates →
      ∃ coordinates : CompactFixedAllClosureTotalEndpointCoordinates,
        CompactFixedAllClosureTotalEndpoint tokenTable width tokens.length
            data.depth
            (compactPackedNatListSlot chunks 5 data.empty)
            (compactPackedNatListSlot chunks 22 data.depthCapture)
            (compactPackedNatListSlot chunks 20 data.sentence)
            (compactPackedNatListSlot chunks 23 data.fixed)
            (compactPackedNatListSlot chunks 24 data.generated)
            coordinates /\
          CompactFormulaTransformTraceCanonicalNumericBounds
            coordinates.trace width tokens.length data.sentence
  intro oldCoordinates holdRoute
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have hstates : CompactGuardedInductionPackedStateRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedStateRows_canonical data extraChunks
  rcases holdRoute with
    ⟨hclosureEmpty, hdepthCaptureCount, _holdClosureEndpoint,
      hgeneratedRows, hclosureSlices⟩
  have hstateSize :
      Nat.size (compactPackedFormulaTransformStateBoundary chunks 36
          (compactGuardedInductionTransformStates
            5 data.depthCapture 0 data.sentence)) <=
        (compactSyntaxRunFuelBound data.sentence + 2) * tokens.length := by
    simpa only [tokens, compactGuardedInductionTransformStates] using
      compactPackedFormulaTransformStateBoundary_size_le
        chunks 36 5 0 data.depthCapture data.sentence
          (by simp [chunks, compactGuardedInductionRouteChunks,
            compactGuardedInductionTransformStates])
          (by rfl)
  rcases exists_compactFormulaTransformTotalExactEndpoint_with_numericBounds
      hnat.depthCapture.rows hnat.sentence.rows hnat.fixed.rows hnat.empty.rows
      hnat.depthCapture.layout hnat.sentence.elements hnat.fixed.elements
      hnat.empty.elements hstates.closure hstateSize
      (by simpa only [data, compactGuardedInductionExecutableData,
          compactGuardedInductionExactTransform] using
        compactGuardedInductionFixed_eq bodyTokens) with
    ⟨trace, hendpoint, hbounds⟩
  let coordinates : CompactFixedAllClosureTotalEndpointCoordinates :=
    { trace := trace }
  have hroute : CompactFixedAllClosureTotalEndpoint
      tokenTable width tokens.length data.depth
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated) coordinates := by
    refine ⟨hclosureEmpty, hdepthCaptureCount, ?_, hgeneratedRows,
      hclosureSlices⟩
    simpa [coordinates, hnat.depthCapture.1, hnat.sentence.1,
      hnat.fixed.1] using hendpoint
  refine ⟨coordinates, hroute, ?_⟩
  simpa [coordinates] using hbounds


set_option maxHeartbeats 20000 in
private theorem
    exists_compactGuardedInductionSentenceRoute_with_numericBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    ∃ route : CompactGuardedInductionSentenceRouteCoordinates,
      CompactGuardedInductionSentenceRoute
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated)
        route /\
      CompactGuardedInductionSentenceRouteCanonicalNumericBounds
        width tokens.length chunks data route := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  change ∃ route : CompactGuardedInductionSentenceRouteCoordinates,
    CompactGuardedInductionSentenceRoute
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated)
        route /\
      CompactGuardedInductionSentenceRouteCanonicalNumericBounds
        width tokens.length chunks data route
  rcases exists_compactGuardedInductionSentenceRoute_of_executable_body
      bodyTokens extraChunks with ⟨oldRoute, holdRoute⟩
  change CompactGuardedInductionSentenceRoute
      tokenTable width tokens.length data.depth
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated)
      oldRoute at holdRoute
  rcases holdRoute with ⟨holdSentence, holdFvSup, holdClosure⟩
  rcases holdSentence with
    ⟨holdBase, hopenZeroLiteral, holdOpenZero, hopenSuccessorLiteral,
      holdOpenSuccessor, holdStep, holdOuter⟩
  rcases exists_compactGuardedInductionBaseRoute_with_numericBounds
      bodyTokens extraChunks oldRoute.sentence.base holdBase with
    ⟨baseCoordinates, hbaseRoute, hbaseBounds, hbaseNegationBounds⟩
  rcases exists_compactGuardedInductionOpenZeroRoute_with_numericBounds
      bodyTokens extraChunks oldRoute.sentence.openZero holdOpenZero with
    ⟨openZeroCoordinates, hopenZeroRoute, hopenZeroShifted,
      hopenZeroSubstituted, hopenZeroShiftBounds,
      hopenZeroSubstitutionBounds, hopenZeroFixitrBounds⟩
  rcases
      exists_compactGuardedInductionOpenSuccessorRoute_with_numericBounds
        bodyTokens extraChunks oldRoute.sentence.openSuccessor
          holdOpenSuccessor with
    ⟨openSuccessorCoordinates, hopenSuccessorRoute,
      hopenSuccessorShifted, hopenSuccessorSubstituted,
      hopenSuccessorShiftBounds, hopenSuccessorSubstitutionBounds,
      hopenSuccessorFixitrBounds⟩
  rcases exists_compactGuardedInductionStepRoute_with_numericBounds
      bodyTokens extraChunks oldRoute.sentence.step holdStep with
    ⟨stepCoordinates, hstepRoute, hstepNegationBounds,
      hquantifiedStepNegationBounds⟩
  rcases exists_compactGuardedInductionFvSupRoute_with_numericBounds
      bodyTokens extraChunks oldRoute.fvSup holdFvSup with
    ⟨fvSupCoordinates, hfvarRoute, hfvarListBounds⟩
  rcases exists_compactGuardedInductionClosureRoute_with_numericBounds
      bodyTokens extraChunks oldRoute.closure holdClosure with
    ⟨closureCoordinates, hclosureRoute, hclosureBounds⟩
  let sentenceCoordinates : CompactSuccIndSentenceRouteCoordinates :=
    { base := baseCoordinates
      openZero := openZeroCoordinates
      openSuccessor := openSuccessorCoordinates
      step := stepCoordinates }
  let route : CompactGuardedInductionSentenceRouteCoordinates :=
    { sentence := sentenceCoordinates
      fvSup := fvSupCoordinates
      closure := closureCoordinates }
  have hsentenceRoute : CompactSuccIndSentenceRoute
      tokenTable width tokens.length
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      sentenceCoordinates := by
    exact ⟨hbaseRoute, hopenZeroLiteral, hopenZeroRoute,
      hopenSuccessorLiteral, hopenSuccessorRoute, hstepRoute, holdOuter⟩
  have hroute : CompactGuardedInductionSentenceRoute
      tokenTable width tokens.length data.depth
      (compactPackedNatListSlot chunks 0 data.body)
      (compactPackedNatListSlot chunks 1 data.zeroWitness)
      (compactPackedNatListSlot chunks 2 data.openZeroWitness)
      (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
      (compactPackedNatListSlot chunks 4 data.captureOne)
      (compactPackedNatListSlot chunks 5 data.empty)
      (compactPackedNatListSlot chunks 6 data.base)
      (compactPackedNatListSlot chunks 7 data.negatedBase)
      (compactPackedNatListSlot chunks 10 data.stepZero)
      (compactPackedNatListSlot chunks 13 data.stepSuccessor)
      (compactPackedNatListSlot chunks 14 data.negatedStepZero)
      (compactPackedNatListSlot chunks 15 data.stepDisjunction)
      (compactPackedNatListSlot chunks 16 data.quantifiedStep)
      (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
      (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
      (compactPackedNatListSlot chunks 19 data.innerDisjunction)
      (compactPackedNatListSlot chunks 20 data.sentence)
      (compactPackedNatListSlot chunks 21 data.fvarList)
      (compactPackedNatListSlot chunks 22 data.depthCapture)
      (compactPackedNatListSlot chunks 23 data.fixed)
      (compactPackedNatListSlot chunks 24 data.generated) route := by
    exact ⟨hsentenceRoute, hfvarRoute, hclosureRoute⟩
  refine ⟨route, hroute, ?_⟩
  exact
    { openZeroShifted := by
        simpa only [route, sentenceCoordinates] using hopenZeroShifted
      openZeroSubstituted := by
        simpa only [route, sentenceCoordinates] using hopenZeroSubstituted
      openSuccessorShifted := by
        simpa only [route, sentenceCoordinates] using hopenSuccessorShifted
      openSuccessorSubstituted := by
        simpa only [route, sentenceCoordinates] using hopenSuccessorSubstituted
      base := by
        simpa only [route, sentenceCoordinates] using hbaseBounds
      baseNegation := by
        simpa only [route, sentenceCoordinates] using
          hbaseNegationBounds
      openZeroShift := by
        simpa only [route, sentenceCoordinates] using
          hopenZeroShiftBounds
      openZeroSubstitution := by
        simpa only [route, sentenceCoordinates] using
          hopenZeroSubstitutionBounds
      openZeroFixitr := by
        simpa only [route, sentenceCoordinates] using
          hopenZeroFixitrBounds
      openSuccessorShift := by
        simpa only [route, sentenceCoordinates] using
          hopenSuccessorShiftBounds
      openSuccessorSubstitution := by
        simpa only [route, sentenceCoordinates] using
          hopenSuccessorSubstitutionBounds
      openSuccessorFixitr := by
        simpa only [route, sentenceCoordinates] using
          hopenSuccessorFixitrBounds
      stepNegation := by
        simpa only [route, sentenceCoordinates] using
          hstepNegationBounds
      quantifiedStepNegation := by
        simpa only [route, sentenceCoordinates] using
          hquantifiedStepNegationBounds
      fvarList := by
        simpa only [route] using hfvarListBounds
      closure := by
        simpa only [route] using hclosureBounds }


structure CompactGuardedInductionSentenceRoutePublicCoordinateBounds
    (tokenTable width tokenCount depth : Nat)
    (body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero stepDisjunction
      quantifiedStep negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence fvarList depthCapture fixed generated : CompactNatListRowSlot)
    (route : CompactGuardedInductionSentenceRouteCoordinates)
    (bound : Nat) : Prop where
  tokenTable : Nat.size tokenTable <= bound
  width : Nat.size width <= bound
  tokenCount : Nat.size tokenCount <= bound
  depth : Nat.size depth <= bound
  body : CompactNatListRowSlotPublicCoordinateBounds body bound
  zeroWitness : CompactNatListRowSlotPublicCoordinateBounds zeroWitness bound
  openZeroWitness : CompactNatListRowSlotPublicCoordinateBounds
    openZeroWitness bound
  openSuccessorWitness : CompactNatListRowSlotPublicCoordinateBounds
    openSuccessorWitness bound
  captureOne : CompactNatListRowSlotPublicCoordinateBounds captureOne bound
  empty : CompactNatListRowSlotPublicCoordinateBounds empty bound
  base : CompactNatListRowSlotPublicCoordinateBounds base bound
  negatedBase : CompactNatListRowSlotPublicCoordinateBounds negatedBase bound
  stepZero : CompactNatListRowSlotPublicCoordinateBounds stepZero bound
  stepSuccessor : CompactNatListRowSlotPublicCoordinateBounds
    stepSuccessor bound
  negatedStepZero : CompactNatListRowSlotPublicCoordinateBounds
    negatedStepZero bound
  stepDisjunction : CompactNatListRowSlotPublicCoordinateBounds
    stepDisjunction bound
  quantifiedStep : CompactNatListRowSlotPublicCoordinateBounds
    quantifiedStep bound
  negatedQuantifiedStep : CompactNatListRowSlotPublicCoordinateBounds
    negatedQuantifiedStep bound
  quantifiedFinal : CompactNatListRowSlotPublicCoordinateBounds
    quantifiedFinal bound
  innerDisjunction : CompactNatListRowSlotPublicCoordinateBounds
    innerDisjunction bound
  sentence : CompactNatListRowSlotPublicCoordinateBounds sentence bound
  fvarList : CompactNatListRowSlotPublicCoordinateBounds fvarList bound
  depthCapture : CompactNatListRowSlotPublicCoordinateBounds depthCapture bound
  fixed : CompactNatListRowSlotPublicCoordinateBounds fixed bound
  generated : CompactNatListRowSlotPublicCoordinateBounds generated bound
  openZeroShifted : CompactNatListRowSlotPublicCoordinateBounds
    route.sentence.openZero.shifted bound
  openZeroSubstituted : CompactNatListRowSlotPublicCoordinateBounds
    route.sentence.openZero.substituted bound
  openSuccessorShifted : CompactNatListRowSlotPublicCoordinateBounds
    route.sentence.openSuccessor.shifted bound
  openSuccessorSubstituted : CompactNatListRowSlotPublicCoordinateBounds
    route.sentence.openSuccessor.substituted bound
  baseTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.base.baseTrace bound
  baseNegationTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.base.negationTrace bound
  openZeroShiftTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.openZero.shiftTrace bound
  openZeroSubstitutionTrace :
    CompactFormulaTransformTracePublicCoordinateBounds
      route.sentence.openZero.substitutionTrace bound
  openZeroFixitrTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.openZero.fixitrTrace bound
  openSuccessorShiftTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.openSuccessor.shiftTrace bound
  openSuccessorSubstitutionTrace :
    CompactFormulaTransformTracePublicCoordinateBounds
      route.sentence.openSuccessor.substitutionTrace bound
  openSuccessorFixitrTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.openSuccessor.fixitrTrace bound
  stepNegationTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.sentence.step.negatedStepZeroTrace bound
  quantifiedStepNegationTrace :
    CompactFormulaTransformTracePublicCoordinateBounds
      route.sentence.step.negatedQuantifiedStepTrace bound
  fvarListTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.fvSup.trace bound
  closureTrace : CompactFormulaTransformTracePublicCoordinateBounds
    route.closure.trace bound

private theorem boundedNatSizeSubtypeValue_vecCons
    {n bound : Nat}
    (head : { value : Nat // Nat.size value <= bound })
    (tail : Fin n -> { value : Nat // Nat.size value <= bound }) :
    (fun coordinate => ((Matrix.vecCons head tail) coordinate).1) =
      Matrix.vecCons head.1 (fun coordinate => (tail coordinate).1) := by
  funext coordinate
  exact Fin.cases rfl (fun _ => rfl) coordinate

private theorem boundedNatSizeSubtypeValue_vecEmpty
    {bound : Nat} :
    (fun coordinate =>
      ((![] : Fin 0 -> { value : Nat // Nat.size value <= bound })
        coordinate).1) =
      (![] : Fin 0 -> Nat) := by
  funext coordinate
  exact Fin.elim0 coordinate

set_option maxHeartbeats 200000 in
set_option maxRecDepth 4096 in
theorem compactGuardedInductionSentenceRouteEnvironment_size_le
    {tokenTable width tokenCount depth : Nat}
    {body zeroWitness openZeroWitness openSuccessorWitness captureOne empty
      base negatedBase stepZero stepSuccessor negatedStepZero stepDisjunction
      quantifiedStep negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence fvarList depthCapture fixed generated : CompactNatListRowSlot}
    {route : CompactGuardedInductionSentenceRouteCoordinates}
    {bound : Nat}
    (hbounds : CompactGuardedInductionSentenceRoutePublicCoordinateBounds
      tokenTable width tokenCount depth body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence fvarList
      depthCapture fixed generated route bound)
    (coordinate : Fin 177) :
    Nat.size (compactGuardedInductionSentenceRouteEnvironment
      tokenTable width tokenCount depth body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence fvarList
      depthCapture fixed generated route coordinate) <= bound := by
  let boundedEnvironment :
      Fin 177 -> { value : Nat // Nat.size value <= bound } :=
    ![⟨tokenTable, hbounds.tokenTable⟩,
      ⟨width, hbounds.width⟩,
      ⟨tokenCount, hbounds.tokenCount⟩,
      ⟨body.start, hbounds.body.start⟩,
      ⟨body.finish, hbounds.body.finish⟩,
      ⟨body.boundary, hbounds.body.boundary⟩,
      ⟨body.count, hbounds.body.count⟩,
      ⟨body.boundarySize, hbounds.body.boundarySize⟩,
      ⟨zeroWitness.start, hbounds.zeroWitness.start⟩,
      ⟨zeroWitness.finish, hbounds.zeroWitness.finish⟩,
      ⟨zeroWitness.boundary, hbounds.zeroWitness.boundary⟩,
      ⟨zeroWitness.count, hbounds.zeroWitness.count⟩,
      ⟨zeroWitness.boundarySize, hbounds.zeroWitness.boundarySize⟩,
      ⟨openZeroWitness.start, hbounds.openZeroWitness.start⟩,
      ⟨openZeroWitness.finish, hbounds.openZeroWitness.finish⟩,
      ⟨openZeroWitness.boundary, hbounds.openZeroWitness.boundary⟩,
      ⟨openZeroWitness.count, hbounds.openZeroWitness.count⟩,
      ⟨openZeroWitness.boundarySize,
        hbounds.openZeroWitness.boundarySize⟩,
      ⟨openSuccessorWitness.start, hbounds.openSuccessorWitness.start⟩,
      ⟨openSuccessorWitness.finish, hbounds.openSuccessorWitness.finish⟩,
      ⟨openSuccessorWitness.boundary,
        hbounds.openSuccessorWitness.boundary⟩,
      ⟨openSuccessorWitness.count, hbounds.openSuccessorWitness.count⟩,
      ⟨openSuccessorWitness.boundarySize,
        hbounds.openSuccessorWitness.boundarySize⟩,
      ⟨captureOne.start, hbounds.captureOne.start⟩,
      ⟨captureOne.finish, hbounds.captureOne.finish⟩,
      ⟨captureOne.boundary, hbounds.captureOne.boundary⟩,
      ⟨captureOne.count, hbounds.captureOne.count⟩,
      ⟨captureOne.boundarySize, hbounds.captureOne.boundarySize⟩,
      ⟨empty.start, hbounds.empty.start⟩,
      ⟨empty.finish, hbounds.empty.finish⟩,
      ⟨empty.boundary, hbounds.empty.boundary⟩,
      ⟨empty.count, hbounds.empty.count⟩,
      ⟨empty.boundarySize, hbounds.empty.boundarySize⟩,
      ⟨base.start, hbounds.base.start⟩,
      ⟨base.finish, hbounds.base.finish⟩,
      ⟨base.boundary, hbounds.base.boundary⟩,
      ⟨base.count, hbounds.base.count⟩,
      ⟨base.boundarySize, hbounds.base.boundarySize⟩,
      ⟨negatedBase.start, hbounds.negatedBase.start⟩,
      ⟨negatedBase.finish, hbounds.negatedBase.finish⟩,
      ⟨negatedBase.boundary, hbounds.negatedBase.boundary⟩,
      ⟨negatedBase.count, hbounds.negatedBase.count⟩,
      ⟨negatedBase.boundarySize, hbounds.negatedBase.boundarySize⟩,
      ⟨stepZero.start, hbounds.stepZero.start⟩,
      ⟨stepZero.finish, hbounds.stepZero.finish⟩,
      ⟨stepZero.boundary, hbounds.stepZero.boundary⟩,
      ⟨stepZero.count, hbounds.stepZero.count⟩,
      ⟨stepZero.boundarySize, hbounds.stepZero.boundarySize⟩,
      ⟨stepSuccessor.start, hbounds.stepSuccessor.start⟩,
      ⟨stepSuccessor.finish, hbounds.stepSuccessor.finish⟩,
      ⟨stepSuccessor.boundary, hbounds.stepSuccessor.boundary⟩,
      ⟨stepSuccessor.count, hbounds.stepSuccessor.count⟩,
      ⟨stepSuccessor.boundarySize, hbounds.stepSuccessor.boundarySize⟩,
      ⟨negatedStepZero.start, hbounds.negatedStepZero.start⟩,
      ⟨negatedStepZero.finish, hbounds.negatedStepZero.finish⟩,
      ⟨negatedStepZero.boundary, hbounds.negatedStepZero.boundary⟩,
      ⟨negatedStepZero.count, hbounds.negatedStepZero.count⟩,
      ⟨negatedStepZero.boundarySize,
        hbounds.negatedStepZero.boundarySize⟩,
      ⟨stepDisjunction.start, hbounds.stepDisjunction.start⟩,
      ⟨stepDisjunction.finish, hbounds.stepDisjunction.finish⟩,
      ⟨stepDisjunction.boundary, hbounds.stepDisjunction.boundary⟩,
      ⟨stepDisjunction.count, hbounds.stepDisjunction.count⟩,
      ⟨stepDisjunction.boundarySize,
        hbounds.stepDisjunction.boundarySize⟩,
      ⟨quantifiedStep.start, hbounds.quantifiedStep.start⟩,
      ⟨quantifiedStep.finish, hbounds.quantifiedStep.finish⟩,
      ⟨quantifiedStep.boundary, hbounds.quantifiedStep.boundary⟩,
      ⟨quantifiedStep.count, hbounds.quantifiedStep.count⟩,
      ⟨quantifiedStep.boundarySize, hbounds.quantifiedStep.boundarySize⟩,
      ⟨negatedQuantifiedStep.start, hbounds.negatedQuantifiedStep.start⟩,
      ⟨negatedQuantifiedStep.finish,
        hbounds.negatedQuantifiedStep.finish⟩,
      ⟨negatedQuantifiedStep.boundary,
        hbounds.negatedQuantifiedStep.boundary⟩,
      ⟨negatedQuantifiedStep.count, hbounds.negatedQuantifiedStep.count⟩,
      ⟨negatedQuantifiedStep.boundarySize,
        hbounds.negatedQuantifiedStep.boundarySize⟩,
      ⟨quantifiedFinal.start, hbounds.quantifiedFinal.start⟩,
      ⟨quantifiedFinal.finish, hbounds.quantifiedFinal.finish⟩,
      ⟨quantifiedFinal.boundary, hbounds.quantifiedFinal.boundary⟩,
      ⟨quantifiedFinal.count, hbounds.quantifiedFinal.count⟩,
      ⟨quantifiedFinal.boundarySize,
        hbounds.quantifiedFinal.boundarySize⟩,
      ⟨innerDisjunction.start, hbounds.innerDisjunction.start⟩,
      ⟨innerDisjunction.finish, hbounds.innerDisjunction.finish⟩,
      ⟨innerDisjunction.boundary, hbounds.innerDisjunction.boundary⟩,
      ⟨innerDisjunction.count, hbounds.innerDisjunction.count⟩,
      ⟨innerDisjunction.boundarySize,
        hbounds.innerDisjunction.boundarySize⟩,
      ⟨sentence.start, hbounds.sentence.start⟩,
      ⟨sentence.finish, hbounds.sentence.finish⟩,
      ⟨sentence.boundary, hbounds.sentence.boundary⟩,
      ⟨sentence.count, hbounds.sentence.count⟩,
      ⟨sentence.boundarySize, hbounds.sentence.boundarySize⟩,
      ⟨route.sentence.base.baseTrace.stateBoundary,
        hbounds.baseTrace.stateBoundary⟩,
      ⟨route.sentence.base.baseTrace.stateCount,
        hbounds.baseTrace.stateCount⟩,
      ⟨route.sentence.base.baseTrace.tableWidth,
        hbounds.baseTrace.tableWidth⟩,
      ⟨route.sentence.base.baseTrace.valueBound,
        hbounds.baseTrace.valueBound⟩,
      ⟨route.sentence.base.negationTrace.stateBoundary,
        hbounds.baseNegationTrace.stateBoundary⟩,
      ⟨route.sentence.base.negationTrace.stateCount,
        hbounds.baseNegationTrace.stateCount⟩,
      ⟨route.sentence.base.negationTrace.tableWidth,
        hbounds.baseNegationTrace.tableWidth⟩,
      ⟨route.sentence.base.negationTrace.valueBound,
        hbounds.baseNegationTrace.valueBound⟩,
      ⟨route.sentence.openZero.shifted.start,
        hbounds.openZeroShifted.start⟩,
      ⟨route.sentence.openZero.shifted.finish,
        hbounds.openZeroShifted.finish⟩,
      ⟨route.sentence.openZero.shifted.boundary,
        hbounds.openZeroShifted.boundary⟩,
      ⟨route.sentence.openZero.shifted.count,
        hbounds.openZeroShifted.count⟩,
      ⟨route.sentence.openZero.shifted.boundarySize,
        hbounds.openZeroShifted.boundarySize⟩,
      ⟨route.sentence.openZero.substituted.start,
        hbounds.openZeroSubstituted.start⟩,
      ⟨route.sentence.openZero.substituted.finish,
        hbounds.openZeroSubstituted.finish⟩,
      ⟨route.sentence.openZero.substituted.boundary,
        hbounds.openZeroSubstituted.boundary⟩,
      ⟨route.sentence.openZero.substituted.count,
        hbounds.openZeroSubstituted.count⟩,
      ⟨route.sentence.openZero.substituted.boundarySize,
        hbounds.openZeroSubstituted.boundarySize⟩,
      ⟨route.sentence.openZero.shiftTrace.stateBoundary,
        hbounds.openZeroShiftTrace.stateBoundary⟩,
      ⟨route.sentence.openZero.shiftTrace.stateCount,
        hbounds.openZeroShiftTrace.stateCount⟩,
      ⟨route.sentence.openZero.shiftTrace.tableWidth,
        hbounds.openZeroShiftTrace.tableWidth⟩,
      ⟨route.sentence.openZero.shiftTrace.valueBound,
        hbounds.openZeroShiftTrace.valueBound⟩,
      ⟨route.sentence.openZero.substitutionTrace.stateBoundary,
        hbounds.openZeroSubstitutionTrace.stateBoundary⟩,
      ⟨route.sentence.openZero.substitutionTrace.stateCount,
        hbounds.openZeroSubstitutionTrace.stateCount⟩,
      ⟨route.sentence.openZero.substitutionTrace.tableWidth,
        hbounds.openZeroSubstitutionTrace.tableWidth⟩,
      ⟨route.sentence.openZero.substitutionTrace.valueBound,
        hbounds.openZeroSubstitutionTrace.valueBound⟩,
      ⟨route.sentence.openZero.fixitrTrace.stateBoundary,
        hbounds.openZeroFixitrTrace.stateBoundary⟩,
      ⟨route.sentence.openZero.fixitrTrace.stateCount,
        hbounds.openZeroFixitrTrace.stateCount⟩,
      ⟨route.sentence.openZero.fixitrTrace.tableWidth,
        hbounds.openZeroFixitrTrace.tableWidth⟩,
      ⟨route.sentence.openZero.fixitrTrace.valueBound,
        hbounds.openZeroFixitrTrace.valueBound⟩,
      ⟨route.sentence.openSuccessor.shifted.start,
        hbounds.openSuccessorShifted.start⟩,
      ⟨route.sentence.openSuccessor.shifted.finish,
        hbounds.openSuccessorShifted.finish⟩,
      ⟨route.sentence.openSuccessor.shifted.boundary,
        hbounds.openSuccessorShifted.boundary⟩,
      ⟨route.sentence.openSuccessor.shifted.count,
        hbounds.openSuccessorShifted.count⟩,
      ⟨route.sentence.openSuccessor.shifted.boundarySize,
        hbounds.openSuccessorShifted.boundarySize⟩,
      ⟨route.sentence.openSuccessor.substituted.start,
        hbounds.openSuccessorSubstituted.start⟩,
      ⟨route.sentence.openSuccessor.substituted.finish,
        hbounds.openSuccessorSubstituted.finish⟩,
      ⟨route.sentence.openSuccessor.substituted.boundary,
        hbounds.openSuccessorSubstituted.boundary⟩,
      ⟨route.sentence.openSuccessor.substituted.count,
        hbounds.openSuccessorSubstituted.count⟩,
      ⟨route.sentence.openSuccessor.substituted.boundarySize,
        hbounds.openSuccessorSubstituted.boundarySize⟩,
      ⟨route.sentence.openSuccessor.shiftTrace.stateBoundary,
        hbounds.openSuccessorShiftTrace.stateBoundary⟩,
      ⟨route.sentence.openSuccessor.shiftTrace.stateCount,
        hbounds.openSuccessorShiftTrace.stateCount⟩,
      ⟨route.sentence.openSuccessor.shiftTrace.tableWidth,
        hbounds.openSuccessorShiftTrace.tableWidth⟩,
      ⟨route.sentence.openSuccessor.shiftTrace.valueBound,
        hbounds.openSuccessorShiftTrace.valueBound⟩,
      ⟨route.sentence.openSuccessor.substitutionTrace.stateBoundary,
        hbounds.openSuccessorSubstitutionTrace.stateBoundary⟩,
      ⟨route.sentence.openSuccessor.substitutionTrace.stateCount,
        hbounds.openSuccessorSubstitutionTrace.stateCount⟩,
      ⟨route.sentence.openSuccessor.substitutionTrace.tableWidth,
        hbounds.openSuccessorSubstitutionTrace.tableWidth⟩,
      ⟨route.sentence.openSuccessor.substitutionTrace.valueBound,
        hbounds.openSuccessorSubstitutionTrace.valueBound⟩,
      ⟨route.sentence.openSuccessor.fixitrTrace.stateBoundary,
        hbounds.openSuccessorFixitrTrace.stateBoundary⟩,
      ⟨route.sentence.openSuccessor.fixitrTrace.stateCount,
        hbounds.openSuccessorFixitrTrace.stateCount⟩,
      ⟨route.sentence.openSuccessor.fixitrTrace.tableWidth,
        hbounds.openSuccessorFixitrTrace.tableWidth⟩,
      ⟨route.sentence.openSuccessor.fixitrTrace.valueBound,
        hbounds.openSuccessorFixitrTrace.valueBound⟩,
      ⟨route.sentence.step.negatedStepZeroTrace.stateBoundary,
        hbounds.stepNegationTrace.stateBoundary⟩,
      ⟨route.sentence.step.negatedStepZeroTrace.stateCount,
        hbounds.stepNegationTrace.stateCount⟩,
      ⟨route.sentence.step.negatedStepZeroTrace.tableWidth,
        hbounds.stepNegationTrace.tableWidth⟩,
      ⟨route.sentence.step.negatedStepZeroTrace.valueBound,
        hbounds.stepNegationTrace.valueBound⟩,
      ⟨route.sentence.step.negatedQuantifiedStepTrace.stateBoundary,
        hbounds.quantifiedStepNegationTrace.stateBoundary⟩,
      ⟨route.sentence.step.negatedQuantifiedStepTrace.stateCount,
        hbounds.quantifiedStepNegationTrace.stateCount⟩,
      ⟨route.sentence.step.negatedQuantifiedStepTrace.tableWidth,
        hbounds.quantifiedStepNegationTrace.tableWidth⟩,
      ⟨route.sentence.step.negatedQuantifiedStepTrace.valueBound,
        hbounds.quantifiedStepNegationTrace.valueBound⟩,
      ⟨depth, hbounds.depth⟩,
      ⟨fvarList.start, hbounds.fvarList.start⟩,
      ⟨fvarList.finish, hbounds.fvarList.finish⟩,
      ⟨fvarList.boundary, hbounds.fvarList.boundary⟩,
      ⟨fvarList.count, hbounds.fvarList.count⟩,
      ⟨fvarList.boundarySize, hbounds.fvarList.boundarySize⟩,
      ⟨depthCapture.start, hbounds.depthCapture.start⟩,
      ⟨depthCapture.finish, hbounds.depthCapture.finish⟩,
      ⟨depthCapture.boundary, hbounds.depthCapture.boundary⟩,
      ⟨depthCapture.count, hbounds.depthCapture.count⟩,
      ⟨depthCapture.boundarySize, hbounds.depthCapture.boundarySize⟩,
      ⟨fixed.start, hbounds.fixed.start⟩,
      ⟨fixed.finish, hbounds.fixed.finish⟩,
      ⟨fixed.boundary, hbounds.fixed.boundary⟩,
      ⟨fixed.count, hbounds.fixed.count⟩,
      ⟨fixed.boundarySize, hbounds.fixed.boundarySize⟩,
      ⟨generated.start, hbounds.generated.start⟩,
      ⟨generated.finish, hbounds.generated.finish⟩,
      ⟨generated.boundary, hbounds.generated.boundary⟩,
      ⟨generated.count, hbounds.generated.count⟩,
      ⟨generated.boundarySize, hbounds.generated.boundarySize⟩,
      ⟨route.fvSup.trace.stateBoundary,
        hbounds.fvarListTrace.stateBoundary⟩,
      ⟨route.fvSup.trace.stateCount, hbounds.fvarListTrace.stateCount⟩,
      ⟨route.fvSup.trace.tableWidth, hbounds.fvarListTrace.tableWidth⟩,
      ⟨route.fvSup.trace.valueBound, hbounds.fvarListTrace.valueBound⟩,
      ⟨route.closure.trace.stateBoundary,
        hbounds.closureTrace.stateBoundary⟩,
      ⟨route.closure.trace.stateCount, hbounds.closureTrace.stateCount⟩,
      ⟨route.closure.trace.tableWidth, hbounds.closureTrace.tableWidth⟩,
      ⟨route.closure.trace.valueBound, hbounds.closureTrace.valueBound⟩]
  have hvalue :
      compactGuardedInductionSentenceRouteEnvironment
          tokenTable width tokenCount depth body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed generated route coordinate =
        (boundedEnvironment coordinate).1 := by
    have hprojection :
        (fun coordinate => (boundedEnvironment coordinate).1) =
          compactGuardedInductionSentenceRouteEnvironment
            tokenTable width tokenCount depth body zeroWitness openZeroWitness
            openSuccessorWitness captureOne empty base negatedBase stepZero
            stepSuccessor negatedStepZero stepDisjunction quantifiedStep
            negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
            fvarList depthCapture fixed generated route := by
      unfold boundedEnvironment
        compactGuardedInductionSentenceRouteEnvironment
      simp only [boundedNatSizeSubtypeValue_vecCons,
        boundedNatSizeSubtypeValue_vecEmpty]
    exact (congrArg (fun environment => environment coordinate)
      hprojection).symm
  rw [hvalue]
  exact (boundedEnvironment coordinate).2


set_option maxHeartbeats 1200000 in
private theorem
    exists_compactGuardedInductionSentenceRoute_with_publicCoordinateBounds
    (bodyTokens : List Nat) (extraChunks : List (List Nat)) :
    let data := compactGuardedInductionExecutableData bodyTokens
    let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
    let tokens := chunks.flatten
    let width := (compactBinaryNatPayloadBits tokens).length
    let tokenTable := compactFixedWidthTableCode width tokens
    let ruleInputWeight := compactAdditiveTokenWeight tokens
    ∃ route : CompactGuardedInductionSentenceRouteCoordinates,
      CompactGuardedInductionSentenceRoute
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated) route /\
      CompactGuardedInductionSentenceRoutePublicCoordinateBounds
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated) route
        (compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
          ruleInputWeight) := by
  let data := compactGuardedInductionExecutableData bodyTokens
  let chunks := compactGuardedInductionRouteChunks data ++ extraChunks
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let ruleInputWeight := compactAdditiveTokenWeight tokens
  change ∃ route : CompactGuardedInductionSentenceRouteCoordinates,
    CompactGuardedInductionSentenceRoute
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated) route /\
      CompactGuardedInductionSentenceRoutePublicCoordinateBounds
        tokenTable width tokens.length data.depth
        (compactPackedNatListSlot chunks 0 data.body)
        (compactPackedNatListSlot chunks 1 data.zeroWitness)
        (compactPackedNatListSlot chunks 2 data.openZeroWitness)
        (compactPackedNatListSlot chunks 3 data.openSuccessorWitness)
        (compactPackedNatListSlot chunks 4 data.captureOne)
        (compactPackedNatListSlot chunks 5 data.empty)
        (compactPackedNatListSlot chunks 6 data.base)
        (compactPackedNatListSlot chunks 7 data.negatedBase)
        (compactPackedNatListSlot chunks 10 data.stepZero)
        (compactPackedNatListSlot chunks 13 data.stepSuccessor)
        (compactPackedNatListSlot chunks 14 data.negatedStepZero)
        (compactPackedNatListSlot chunks 15 data.stepDisjunction)
        (compactPackedNatListSlot chunks 16 data.quantifiedStep)
        (compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep)
        (compactPackedNatListSlot chunks 18 data.quantifiedFinal)
        (compactPackedNatListSlot chunks 19 data.innerDisjunction)
        (compactPackedNatListSlot chunks 20 data.sentence)
        (compactPackedNatListSlot chunks 21 data.fvarList)
        (compactPackedNatListSlot chunks 22 data.depthCapture)
        (compactPackedNatListSlot chunks 23 data.fixed)
        (compactPackedNatListSlot chunks 24 data.generated) route
        (compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
          ruleInputWeight)
  rcases exists_compactGuardedInductionSentenceRoute_with_numericBounds
      bodyTokens extraChunks with ⟨route, hroute, hnumeric⟩
  have hnat : CompactGuardedInductionPackedNatRows
      tokenTable width tokens.length chunks data := by
    simpa [chunks, tokens, width, tokenTable] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  have htokenCount : tokens.length <= ruleInputWeight := by
    exact compactAdditiveTokenList_length_le_weight tokens
  have hwidthValue : width <=
      compactNumericVerifierPAAxiomJointLeafRuleWidthBound ruleInputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    rfl
  have htable : Nat.size tokenTable <=
      compactNumericVerifierPAAxiomJointLeafRuleTableSizeBound
        ruleInputWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans (by
      unfold compactNumericVerifierPAAxiomJointLeafRuleTableSizeBound
      exact Nat.mul_le_mul htokenCount hwidthValue)
  let bound := compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    ruleInputWeight
  have htablePublic : Nat.size tokenTable <= bound := htable.trans (by
    dsimp only [bound]
    unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    omega)
  have hwidthPublic : Nat.size width <= bound :=
    (natSize_le_of_le hwidthValue).trans (by
      dsimp only [bound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have htokenCountPublic : Nat.size tokens.length <= bound :=
    (natSize_le_of_le htokenCount).trans (by
      dsimp only [bound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have hbody := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.body htokenCount
  have hzeroWitness := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.zeroWitness htokenCount
  have hopenZeroWitness :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.openZeroWitness htokenCount
  have hopenSuccessorWitness :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.openSuccessorWitness htokenCount
  have hcaptureOne := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.captureOne htokenCount
  have hempty := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.empty htokenCount
  have hbase := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.base htokenCount
  have hnegatedBase := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.negatedBase htokenCount
  have hopenZeroShiftedRaw :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.openZeroShifted htokenCount
  have hopenZeroSubstitutedRaw :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.openZeroSubstituted htokenCount
  have hstepZero := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.stepZero htokenCount
  have hopenSuccessorShiftedRaw :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.openSuccessorShifted htokenCount
  have hopenSuccessorSubstitutedRaw :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.openSuccessorSubstituted htokenCount
  have hstepSuccessor :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.stepSuccessor htokenCount
  have hnegatedStepZero :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.negatedStepZero htokenCount
  have hstepDisjunction :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.stepDisjunction htokenCount
  have hquantifiedStep :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.quantifiedStep htokenCount
  have hnegatedQuantifiedStep :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.negatedQuantifiedStep htokenCount
  have hquantifiedFinal :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.quantifiedFinal htokenCount
  have hinnerDisjunction :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.innerDisjunction htokenCount
  have hsentence := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.sentence htokenCount
  have hfvarList := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.fvarList htokenCount
  have hdepthCapture :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hnat.depthCapture htokenCount
  have hfixed := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.fixed htokenCount
  have hgenerated := CompactPackedNatListSlotCanonical.publicCoordinateBounds
    hnat.generated htokenCount
  have hdepthCaptureCount :
      (compactPackedNatListSlot chunks 22 data.depthCapture).count =
        data.depth := hroute.2.2.2.1
  have hdepth : Nat.size data.depth <= bound := by
    rw [← hdepthCaptureCount]
    exact hdepthCapture.count
  have hopenZeroShifted : CompactNatListRowSlotPublicCoordinateBounds
      route.sentence.openZero.shifted bound := by
    simpa only [bound, hnumeric.openZeroShifted] using
      hopenZeroShiftedRaw
  have hopenZeroSubstituted : CompactNatListRowSlotPublicCoordinateBounds
      route.sentence.openZero.substituted bound := by
    simpa only [bound, hnumeric.openZeroSubstituted] using
      hopenZeroSubstitutedRaw
  have hopenSuccessorShifted : CompactNatListRowSlotPublicCoordinateBounds
      route.sentence.openSuccessor.shifted bound := by
    simpa only [bound, hnumeric.openSuccessorShifted] using
      hopenSuccessorShiftedRaw
  have hopenSuccessorSubstituted : CompactNatListRowSlotPublicCoordinateBounds
      route.sentence.openSuccessor.substituted bound := by
    simpa only [bound, hnumeric.openSuccessorSubstituted] using
      hopenSuccessorSubstitutedRaw
  have inputWeight (values : List Nat)
      (hmem : compactAdditiveEncode values ∈ chunks) :
      compactAdditiveValueWeight values <= ruleInputWeight := by
    exact compactAdditiveValueWeight_le_flatten_of_mem chunks values hmem
  have hbodyWeight : compactAdditiveValueWeight data.body <= ruleInputWeight :=
    inputWeight data.body (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hbaseWeight : compactAdditiveValueWeight data.base <= ruleInputWeight :=
    inputWeight data.base (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hopenZeroShiftedWeight :
      compactAdditiveValueWeight data.openZeroShifted <= ruleInputWeight :=
    inputWeight data.openZeroShifted (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hopenZeroSubstitutedWeight :
      compactAdditiveValueWeight data.openZeroSubstituted <= ruleInputWeight :=
    inputWeight data.openZeroSubstituted (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hopenSuccessorShiftedWeight :
      compactAdditiveValueWeight data.openSuccessorShifted <= ruleInputWeight :=
    inputWeight data.openSuccessorShifted (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hopenSuccessorSubstitutedWeight :
      compactAdditiveValueWeight data.openSuccessorSubstituted <=
        ruleInputWeight :=
    inputWeight data.openSuccessorSubstituted (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hstepZeroWeight :
      compactAdditiveValueWeight data.stepZero <= ruleInputWeight :=
    inputWeight data.stepZero (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hquantifiedStepWeight :
      compactAdditiveValueWeight data.quantifiedStep <= ruleInputWeight :=
    inputWeight data.quantifiedStep (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hsentenceWeight :
      compactAdditiveValueWeight data.sentence <= ruleInputWeight :=
    inputWeight data.sentence (by
      simp [chunks, compactGuardedInductionRouteChunks])
  have hbaseTrace := hnumeric.base.publicCoordinateBounds
    hwidthValue htokenCount hbodyWeight
  have hbaseNegationTrace := hnumeric.baseNegation.publicCoordinateBounds
    hwidthValue htokenCount hbaseWeight
  have hopenZeroShiftTrace := hnumeric.openZeroShift.publicCoordinateBounds
    hwidthValue htokenCount hbodyWeight
  have hopenZeroSubstitutionTrace :=
    hnumeric.openZeroSubstitution.publicCoordinateBounds
      hwidthValue htokenCount hopenZeroShiftedWeight
  have hopenZeroFixitrTrace :=
    hnumeric.openZeroFixitr.publicCoordinateBounds
      hwidthValue htokenCount hopenZeroSubstitutedWeight
  have hopenSuccessorShiftTrace :=
    hnumeric.openSuccessorShift.publicCoordinateBounds
      hwidthValue htokenCount hbodyWeight
  have hopenSuccessorSubstitutionTrace :=
    hnumeric.openSuccessorSubstitution.publicCoordinateBounds
      hwidthValue htokenCount hopenSuccessorShiftedWeight
  have hopenSuccessorFixitrTrace :=
    hnumeric.openSuccessorFixitr.publicCoordinateBounds
      hwidthValue htokenCount hopenSuccessorSubstitutedWeight
  have hstepNegationTrace := hnumeric.stepNegation.publicCoordinateBounds
    hwidthValue htokenCount hstepZeroWeight
  have hquantifiedStepNegationTrace :=
    hnumeric.quantifiedStepNegation.publicCoordinateBounds
      hwidthValue htokenCount hquantifiedStepWeight
  have hfvarListTrace := hnumeric.fvarList.publicCoordinateBounds
    hwidthValue htokenCount hsentenceWeight
  have hclosureTrace := hnumeric.closure.publicCoordinateBounds
    hwidthValue htokenCount hsentenceWeight
  refine ⟨route, hroute, ?_⟩
  exact
    { tokenTable := htablePublic
      width := hwidthPublic
      tokenCount := htokenCountPublic
      depth := hdepth
      body := hbody
      zeroWitness := hzeroWitness
      openZeroWitness := hopenZeroWitness
      openSuccessorWitness := hopenSuccessorWitness
      captureOne := hcaptureOne
      empty := hempty
      base := hbase
      negatedBase := hnegatedBase
      stepZero := hstepZero
      stepSuccessor := hstepSuccessor
      negatedStepZero := hnegatedStepZero
      stepDisjunction := hstepDisjunction
      quantifiedStep := hquantifiedStep
      negatedQuantifiedStep := hnegatedQuantifiedStep
      quantifiedFinal := hquantifiedFinal
      innerDisjunction := hinnerDisjunction
      sentence := hsentence
      fvarList := hfvarList
      depthCapture := hdepthCapture
      fixed := hfixed
      generated := hgenerated
      openZeroShifted := hopenZeroShifted
      openZeroSubstituted := hopenZeroSubstituted
      openSuccessorShifted := hopenSuccessorShifted
      openSuccessorSubstituted := hopenSuccessorSubstituted
      baseTrace := hbaseTrace
      baseNegationTrace := hbaseNegationTrace
      openZeroShiftTrace := hopenZeroShiftTrace
      openZeroSubstitutionTrace := hopenZeroSubstitutionTrace
      openZeroFixitrTrace := hopenZeroFixitrTrace
      openSuccessorShiftTrace := hopenSuccessorShiftTrace
      openSuccessorSubstitutionTrace := hopenSuccessorSubstitutionTrace
      openSuccessorFixitrTrace := hopenSuccessorFixitrTrace
      stepNegationTrace := hstepNegationTrace
      quantifiedStepNegationTrace := hquantifiedStepNegationTrace
      fvarListTrace := hfvarListTrace
      closureTrace := hclosureTrace }

private theorem inactiveRoute_publicCoordinateBounds
    {tokenTable width tokenCount ruleInputWeight : Nat}
    (htable : Nat.size tokenTable <=
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        ruleInputWeight)
    (hwidth : Nat.size width <=
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        ruleInputWeight)
    (htokenCount : Nat.size tokenCount <=
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        ruleInputWeight) :
    CompactGuardedInductionSentenceRoutePublicCoordinateBounds
      tokenTable width tokenCount 0
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveNatListRowSlot
      compactPAAxiomLeafInactiveRouteCoordinates
      (compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
        ruleInputWeight) := by
  let bound := compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    ruleInputWeight
  have hslot : CompactNatListRowSlotPublicCoordinateBounds
      compactPAAxiomLeafInactiveNatListRowSlot bound := by
    constructor <;> simp [compactPAAxiomLeafInactiveNatListRowSlot]
  have htrace : CompactFormulaTransformTracePublicCoordinateBounds
      compactPAAxiomLeafInactiveFormulaTransformTraceSlot bound := by
    constructor <;>
      simp [compactPAAxiomLeafInactiveFormulaTransformTraceSlot]
  exact
    { tokenTable := htable
      width := hwidth
      tokenCount := htokenCount
      depth := by simp
      body := hslot
      zeroWitness := hslot
      openZeroWitness := hslot
      openSuccessorWitness := hslot
      captureOne := hslot
      empty := hslot
      base := hslot
      negatedBase := hslot
      stepZero := hslot
      stepSuccessor := hslot
      negatedStepZero := hslot
      stepDisjunction := hslot
      quantifiedStep := hslot
      negatedQuantifiedStep := hslot
      quantifiedFinal := hslot
      innerDisjunction := hslot
      sentence := hslot
      fvarList := hslot
      depthCapture := hslot
      fixed := hslot
      generated := hslot
      openZeroShifted := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using hslot
      openZeroSubstituted := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using hslot
      openSuccessorShifted := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using hslot
      openSuccessorSubstituted := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using hslot
      baseTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      baseNegationTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      openZeroShiftTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      openZeroSubstitutionTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      openZeroFixitrTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      openSuccessorShiftTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      openSuccessorSubstitutionTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      openSuccessorFixitrTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      stepNegationTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      quantifiedStepNegationTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      fvarListTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace
      closureTrace := by
        simpa [compactPAAxiomLeafInactiveRouteCoordinates] using htrace }

theorem compactAdditiveInductionPAAxiomRuleCheckEnvironment_size_le
    {tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth bound : Nat}
    {axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated candidate :
      CompactNatListRowSlot}
    {route : CompactGuardedInductionSentenceRouteCoordinates}
    (hroute : CompactGuardedInductionSentenceRoutePublicCoordinateBounds
      tokenTable width tokenCount depth body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence fvarList
      depthCapture fixed generated route bound)
    (hgammaBoundary : Nat.size gammaBoundary <= bound)
    (hgammaCount : Nat.size gammaCount <= bound)
    (hresultBool : Nat.size resultBoolValue <= bound)
    (haxiomBoundary : Nat.size axiomTokens.boundary <= bound)
    (haxiomCount : Nat.size axiomTokens.count <= bound)
    (hcandidateStart : Nat.size candidate.start <= bound)
    (hcandidateFinish : Nat.size candidate.finish <= bound)
    (coordinate : Fin 184) :
    Nat.size (compactAdditiveInductionPAAxiomRuleCheckEnvironment
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth axiomTokens body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence fvarList
      depthCapture fixed generated candidate route coordinate) <= bound := by
  apply natSize_vecAppend_le rfl
  · exact compactGuardedInductionSentenceRouteEnvironment_size_le hroute
  · intro tailCoordinate
    fin_cases tailCoordinate <;>
      simp <;> assumption

structure CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
    (coordinates : CompactCertificateNodeFixedPAEndpointCoordinates)
    (bound : Nat) : Prop where
  inputBoundary : Nat.size coordinates.inputBoundary <= bound
  inputCount : Nat.size coordinates.inputCount <= bound
  inputBoundarySize : Nat.size coordinates.inputBoundarySize <= bound
  tailStart : Nat.size coordinates.tailStart <= bound
  tailFinish : Nat.size coordinates.tailFinish <= bound
  tailBoundary : Nat.size coordinates.tailBoundary <= bound
  tailCount : Nat.size coordinates.tailCount <= bound
  tailBoundarySize : Nat.size coordinates.tailBoundarySize <= bound
  axiomBoundary : Nat.size coordinates.axiomBoundary <= bound
  axiomCount : Nat.size coordinates.axiomCount <= bound
  axiomBoundarySize : Nat.size coordinates.axiomBoundarySize <= bound
  suffixBoundary : Nat.size coordinates.suffixBoundary <= bound
  suffixCount : Nat.size coordinates.suffixCount <= bound
  suffixBoundarySize : Nat.size coordinates.suffixBoundarySize <= bound
  paTag : Nat.size coordinates.paTag <= bound

structure CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
    (coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates)
    (bound : Nat) : Prop where
  inputBoundary : Nat.size coordinates.inputBoundary <= bound
  inputCount : Nat.size coordinates.inputCount <= bound
  inputBoundarySize : Nat.size coordinates.inputBoundarySize <= bound
  tailStart : Nat.size coordinates.tailStart <= bound
  tailFinish : Nat.size coordinates.tailFinish <= bound
  tailBoundary : Nat.size coordinates.tailBoundary <= bound
  tailCount : Nat.size coordinates.tailCount <= bound
  tailBoundarySize : Nat.size coordinates.tailBoundarySize <= bound
  axiomBoundary : Nat.size coordinates.axiomBoundary <= bound
  axiomCount : Nat.size coordinates.axiomCount <= bound
  axiomBoundarySize : Nat.size coordinates.axiomBoundarySize <= bound
  suffixBoundary : Nat.size coordinates.suffixBoundary <= bound
  suffixCount : Nat.size coordinates.suffixCount <= bound
  suffixBoundarySize : Nat.size coordinates.suffixBoundarySize <= bound
  paTag : Nat.size coordinates.paTag <= bound
  arity : Nat.size coordinates.arity <= bound
  symbolCode : Nat.size coordinates.symbolCode <= bound

structure CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
    (coordinates : CompactCertificateNodeInductionPAEndpointCoordinates)
    (bound : Nat) : Prop where
  inputBoundary : Nat.size coordinates.inputBoundary <= bound
  inputCount : Nat.size coordinates.inputCount <= bound
  inputBoundarySize : Nat.size coordinates.inputBoundarySize <= bound
  tailStart : Nat.size coordinates.tailStart <= bound
  tailFinish : Nat.size coordinates.tailFinish <= bound
  tailBoundary : Nat.size coordinates.tailBoundary <= bound
  tailCount : Nat.size coordinates.tailCount <= bound
  tailBoundarySize : Nat.size coordinates.tailBoundarySize <= bound
  axiomBoundary : Nat.size coordinates.axiomBoundary <= bound
  axiomCount : Nat.size coordinates.axiomCount <= bound
  axiomBoundarySize : Nat.size coordinates.axiomBoundarySize <= bound
  parserInputBoundary : Nat.size coordinates.parser.inputBoundary <= bound
  parserInputCount : Nat.size coordinates.parser.inputCount <= bound
  parserInputBoundarySize :
    Nat.size coordinates.parser.inputBoundarySize <= bound
  parserExpectedBoundary : Nat.size coordinates.parser.expectedBoundary <= bound
  parserExpectedCount : Nat.size coordinates.parser.expectedCount <= bound
  parserExpectedBoundarySize :
    Nat.size coordinates.parser.expectedBoundarySize <= bound
  parserStateBoundary : Nat.size coordinates.parser.stateBoundary <= bound
  parserStateCount : Nat.size coordinates.parser.stateCount <= bound
  parserTableWidth : Nat.size coordinates.parser.tableWidth <= bound
  parserValueBound : Nat.size coordinates.parser.valueBound <= bound

theorem CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds.mono
    {coordinates : CompactCertificateNodeFixedPAEndpointCoordinates}
    {left right : Nat}
    (hbounds : CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
      coordinates left)
    (h : left <= right) :
    CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
      coordinates right := by
  rcases hbounds with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14⟩
  exact ⟨h0.trans h, h1.trans h, h2.trans h, h3.trans h, h4.trans h,
    h5.trans h, h6.trans h, h7.trans h, h8.trans h, h9.trans h,
    h10.trans h, h11.trans h, h12.trans h, h13.trans h, h14.trans h⟩

theorem CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds.mono
    {coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates}
    {left right : Nat}
    (hbounds : CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
      coordinates left)
    (h : left <= right) :
    CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
      coordinates right := by
  rcases hbounds with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16⟩
  exact ⟨h0.trans h, h1.trans h, h2.trans h, h3.trans h, h4.trans h,
    h5.trans h, h6.trans h, h7.trans h, h8.trans h, h9.trans h,
    h10.trans h, h11.trans h, h12.trans h, h13.trans h, h14.trans h,
    h15.trans h, h16.trans h⟩

theorem CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds.mono
    {coordinates : CompactCertificateNodeInductionPAEndpointCoordinates}
    {left right : Nat}
    (hbounds : CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
      coordinates left)
    (h : left <= right) :
    CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
      coordinates right := by
  rcases hbounds with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
      h14, h15, h16, h17, h18, h19, h20⟩
  exact ⟨h0.trans h, h1.trans h, h2.trans h, h3.trans h, h4.trans h,
    h5.trans h, h6.trans h, h7.trans h, h8.trans h, h9.trans h,
    h10.trans h, h11.trans h, h12.trans h, h13.trans h, h14.trans h,
    h15.trans h, h16.trans h, h17.trans h, h18.trans h, h19.trans h,
    h20.trans h⟩

private theorem hiddenCoordinate_size_le
    {value endpointBound publicBound : Nat}
    (hvalue : value <= endpointBound)
    (hendpoint : Nat.size endpointBound <= publicBound) :
    Nat.size value <= publicBound :=
  (Nat.size_le_size hvalue).trans hendpoint

private theorem fixedEndpoint_of_boundedGraph
    {tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound publicBound : Nat}
    (hbounded : CompactCertificateNodeFixedPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound)
    (hpublic : CompactCertificateNodeFixedPAPublicCoordinateBounds
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound publicBound) :
    ∃ coordinates : CompactCertificateNodeFixedPAEndpointCoordinates,
      CompactCertificateNodeFixedPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates /\
      CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
        coordinates publicBound := by
  rcases hbounded with
    ⟨inputBoundary, hinputBoundary, inputCount, hinputCount,
      inputBoundarySize, hinputBoundarySize, tailStart, htailStart,
      tailFinish, htailFinish, tailBoundary, htailBoundary,
      tailCount, htailCount, tailBoundarySize, htailBoundarySize,
      axiomBoundary, haxiomBoundary, axiomCount, haxiomCount,
      axiomBoundarySize, haxiomBoundarySize, suffixBoundary,
      hsuffixBoundary, suffixCount, hsuffixCount, suffixBoundarySize,
      hsuffixBoundarySize, paTag, hpaTag, hgraph⟩
  let coordinates := compactCertificateNodeFixedPAEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize tailStart tailFinish
    tailBoundary tailCount tailBoundarySize axiomBoundary axiomCount
    axiomBoundarySize suffixBoundary suffixCount suffixBoundarySize paTag
  refine ⟨coordinates, hgraph, ?_⟩
  exact
    { inputBoundary := hiddenCoordinate_size_le hinputBoundary
        hpublic.endpointBound
      inputCount := hiddenCoordinate_size_le hinputCount hpublic.endpointBound
      inputBoundarySize := hiddenCoordinate_size_le hinputBoundarySize
        hpublic.endpointBound
      tailStart := hiddenCoordinate_size_le htailStart hpublic.endpointBound
      tailFinish := hiddenCoordinate_size_le htailFinish hpublic.endpointBound
      tailBoundary := hiddenCoordinate_size_le htailBoundary
        hpublic.endpointBound
      tailCount := hiddenCoordinate_size_le htailCount hpublic.endpointBound
      tailBoundarySize := hiddenCoordinate_size_le htailBoundarySize
        hpublic.endpointBound
      axiomBoundary := hiddenCoordinate_size_le haxiomBoundary
        hpublic.endpointBound
      axiomCount := hiddenCoordinate_size_le haxiomCount hpublic.endpointBound
      axiomBoundarySize := hiddenCoordinate_size_le haxiomBoundarySize
        hpublic.endpointBound
      suffixBoundary := hiddenCoordinate_size_le hsuffixBoundary
        hpublic.endpointBound
      suffixCount := hiddenCoordinate_size_le hsuffixCount hpublic.endpointBound
      suffixBoundarySize := hiddenCoordinate_size_le hsuffixBoundarySize
        hpublic.endpointBound
      paTag := hiddenCoordinate_size_le hpaTag hpublic.endpointBound }

private theorem symbolEndpoint_of_boundedGraph
    {tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound publicBound : Nat}
    (hbounded : CompactCertificateNodeSymbolPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound)
    (hpublic : CompactCertificateNodeSymbolPAPublicCoordinateBounds
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      suffixStart suffixFinish certificateTag endpointBound publicBound) :
    ∃ coordinates : CompactCertificateNodeSymbolPAEndpointCoordinates,
      CompactCertificateNodeSymbolPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish certificateTag coordinates /\
      CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
        coordinates publicBound := by
  rcases hbounded with
    ⟨inputBoundary, hinputBoundary, inputCount, hinputCount,
      inputBoundarySize, hinputBoundarySize, tailStart, htailStart,
      tailFinish, htailFinish, tailBoundary, htailBoundary,
      tailCount, htailCount, tailBoundarySize, htailBoundarySize,
      axiomBoundary, haxiomBoundary, axiomCount, haxiomCount,
      axiomBoundarySize, haxiomBoundarySize, suffixBoundary,
      hsuffixBoundary, suffixCount, hsuffixCount, suffixBoundarySize,
      hsuffixBoundarySize, paTag, hpaTag, arity, harity, symbolCode,
      hsymbolCode, hgraph⟩
  let coordinates := compactCertificateNodeSymbolPAEndpointCoordinatesOfValues
    inputBoundary inputCount inputBoundarySize tailStart tailFinish
    tailBoundary tailCount tailBoundarySize axiomBoundary axiomCount
    axiomBoundarySize suffixBoundary suffixCount suffixBoundarySize paTag arity
    symbolCode
  refine ⟨coordinates, hgraph, ?_⟩
  exact
    { inputBoundary := hiddenCoordinate_size_le hinputBoundary
        hpublic.endpointBound
      inputCount := hiddenCoordinate_size_le hinputCount hpublic.endpointBound
      inputBoundarySize := hiddenCoordinate_size_le hinputBoundarySize
        hpublic.endpointBound
      tailStart := hiddenCoordinate_size_le htailStart hpublic.endpointBound
      tailFinish := hiddenCoordinate_size_le htailFinish hpublic.endpointBound
      tailBoundary := hiddenCoordinate_size_le htailBoundary
        hpublic.endpointBound
      tailCount := hiddenCoordinate_size_le htailCount hpublic.endpointBound
      tailBoundarySize := hiddenCoordinate_size_le htailBoundarySize
        hpublic.endpointBound
      axiomBoundary := hiddenCoordinate_size_le haxiomBoundary
        hpublic.endpointBound
      axiomCount := hiddenCoordinate_size_le haxiomCount hpublic.endpointBound
      axiomBoundarySize := hiddenCoordinate_size_le haxiomBoundarySize
        hpublic.endpointBound
      suffixBoundary := hiddenCoordinate_size_le hsuffixBoundary
        hpublic.endpointBound
      suffixCount := hiddenCoordinate_size_le hsuffixCount hpublic.endpointBound
      suffixBoundarySize := hiddenCoordinate_size_le hsuffixBoundarySize
        hpublic.endpointBound
      paTag := hiddenCoordinate_size_le hpaTag hpublic.endpointBound
      arity := hiddenCoordinate_size_le harity hpublic.endpointBound
      symbolCode := hiddenCoordinate_size_le hsymbolCode hpublic.endpointBound }

private theorem inductionEndpoint_of_boundedGraph
    {tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      endpointBound publicBound : Nat}
    (hbounded : CompactCertificateNodeInductionPAEndpointBoundedGraph
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      endpointBound)
    (hpublic : CompactCertificateNodeInductionPAPublicCoordinateBounds
      tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
      formulaStart formulaFinish suffixStart suffixFinish certificateTag
      endpointBound publicBound) :
    ∃ coordinates : CompactCertificateNodeInductionPAEndpointCoordinates,
      CompactCertificateNodeInductionPAEndpointGraph
        tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        formulaStart formulaFinish suffixStart suffixFinish certificateTag
        coordinates /\
      CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
        coordinates publicBound := by
  rcases hbounded with
    ⟨inputBoundary, hinputBoundary, inputCount, hinputCount,
      inputBoundarySize, hinputBoundarySize, tailStart, htailStart,
      tailFinish, htailFinish, tailBoundary, htailBoundary,
      tailCount, htailCount, tailBoundarySize, htailBoundarySize,
      axiomBoundary, haxiomBoundary, axiomCount, haxiomCount,
      axiomBoundarySize, haxiomBoundarySize, formulaBoundary,
      hformulaBoundary, formulaCount, hformulaCount, formulaBoundarySize,
      hformulaBoundarySize, suffixBoundary, hsuffixBoundary, suffixCount,
      hsuffixCount, suffixBoundarySize, hsuffixBoundarySize, stateBoundary,
      hstateBoundary, stateCount, hstateCount, tableWidth, htableWidth,
      valueBound, hvalueBound, hgraph⟩
  let coordinates :=
    compactCertificateNodeInductionPAEndpointCoordinatesOfValues
      inputBoundary inputCount inputBoundarySize tailStart tailFinish
      tailBoundary tailCount tailBoundarySize axiomBoundary axiomCount
      axiomBoundarySize formulaBoundary formulaCount formulaBoundarySize
      suffixBoundary suffixCount suffixBoundarySize stateBoundary stateCount
      tableWidth valueBound
  refine ⟨coordinates, hgraph, ?_⟩
  exact
    { inputBoundary := hiddenCoordinate_size_le hinputBoundary
        hpublic.endpointBound
      inputCount := hiddenCoordinate_size_le hinputCount hpublic.endpointBound
      inputBoundarySize := hiddenCoordinate_size_le hinputBoundarySize
        hpublic.endpointBound
      tailStart := hiddenCoordinate_size_le htailStart hpublic.endpointBound
      tailFinish := hiddenCoordinate_size_le htailFinish hpublic.endpointBound
      tailBoundary := hiddenCoordinate_size_le htailBoundary
        hpublic.endpointBound
      tailCount := hiddenCoordinate_size_le htailCount hpublic.endpointBound
      tailBoundarySize := hiddenCoordinate_size_le htailBoundarySize
        hpublic.endpointBound
      axiomBoundary := hiddenCoordinate_size_le haxiomBoundary
        hpublic.endpointBound
      axiomCount := hiddenCoordinate_size_le haxiomCount hpublic.endpointBound
      axiomBoundarySize := hiddenCoordinate_size_le haxiomBoundarySize
        hpublic.endpointBound
      parserInputBoundary := hiddenCoordinate_size_le hformulaBoundary
        hpublic.endpointBound
      parserInputCount := hiddenCoordinate_size_le hformulaCount
        hpublic.endpointBound
      parserInputBoundarySize := hiddenCoordinate_size_le hformulaBoundarySize
        hpublic.endpointBound
      parserExpectedBoundary := hiddenCoordinate_size_le hsuffixBoundary
        hpublic.endpointBound
      parserExpectedCount := hiddenCoordinate_size_le hsuffixCount
        hpublic.endpointBound
      parserExpectedBoundarySize := hiddenCoordinate_size_le hsuffixBoundarySize
        hpublic.endpointBound
      parserStateBoundary := hiddenCoordinate_size_le hstateBoundary
        hpublic.endpointBound
      parserStateCount := hiddenCoordinate_size_le hstateCount
        hpublic.endpointBound
      parserTableWidth := hiddenCoordinate_size_le htableWidth
        hpublic.endpointBound
      parserValueBound := hiddenCoordinate_size_le hvalueBound
        hpublic.endpointBound }

private theorem inactiveFixedEndpoint_coordinateSizeBounds (bound : Nat) :
    CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
      compactPAAxiomJointInactiveFixedEndpoint bound := by
  constructor <;> simp [compactPAAxiomJointInactiveFixedEndpoint]

private theorem inactiveSymbolEndpoint_coordinateSizeBounds (bound : Nat) :
    CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
      compactPAAxiomJointInactiveSymbolEndpoint bound := by
  constructor <;> simp [compactPAAxiomJointInactiveSymbolEndpoint]

private theorem inactiveInductionEndpoint_coordinateSizeBounds (bound : Nat) :
    CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
      compactPAAxiomJointInactiveInductionEndpoint bound := by
  constructor <;> simp [compactPAAxiomJointInactiveInductionEndpoint]

def compactNumericVerifierPAAxiomJointLeafTailEnvironment
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates) : Fin 75 -> Nat :=
  ![c.endpointTable, c.endpointWidth, c.endpointTokenCount,
    c.inputStart, c.inputFinish, c.endpointAxiomStart,
    c.endpointAxiomFinish, c.formulaStart, c.formulaFinish,
    c.suffixStart, c.suffixFinish, c.proofTag, c.certificateTag,
    c.gammaStart, c.gammaFinish, c.gammaBoundarySize,
    c.candidate.boundary, c.candidate.count, c.candidate.boundarySize,
    c.ruleAxiom.start, c.ruleAxiom.finish, c.ruleAxiom.boundarySize,
    c.fixedEndpoint.inputBoundary, c.fixedEndpoint.inputCount,
    c.fixedEndpoint.inputBoundarySize, c.fixedEndpoint.tailStart,
    c.fixedEndpoint.tailFinish, c.fixedEndpoint.tailBoundary,
    c.fixedEndpoint.tailCount, c.fixedEndpoint.tailBoundarySize,
    c.fixedEndpoint.axiomBoundary, c.fixedEndpoint.axiomCount,
    c.fixedEndpoint.axiomBoundarySize, c.fixedEndpoint.suffixBoundary,
    c.fixedEndpoint.suffixCount, c.fixedEndpoint.suffixBoundarySize,
    c.fixedEndpoint.paTag,
    c.symbolEndpoint.inputBoundary, c.symbolEndpoint.inputCount,
    c.symbolEndpoint.inputBoundarySize, c.symbolEndpoint.tailStart,
    c.symbolEndpoint.tailFinish, c.symbolEndpoint.tailBoundary,
    c.symbolEndpoint.tailCount, c.symbolEndpoint.tailBoundarySize,
    c.symbolEndpoint.axiomBoundary, c.symbolEndpoint.axiomCount,
    c.symbolEndpoint.axiomBoundarySize, c.symbolEndpoint.suffixBoundary,
    c.symbolEndpoint.suffixCount, c.symbolEndpoint.suffixBoundarySize,
    c.symbolEndpoint.paTag, c.symbolEndpoint.arity,
    c.symbolEndpoint.symbolCode,
    c.inductionEndpoint.inputBoundary, c.inductionEndpoint.inputCount,
    c.inductionEndpoint.inputBoundarySize, c.inductionEndpoint.tailStart,
    c.inductionEndpoint.tailFinish, c.inductionEndpoint.tailBoundary,
    c.inductionEndpoint.tailCount, c.inductionEndpoint.tailBoundarySize,
    c.inductionEndpoint.axiomBoundary, c.inductionEndpoint.axiomCount,
    c.inductionEndpoint.axiomBoundarySize,
    c.inductionEndpoint.parser.inputBoundary,
    c.inductionEndpoint.parser.inputCount,
    c.inductionEndpoint.parser.inputBoundarySize,
    c.inductionEndpoint.parser.expectedBoundary,
    c.inductionEndpoint.parser.expectedCount,
    c.inductionEndpoint.parser.expectedBoundarySize,
    c.inductionEndpoint.parser.stateBoundary,
    c.inductionEndpoint.parser.stateCount,
    c.inductionEndpoint.parser.tableWidth,
    c.inductionEndpoint.parser.valueBound]

structure CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
    (c : CompactNumericVerifierPAAxiomJointLeafCoordinates)
    (bound : Nat) : Prop where
  endpointTable : Nat.size c.endpointTable <= bound
  endpointWidth : Nat.size c.endpointWidth <= bound
  endpointTokenCount : Nat.size c.endpointTokenCount <= bound
  inputStart : Nat.size c.inputStart <= bound
  inputFinish : Nat.size c.inputFinish <= bound
  endpointAxiomStart : Nat.size c.endpointAxiomStart <= bound
  endpointAxiomFinish : Nat.size c.endpointAxiomFinish <= bound
  formulaStart : Nat.size c.formulaStart <= bound
  formulaFinish : Nat.size c.formulaFinish <= bound
  suffixStart : Nat.size c.suffixStart <= bound
  suffixFinish : Nat.size c.suffixFinish <= bound
  proofTag : Nat.size c.proofTag <= bound
  certificateTag : Nat.size c.certificateTag <= bound
  gammaStart : Nat.size c.gammaStart <= bound
  gammaFinish : Nat.size c.gammaFinish <= bound
  gammaBoundarySize : Nat.size c.gammaBoundarySize <= bound
  candidate : CompactNatListRowSlotPublicCoordinateBounds c.candidate bound
  ruleAxiom : CompactNatListRowSlotPublicCoordinateBounds c.ruleAxiom bound
  fixedEndpoint : CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
    c.fixedEndpoint bound
  symbolEndpoint : CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
    c.symbolEndpoint bound
  inductionEndpoint :
    CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
      c.inductionEndpoint bound

set_option maxHeartbeats 500000 in
theorem compactNumericVerifierPAAxiomJointLeafTailEnvironment_size_le
    {c : CompactNumericVerifierPAAxiomJointLeafCoordinates} {bound : Nat}
    (hbounds : CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
      c bound)
    (coordinate : Fin 75) :
    Nat.size (compactNumericVerifierPAAxiomJointLeafTailEnvironment
      c coordinate) <= bound := by
  rcases hbounds with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
      h13, h14, h15, hcandidate, haxiom, hfixed, hsymbol, hinduction⟩
  rcases hcandidate with ⟨hc0, hc1, hc2, hc3, hc4⟩
  rcases haxiom with ⟨ha0, ha1, ha2, ha3, ha4⟩
  rcases hfixed with
    ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11,
      hf12, hf13, hf14⟩
  rcases hsymbol with
    ⟨hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11,
      hs12, hs13, hs14, hs15, hs16⟩
  rcases hinduction with
    ⟨hi0, hi1, hi2, hi3, hi4, hi5, hi6, hi7, hi8, hi9, hi10, hi11,
      hi12, hi13, hi14, hi15, hi16, hi17, hi18, hi19, hi20⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierPAAxiomJointLeafTailEnvironment] <;>
    assumption

theorem compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le
    {c : CompactNumericVerifierPAAxiomJointLeafCoordinates} {bound : Nat}
    (hrule : forall coordinate : Fin 184,
      Nat.size (compactAdditiveInductionPAAxiomRuleCheckEnvironment
        c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
        c.resultBool c.depth c.ruleAxiom c.body c.zeroWitness
        c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
        c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
        c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
        c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
        c.depthCapture c.fixed c.generated c.candidate c.route coordinate) <=
          bound)
    (htail : CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
      c bound)
    (coordinate : Fin 259) :
    Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
      c coordinate) <= bound := by
  apply natSize_vecAppend_le rfl
  · exact hrule
  · exact compactNumericVerifierPAAxiomJointLeafTailEnvironment_size_le htail

/-- Offset-128 adapter used by the 429-column step environment. -/
theorem compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le_at_429
    {c : CompactNumericVerifierPAAxiomJointLeafCoordinates} {bound : Nat}
    (hjoint : forall coordinate : Fin 259,
      Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
        c coordinate) <= bound)
    (environment : Fin 429 -> Nat)
    (hblock : forall coordinate : Fin 259,
      environment ⟨128 + coordinate, by omega⟩ =
        compactNumericVerifierPAAxiomJointLeafRowsEnvironment c coordinate)
    (coordinate : Fin 259) :
    Nat.size (environment ⟨128 + coordinate, by omega⟩) <= bound := by
  rw [hblock]
  exact hjoint coordinate

set_option maxHeartbeats 2200000 in
set_option maxRecDepth 8192 in
private theorem exists_nonInductionEndpoint_with_publicBounds
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    let endpointInputWeight :=
      compactNumericVerifierPAAxiomJointLeafEndpointInputWeight certificate
    ∃ tokenTable width tokenCount inputStart inputFinish axiomStart axiomFinish
        suffixStart suffixFinish endpointBound,
    ∃ fixedCoordinates : CompactCertificateNodeFixedPAEndpointCoordinates,
    ∃ symbolCoordinates : CompactCertificateNodeSymbolPAEndpointCoordinates,
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        axiomStart axiomFinish (compactPAAxiomCertificateTokens certificate) /\
      ((CompactCertificateNodeFixedPAEndpointGraph tokenTable width tokenCount
          inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish
          1 fixedCoordinates /\
        fixedCoordinates.paTag =
          compactTokenAt 0 (compactPAAxiomCertificateTokens certificate) /\
        compactTokenAt 1 (compactPAAxiomCertificateTokens certificate) = 0 /\
        compactTokenAt 2 (compactPAAxiomCertificateTokens certificate) = 0 /\
        CompactCertificateNodeFixedPAPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish axiomStart
          axiomFinish suffixStart suffixFinish 1 endpointBound
          (compactCertificateNodeFixedPAPublicCoordinateSizeBound
            endpointInputWeight) /\
        CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
          fixedCoordinates
          (compactCertificateNodeFixedPAPublicCoordinateSizeBound
            endpointInputWeight) /\
        symbolCoordinates = compactPAAxiomJointInactiveSymbolEndpoint) \/
       (CompactCertificateNodeSymbolPAEndpointGraph tokenTable width tokenCount
          inputStart inputFinish axiomStart axiomFinish suffixStart suffixFinish
          1 symbolCoordinates /\
        symbolCoordinates.paTag =
          compactTokenAt 0 (compactPAAxiomCertificateTokens certificate) /\
        symbolCoordinates.arity =
          compactTokenAt 1 (compactPAAxiomCertificateTokens certificate) /\
        symbolCoordinates.symbolCode =
          compactTokenAt 2 (compactPAAxiomCertificateTokens certificate) /\
        CompactCertificateNodeSymbolPAPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish axiomStart
          axiomFinish suffixStart suffixFinish 1 endpointBound
          (compactCertificateNodeSymbolPAPublicCoordinateSizeBound
            endpointInputWeight) /\
        CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
          symbolCoordinates
          (compactCertificateNodeSymbolPAPublicCoordinateSizeBound
            endpointInputWeight) /\
        fixedCoordinates = compactPAAxiomJointInactiveFixedEndpoint)) := by
  let tokens := compactPAAxiomCertificateTokens certificate
  let endpointInputWeight :=
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight certificate
  by_cases hsymbol : compactTokenAt 0 tokens = 3 \/ compactTokenAt 0 tokens = 4
  · have hvalid : CompactSymbolPAAxiomTagValid (compactTokenAt 0 tokens)
      (compactTokenAt 1 tokens) (compactTokenAt 2 tokens) := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt,
          CompactSymbolPAAxiomTagValid] <;>
        first
        | exact arithmeticFuncCodeValid_encode _
        | exact arithmeticRelCodeValid_encode _
    rcases
        exists_compactCertificateNodeSymbolPAEndpointBoundedGraph_with_publicBounds
          (compactTokenAt 0 tokens) (compactTokenAt 1 tokens)
          (compactTokenAt 2 tokens) [] hvalid with
      ⟨table, width, count, inputStart, inputFinish, axiomStart, axiomFinish,
        suffixStart, suffixFinish, endpointBound, hinput, hbounded, hpublic⟩
    rcases symbolEndpoint_of_boundedGraph hbounded hpublic with
      ⟨coordinates, hgraph, hcoordinates⟩
    have haxiom :=
      CompactCertificateNodeSymbolPAEndpointGraph.axiom_layout_exact hgraph
    rcases hgraph.sound with
      ⟨decodedInput, decodedAxiom, decodedSuffix, hdecodedInput,
        hdecodedAxiom, _hdecodedSuffix, hparser⟩
    have hinputEq : decodedInput =
        (1 :: compactTokenAt 0 tokens :: compactTokenAt 1 tokens ::
          compactTokenAt 2 tokens :: []) :=
      (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hdecodedInput hinput).1.symm
    subst decodedInput
    have hparserExpected : compactStructuralCertificateNodeParser
        (1 :: compactTokenAt 0 tokens :: compactTokenAt 1 tokens ::
          compactTokenAt 2 tokens :: []) =
        some (1, ([compactTokenAt 0 tokens, compactTokenAt 1 tokens,
          compactTokenAt 2 tokens], [])) := by
      simp [compactStructuralCertificateNodeParser,
        compactPAAxiomCertificateTokenParser_symbol,
        hvalid, consumedTokenPrefix]
    rw [hparserExpected] at hparser
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hparser
    have hdecodedAxiomEq : decodedAxiom =
        [compactTokenAt 0 tokens, compactTokenAt 1 tokens,
          compactTokenAt 2 tokens] := by
      simpa using hparser.1.symm
    have hcoordinateList :
        [coordinates.paTag, coordinates.arity, coordinates.symbolCode] =
          [compactTokenAt 0 tokens, compactTokenAt 1 tokens,
            compactTokenAt 2 tokens] := by
      rw [← hdecodedAxiomEq]
      exact
        (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hdecodedAxiom haxiom).1
    simp at hcoordinateList
    have htokens : tokens = [compactTokenAt 0 tokens,
        compactTokenAt 1 tokens, compactTokenAt 2 tokens] := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    have hendpointInputWeight :
        compactAdditiveValueWeight
            (1 :: compactTokenAt 0 tokens :: compactTokenAt 1 tokens ::
              compactTokenAt 2 tokens :: []) =
          endpointInputWeight := by
      change compactAdditiveValueWeight
          (1 :: compactTokenAt 0 tokens :: compactTokenAt 1 tokens ::
            compactTokenAt 2 tokens :: []) =
        compactAdditiveValueWeight (1 :: tokens)
      exact congrArg compactAdditiveValueWeight
        (congrArg (fun tail => 1 :: tail) htokens.symm)
    rw [hendpointInputWeight] at hpublic hcoordinates
    refine ⟨table, width, count, inputStart, inputFinish, axiomStart,
      axiomFinish, suffixStart, suffixFinish, endpointBound,
      compactPAAxiomJointInactiveFixedEndpoint, coordinates, ?_, Or.inr ?_⟩
    · change CompactAdditiveNatListDirectLayout table width count axiomStart
        axiomFinish tokens
      rw [htokens]
      simpa only [hcoordinateList.1, hcoordinateList.2.1,
        hcoordinateList.2.2] using haxiom
    · have hpublic' : CompactCertificateNodeSymbolPAPublicCoordinateBounds
          table width count inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish 1 endpointBound
          (compactCertificateNodeSymbolPAPublicCoordinateSizeBound
            endpointInputWeight) := by
        exact hpublic
      have hcoordinates' :
          CompactCertificateNodeSymbolPAEndpointCoordinateSizeBounds
            coordinates
            (compactCertificateNodeSymbolPAPublicCoordinateSizeBound
              endpointInputWeight) := by
        exact hcoordinates
      exact ⟨hgraph, hcoordinateList.1, hcoordinateList.2.1,
        hcoordinateList.2.2, hpublic', hcoordinates', rfl⟩
  · have htag : CompactFixedPAAxiomTag (compactTokenAt 0 tokens) := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt,
          CompactFixedPAAxiomTag]
    have hone : compactTokenAt 1 tokens = 0 := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    have htwo : compactTokenAt 2 tokens = 0 := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    rcases
        exists_compactCertificateNodeFixedPAEndpointBoundedGraph_with_publicBounds
          (compactTokenAt 0 tokens) [] htag with
      ⟨table, width, count, inputStart, inputFinish, axiomStart, axiomFinish,
        suffixStart, suffixFinish, endpointBound, hinput, hbounded, hpublic⟩
    rcases fixedEndpoint_of_boundedGraph hbounded hpublic with
      ⟨coordinates, hgraph, hcoordinates⟩
    have haxiom :=
      CompactCertificateNodeFixedPAEndpointGraph.axiom_layout_exact hgraph
    rcases hgraph.sound with
      ⟨decodedInput, decodedAxiom, decodedSuffix, hdecodedInput,
        hdecodedAxiom, _hdecodedSuffix, hparser⟩
    have hinputEq : decodedInput =
        (1 :: compactTokenAt 0 tokens :: []) :=
      (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hdecodedInput hinput).1.symm
    subst decodedInput
    have hparserExpected : compactStructuralCertificateNodeParser
        (1 :: compactTokenAt 0 tokens :: []) =
        some (1, ([compactTokenAt 0 tokens], [])) := by
      simp [compactStructuralCertificateNodeParser,
        compactPAAxiomCertificateTokenParser_fixed,
        htag, consumedTokenPrefix]
    rw [hparserExpected] at hparser
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hparser
    have hdecodedAxiomEq : decodedAxiom =
        [compactTokenAt 0 tokens] := by
      simpa using hparser.1.symm
    have hcoordinateList : [coordinates.paTag] =
        [compactTokenAt 0 tokens] := by
      rw [← hdecodedAxiomEq]
      exact
        (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
          hdecodedAxiom haxiom).1
    simp at hcoordinateList
    have htokens : tokens = [compactTokenAt 0 tokens] := by
      cases certificate <;>
        simp_all [tokens, FixedPAAxiomCertificate,
          compactPAAxiomCertificateTokens, compactTokenAt]
    have hendpointInputWeight :
        compactAdditiveValueWeight
            (1 :: compactTokenAt 0 tokens :: []) =
          endpointInputWeight := by
      change compactAdditiveValueWeight
          (1 :: compactTokenAt 0 tokens :: []) =
        compactAdditiveValueWeight (1 :: tokens)
      exact congrArg compactAdditiveValueWeight
        (congrArg (fun tail => 1 :: tail) htokens.symm)
    rw [hendpointInputWeight] at hpublic hcoordinates
    refine ⟨table, width, count, inputStart, inputFinish, axiomStart,
      axiomFinish, suffixStart, suffixFinish, endpointBound, coordinates,
      compactPAAxiomJointInactiveSymbolEndpoint, ?_, Or.inl ?_⟩
    · change CompactAdditiveNatListDirectLayout table width count axiomStart
        axiomFinish tokens
      rw [htokens]
      simpa only [hcoordinateList] using haxiom
    · have hpublic' : CompactCertificateNodeFixedPAPublicCoordinateBounds
          table width count inputStart inputFinish axiomStart axiomFinish
          suffixStart suffixFinish 1 endpointBound
          (compactCertificateNodeFixedPAPublicCoordinateSizeBound
            endpointInputWeight) := by
        exact hpublic
      have hcoordinates' :
          CompactCertificateNodeFixedPAEndpointCoordinateSizeBounds
            coordinates
            (compactCertificateNodeFixedPAPublicCoordinateSizeBound
              endpointInputWeight) := by
        exact hcoordinates
      exact ⟨hgraph, hcoordinateList, hone, htwo, hpublic', hcoordinates',
        rfl⟩


set_option maxHeartbeats 3000000 in
private theorem exists_fixedCanonicalJoint_with_publicBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate)
    (hfixed : FixedPAAxiomCertificate certificate) :
    ∃ c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c /\
      forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <=
        compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
          Gamma candidate certificate := by
  let candidateTokens := compactSentenceTokens candidate
  let certificateTokens := compactPAAxiomCertificateTokens certificate
  let chunks := compactFixedPAAxiomLeafRuleRowsCanonicalChunks
    Gamma candidate certificate
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let ruleTable := compactFixedWidthTableCode width tokens
  let gammaStart := (compactPackedChunkPrefix chunks 0).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let ruleAxiom := compactPackedNatListSlot chunks 1 certificateTokens
  let candidateSlot := compactPackedNatListSlot chunks 2 candidateTokens
  let ruleInputWeight := compactAdditiveTokenWeight tokens
  let endpointInputWeight :=
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight certificate
  let ruleBound :=
    compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      ruleInputWeight
  let endpointBound :=
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      endpointInputWeight
  let publicBound := ruleBound + endpointBound
  have hcanonicalChunks : compactPAAxiomLeafRuleRowsCanonicalChunks
      Gamma candidate certificate = chunks := by
    cases certificate <;>
      simp_all [chunks, compactPAAxiomLeafRuleRowsCanonicalChunks,
        FixedPAAxiomCertificate]
  have hpublicBound :
      compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
          Gamma candidate certificate = publicBound := by
    simp [compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound,
      compactNumericVerifierPAAxiomJointLeafRuleInputWeight,
      compactNumericVerifierPAAxiomJointLeafCanonicalRuleTokens,
      hcanonicalChunks, tokens, ruleInputWeight, endpointInputWeight,
      ruleBound, endpointBound, publicBound]
  have hGammaLayout : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma := by
    simpa [ruleTable, width, tokens, gammaStart, gammaFinish] using
      compactPackedNatListListLayout_canonical chunks 0 Gamma
        (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
        (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
  rcases hGammaLayout with
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaLayout' : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaWitness : CompactAdditiveNatListListWitnessRows ruleTable width
      tokens.length gammaStart Gamma.length gammaFinish gammaBoundary
        (Nat.size gammaBoundary) :=
    ⟨hGammaStructure,
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hGammaElementRows,
      rfl, by simpa using hGammaSize⟩
  have hRuleAxiom := compactPackedNatListSlot_canonical chunks 1
    certificateTokens
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
      certificateTokens])
  have hCandidate := compactPackedNatListSlot_canonical chunks 2
    candidateTokens
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks])
    (by simp [chunks, compactFixedPAAxiomLeafRuleRowsCanonicalChunks,
      candidateTokens])
  dsimp only [ruleAxiom, candidateSlot] at hRuleAxiom hCandidate
  have hfixedRule : CompactAdditiveFixedPAAxiomRuleCheck ruleTable width
      tokens.length gammaBoundary Gamma.length candidateSlot.start
      candidateSlot.finish candidateSlot.count
      (compactTokenAt 0 certificateTokens) (compactTokenAt 1 certificateTokens)
      (compactTokenAt 2 certificateTokens)
      (compactAdditiveBoolTag
        (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))) := by
    have hcanonical :=
      (compactAdditiveFixedPAAxiomRuleCheck_canonical_iff candidate certificate
        hfixed hGammaElementRows hCandidate.2.2.1).2 rfl
    simpa [candidateTokens, certificateTokens, candidateSlot, hCandidate.1]
      using hcanonical
  have htokenCount : tokens.length <= ruleInputWeight :=
    compactAdditiveTokenList_length_le_weight tokens
  have hwidthValue : width <=
      compactNumericVerifierPAAxiomJointLeafRuleWidthBound ruleInputWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    rfl
  have htableRule : Nat.size ruleTable <= ruleBound := by
    apply (compactFixedWidthTableCode_size_le width tokens).trans
    apply (Nat.mul_le_mul htokenCount hwidthValue).trans
    dsimp only [ruleBound]
    unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
    unfold compactNumericVerifierPAAxiomJointLeafRuleTableSizeBound
    omega
  have hwidthRule : Nat.size width <= ruleBound :=
    (natSize_le_of_le hwidthValue).trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have htokenRule : Nat.size tokens.length <= ruleBound :=
    (natSize_le_of_le htokenCount).trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have hGammaCoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hGammaStructure
  have hGammaArea : (Gamma.length + 1) * tokens.length <=
      (ruleInputWeight + 1) * ruleInputWeight :=
    Nat.mul_le_mul
      (Nat.add_le_add_right (hGammaCoordinates.2.1.trans htokenCount) 1)
      htokenCount
  have hgammaBoundaryRule : Nat.size gammaBoundary <= ruleBound :=
    hGammaSize.trans (hGammaArea.trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      unfold compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
      omega))
  have hgammaBoundarySizeRule : Nat.size (Nat.size gammaBoundary) <=
      ruleBound :=
    (natSize_le_of_le hGammaSize).trans (hGammaArea.trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      unfold compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
      omega))
  have hpositionRule {value : Nat} (hvalue : value <= tokens.length) :
      Nat.size value <= ruleBound :=
    (natSize_le_of_le (hvalue.trans htokenCount)).trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have hgammaStartRule := hpositionRule hGammaCoordinates.1
  have hgammaFinishRule := hpositionRule hGammaCoordinates.2.2
  have hgammaCountRule := hpositionRule hGammaCoordinates.2.1
  have hRuleAxiomBounds :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hRuleAxiom htokenCount
  have hCandidateBounds :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hCandidate htokenCount
  have hinactiveRoute := inactiveRoute_publicCoordinateBounds
    htableRule hwidthRule htokenRule
  have hresultRule : Nat.size
      (compactAdditiveBoolTag
        (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))) <=
      ruleBound := by
    simp only [compactAdditiveBoolTag]
    split <;> simp [ruleBound,
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound]
  have hruleEnvironment : forall coordinate : Fin 184,
      Nat.size (compactAdditiveInductionPAAxiomRuleCheckEnvironment
        ruleTable width tokens.length gammaBoundary Gamma.length
        (compactAdditiveBoolTag
          (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens))))
        0 ruleAxiom
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot
        compactPAAxiomLeafInactiveNatListRowSlot candidateSlot
        compactPAAxiomLeafInactiveRouteCoordinates coordinate) <= ruleBound :=
    compactAdditiveInductionPAAxiomRuleCheckEnvironment_size_le
      hinactiveRoute hgammaBoundaryRule hgammaCountRule hresultRule
      hRuleAxiomBounds.boundary hRuleAxiomBounds.count
      hCandidateBounds.start hCandidateBounds.finish
  rcases exists_nonInductionEndpoint_with_publicBounds certificate hfixed with
    ⟨endpointTable, endpointWidth, endpointTokenCount, inputStart, inputFinish,
      endpointAxiomStart, endpointAxiomFinish, suffixStart, suffixFinish,
      endpointWitnessBound, fixedEndpoint, symbolEndpoint, hEndpointAxiom,
      hfixedEndpoint | hsymbolEndpoint⟩
  · rcases hfixedEndpoint with
      ⟨hendpoint, hpaTag, harity, hsymbolCode, hendpointPublic,
        hfixedCoordinateBounds, _hsymbolInactive⟩
    have hcross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hEndpointAxiom hRuleAxiom.2.2.1
    have hjointRule : CompactAdditiveFixedPAAxiomRuleCheck ruleTable width
        tokens.length gammaBoundary Gamma.length candidateSlot.start
        candidateSlot.finish candidateSlot.count fixedEndpoint.paTag 0 0
        (compactAdditiveBoolTag
          (compactAxmRuleCheck
            (Gamma, (candidateTokens, certificateTokens)))) := by
      simpa [certificateTokens, hpaTag, harity, hsymbolCode] using hfixedRule
    let c : CompactNumericVerifierPAAxiomJointLeafCoordinates :=
      { endpointTable := endpointTable
        endpointWidth := endpointWidth
        endpointTokenCount := endpointTokenCount
        ruleTable := ruleTable
        ruleWidth := width
        ruleTokenCount := tokens.length
        inputStart := inputStart
        inputFinish := inputFinish
        endpointAxiomStart := endpointAxiomStart
        endpointAxiomFinish := endpointAxiomFinish
        formulaStart := 0
        formulaFinish := 0
        suffixStart := suffixStart
        suffixFinish := suffixFinish
        proofTag := 1
        certificateTag := 1
        gammaStart := gammaStart
        gammaFinish := gammaFinish
        gammaBoundary := gammaBoundary
        gammaCount := Gamma.length
        gammaBoundarySize := Nat.size gammaBoundary
        candidate := candidateSlot
        ruleAxiom := ruleAxiom
        resultBool := compactAdditiveBoolTag
          (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
        depth := 0
        fixedEndpoint := fixedEndpoint
        symbolEndpoint := compactPAAxiomJointInactiveSymbolEndpoint
        inductionEndpoint := compactPAAxiomJointInactiveInductionEndpoint
        body := compactPAAxiomLeafInactiveNatListRowSlot
        zeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openZeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openSuccessorWitness := compactPAAxiomLeafInactiveNatListRowSlot
        captureOne := compactPAAxiomLeafInactiveNatListRowSlot
        empty := compactPAAxiomLeafInactiveNatListRowSlot
        base := compactPAAxiomLeafInactiveNatListRowSlot
        negatedBase := compactPAAxiomLeafInactiveNatListRowSlot
        stepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepSuccessor := compactPAAxiomLeafInactiveNatListRowSlot
        negatedStepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        negatedQuantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedFinal := compactPAAxiomLeafInactiveNatListRowSlot
        innerDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        sentence := compactPAAxiomLeafInactiveNatListRowSlot
        fvarList := compactPAAxiomLeafInactiveNatListRowSlot
        depthCapture := compactPAAxiomLeafInactiveNatListRowSlot
        fixed := compactPAAxiomLeafInactiveNatListRowSlot
        generated := compactPAAxiomLeafInactiveNatListRowSlot
        route := compactPAAxiomLeafInactiveRouteCoordinates }
    have hcanonical : CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c := by
      dsimp [CompactCanonicalNumericVerifierPAAxiomJointLeafRows, c,
        CompactNumericVerifierPAAxiomJointLeafRows]
      refine ⟨?_, rfl, hGammaLayout', hCandidate.2.2.1,
        hRuleAxiom.2.2.1, hEndpointAxiom⟩
      exact ⟨hGammaWitness, hCandidate.2.1, hRuleAxiom.2.1, hcross, rfl,
        Or.inl (Or.inl ⟨hendpoint, hjointRule⟩)⟩
    have hRuleToPublic : ruleBound <= publicBound := by
      dsimp only [publicBound]
      omega
    have hEndpointToPublic :
        compactCertificateNodeFixedPAPublicCoordinateSizeBound
            endpointInputWeight <= publicBound := by
      dsimp only [publicBound, endpointBound]
      unfold compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      omega
    have htail : CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
        c publicBound := by
      exact
        { endpointTable := hendpointPublic.tokenTable.trans hEndpointToPublic
          endpointWidth := hendpointPublic.width.trans hEndpointToPublic
          endpointTokenCount :=
            hendpointPublic.tokenCount.trans hEndpointToPublic
          inputStart := hendpointPublic.inputStart.trans hEndpointToPublic
          inputFinish := hendpointPublic.inputFinish.trans hEndpointToPublic
          endpointAxiomStart :=
            hendpointPublic.axiomStart.trans hEndpointToPublic
          endpointAxiomFinish :=
            hendpointPublic.axiomFinish.trans hEndpointToPublic
          formulaStart := by
            change Nat.size 0 <= publicBound
            simp
          formulaFinish := by
            change Nat.size 0 <= publicBound
            simp
          suffixStart := hendpointPublic.suffixStart.trans hEndpointToPublic
          suffixFinish := hendpointPublic.suffixFinish.trans hEndpointToPublic
          proofTag := hendpointPublic.certificateTag.trans hEndpointToPublic
          certificateTag :=
            hendpointPublic.certificateTag.trans hEndpointToPublic
          gammaStart := hgammaStartRule.trans hRuleToPublic
          gammaFinish := hgammaFinishRule.trans hRuleToPublic
          gammaBoundarySize := hgammaBoundarySizeRule.trans hRuleToPublic
          candidate := hCandidateBounds.mono hRuleToPublic
          ruleAxiom := hRuleAxiomBounds.mono hRuleToPublic
          fixedEndpoint := hfixedCoordinateBounds.mono hEndpointToPublic
          symbolEndpoint :=
            inactiveSymbolEndpoint_coordinateSizeBounds publicBound
          inductionEndpoint :=
            inactiveInductionEndpoint_coordinateSizeBounds publicBound }
    have henvironment : forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <= publicBound := by
      apply compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le
      · intro coordinate
        exact (hruleEnvironment coordinate).trans hRuleToPublic
      · exact htail
    refine ⟨c, hcanonical, ?_⟩
    simpa only [hpublicBound] using henvironment
  · rcases hsymbolEndpoint with
      ⟨hendpoint, hpaTag, harity, hsymbolCode, hendpointPublic,
        hsymbolCoordinateBounds, _hfixedInactive⟩
    have hcross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
      hEndpointAxiom hRuleAxiom.2.2.1
    have hjointRule : CompactAdditiveFixedPAAxiomRuleCheck ruleTable width
        tokens.length gammaBoundary Gamma.length candidateSlot.start
        candidateSlot.finish candidateSlot.count symbolEndpoint.paTag
        symbolEndpoint.arity symbolEndpoint.symbolCode
        (compactAdditiveBoolTag
          (compactAxmRuleCheck
            (Gamma, (candidateTokens, certificateTokens)))) := by
      simpa [certificateTokens, hpaTag, harity, hsymbolCode] using hfixedRule
    let c : CompactNumericVerifierPAAxiomJointLeafCoordinates :=
      { endpointTable := endpointTable
        endpointWidth := endpointWidth
        endpointTokenCount := endpointTokenCount
        ruleTable := ruleTable
        ruleWidth := width
        ruleTokenCount := tokens.length
        inputStart := inputStart
        inputFinish := inputFinish
        endpointAxiomStart := endpointAxiomStart
        endpointAxiomFinish := endpointAxiomFinish
        formulaStart := 0
        formulaFinish := 0
        suffixStart := suffixStart
        suffixFinish := suffixFinish
        proofTag := 1
        certificateTag := 1
        gammaStart := gammaStart
        gammaFinish := gammaFinish
        gammaBoundary := gammaBoundary
        gammaCount := Gamma.length
        gammaBoundarySize := Nat.size gammaBoundary
        candidate := candidateSlot
        ruleAxiom := ruleAxiom
        resultBool := compactAdditiveBoolTag
          (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
        depth := 0
        fixedEndpoint := compactPAAxiomJointInactiveFixedEndpoint
        symbolEndpoint := symbolEndpoint
        inductionEndpoint := compactPAAxiomJointInactiveInductionEndpoint
        body := compactPAAxiomLeafInactiveNatListRowSlot
        zeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openZeroWitness := compactPAAxiomLeafInactiveNatListRowSlot
        openSuccessorWitness := compactPAAxiomLeafInactiveNatListRowSlot
        captureOne := compactPAAxiomLeafInactiveNatListRowSlot
        empty := compactPAAxiomLeafInactiveNatListRowSlot
        base := compactPAAxiomLeafInactiveNatListRowSlot
        negatedBase := compactPAAxiomLeafInactiveNatListRowSlot
        stepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepSuccessor := compactPAAxiomLeafInactiveNatListRowSlot
        negatedStepZero := compactPAAxiomLeafInactiveNatListRowSlot
        stepDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        negatedQuantifiedStep := compactPAAxiomLeafInactiveNatListRowSlot
        quantifiedFinal := compactPAAxiomLeafInactiveNatListRowSlot
        innerDisjunction := compactPAAxiomLeafInactiveNatListRowSlot
        sentence := compactPAAxiomLeafInactiveNatListRowSlot
        fvarList := compactPAAxiomLeafInactiveNatListRowSlot
        depthCapture := compactPAAxiomLeafInactiveNatListRowSlot
        fixed := compactPAAxiomLeafInactiveNatListRowSlot
        generated := compactPAAxiomLeafInactiveNatListRowSlot
        route := compactPAAxiomLeafInactiveRouteCoordinates }
    have hcanonical : CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c := by
      dsimp [CompactCanonicalNumericVerifierPAAxiomJointLeafRows, c,
        CompactNumericVerifierPAAxiomJointLeafRows]
      refine ⟨?_, rfl, hGammaLayout', hCandidate.2.2.1,
        hRuleAxiom.2.2.1, hEndpointAxiom⟩
      exact ⟨hGammaWitness, hCandidate.2.1, hRuleAxiom.2.1, hcross, rfl,
        Or.inl (Or.inr ⟨hendpoint, hjointRule⟩)⟩
    have hRuleToPublic : ruleBound <= publicBound := by
      dsimp only [publicBound]
      omega
    have hEndpointToPublic :
        compactCertificateNodeSymbolPAPublicCoordinateSizeBound
            endpointInputWeight <= publicBound := by
      dsimp only [publicBound, endpointBound]
      unfold compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      omega
    have htail : CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
        c publicBound := by
      exact
        { endpointTable := hendpointPublic.tokenTable.trans hEndpointToPublic
          endpointWidth := hendpointPublic.width.trans hEndpointToPublic
          endpointTokenCount :=
            hendpointPublic.tokenCount.trans hEndpointToPublic
          inputStart := hendpointPublic.inputStart.trans hEndpointToPublic
          inputFinish := hendpointPublic.inputFinish.trans hEndpointToPublic
          endpointAxiomStart :=
            hendpointPublic.axiomStart.trans hEndpointToPublic
          endpointAxiomFinish :=
            hendpointPublic.axiomFinish.trans hEndpointToPublic
          formulaStart := by
            change Nat.size 0 <= publicBound
            simp
          formulaFinish := by
            change Nat.size 0 <= publicBound
            simp
          suffixStart := hendpointPublic.suffixStart.trans hEndpointToPublic
          suffixFinish := hendpointPublic.suffixFinish.trans hEndpointToPublic
          proofTag := hendpointPublic.certificateTag.trans hEndpointToPublic
          certificateTag :=
            hendpointPublic.certificateTag.trans hEndpointToPublic
          gammaStart := hgammaStartRule.trans hRuleToPublic
          gammaFinish := hgammaFinishRule.trans hRuleToPublic
          gammaBoundarySize := hgammaBoundarySizeRule.trans hRuleToPublic
          candidate := hCandidateBounds.mono hRuleToPublic
          ruleAxiom := hRuleAxiomBounds.mono hRuleToPublic
          fixedEndpoint :=
            inactiveFixedEndpoint_coordinateSizeBounds publicBound
          symbolEndpoint := hsymbolCoordinateBounds.mono hEndpointToPublic
          inductionEndpoint :=
            inactiveInductionEndpoint_coordinateSizeBounds publicBound }
    have henvironment : forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <= publicBound := by
      apply compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le
      · intro coordinate
        exact (hruleEnvironment coordinate).trans hRuleToPublic
      · exact htail
    refine ⟨c, hcanonical, ?_⟩
    simpa only [hpublicBound] using henvironment


set_option maxHeartbeats 3500000 in
private theorem exists_inductionCanonicalJoint_with_publicBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1) :
    ∃ c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate (PAAxiomCertificate.induction body) c /\
      forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <=
        compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
          Gamma candidate (PAAxiomCertificate.induction body) := by
  let bodyTokens := compactArithmeticFormulaTokens body
  let candidateTokens := compactSentenceTokens candidate
  let certificateTokens := 22 :: bodyTokens
  let data := compactGuardedInductionExecutableData bodyTokens
  let extraChunks := compactInductionPAAxiomRuleCheckExtraChunks
    bodyTokens candidateTokens Gamma
  let chunks := compactInductionPAAxiomRuleCheckChunks
    bodyTokens candidateTokens Gamma
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let ruleTable := compactFixedWidthTableCode width tokens
  let resultBool := compactAdditiveBoolTag
    (compactAxmRuleCheck (Gamma, (candidateTokens, certificateTokens)))
  let gammaStart := (compactPackedChunkPrefix chunks 39).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let ruleAxiom := compactPackedNatListSlot chunks 37 certificateTokens
  let bodySlot := compactPackedNatListSlot chunks 0 data.body
  let zeroWitness := compactPackedNatListSlot chunks 1 data.zeroWitness
  let openZeroWitness := compactPackedNatListSlot chunks 2 data.openZeroWitness
  let openSuccessorWitness :=
    compactPackedNatListSlot chunks 3 data.openSuccessorWitness
  let captureOne := compactPackedNatListSlot chunks 4 data.captureOne
  let empty := compactPackedNatListSlot chunks 5 data.empty
  let base := compactPackedNatListSlot chunks 6 data.base
  let negatedBase := compactPackedNatListSlot chunks 7 data.negatedBase
  let stepZero := compactPackedNatListSlot chunks 10 data.stepZero
  let stepSuccessor := compactPackedNatListSlot chunks 13 data.stepSuccessor
  let negatedStepZero :=
    compactPackedNatListSlot chunks 14 data.negatedStepZero
  let stepDisjunction :=
    compactPackedNatListSlot chunks 15 data.stepDisjunction
  let quantifiedStep := compactPackedNatListSlot chunks 16 data.quantifiedStep
  let negatedQuantifiedStep :=
    compactPackedNatListSlot chunks 17 data.negatedQuantifiedStep
  let quantifiedFinal :=
    compactPackedNatListSlot chunks 18 data.quantifiedFinal
  let innerDisjunction :=
    compactPackedNatListSlot chunks 19 data.innerDisjunction
  let sentence := compactPackedNatListSlot chunks 20 data.sentence
  let fvarList := compactPackedNatListSlot chunks 21 data.fvarList
  let depthCapture := compactPackedNatListSlot chunks 22 data.depthCapture
  let fixed := compactPackedNatListSlot chunks 23 data.fixed
  let generated := compactPackedNatListSlot chunks 24 data.generated
  let candidateSlot := compactPackedNatListSlot chunks 38 candidateTokens
  let ruleInputWeight := compactAdditiveTokenWeight tokens
  let endpointInputWeight :=
    compactNumericVerifierPAAxiomJointLeafEndpointInputWeight
      (PAAxiomCertificate.induction body)
  let ruleBound :=
    compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      ruleInputWeight
  let endpointCoordinateBound :=
    compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
      endpointInputWeight
  let publicBound := ruleBound + endpointCoordinateBound
  have hchunks : chunks = compactGuardedInductionRouteChunks data ++
      extraChunks := by
    simp [chunks, data, extraChunks,
      compactInductionPAAxiomRuleCheckChunks]
  have hpublicBound :
      compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
          Gamma candidate (PAAxiomCertificate.induction body) = publicBound := by
    simp [compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound,
      compactNumericVerifierPAAxiomJointLeafRuleInputWeight,
      compactNumericVerifierPAAxiomJointLeafCanonicalRuleTokens,
      compactPAAxiomLeafRuleRowsCanonicalChunks,
      compactNumericVerifierPAAxiomJointLeafEndpointInputWeight,
      compactPAAxiomCertificateTokens, bodyTokens, candidateTokens,
      chunks, tokens, ruleInputWeight,
      endpointInputWeight, ruleBound, endpointCoordinateBound, publicBound,
      compactInductionPAAxiomRuleCheckChunks]
  have hchunksLength : chunks.length = 40 := by
    simp [chunks]
  have hGammaLayout : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma := by
    simpa [ruleTable, width, tokens, gammaStart, gammaFinish] using
      compactPackedNatListListLayout_canonical chunks 39 Gamma
        (by omega)
        (by
          rw [← List.getI_eq_getElem chunks (by omega)]
          simp [chunks])
  rcases hGammaLayout with
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaLayout' : CompactAdditiveNatListListDirectLayout ruleTable width
      tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hGammaStructure, hGammaElementRows, hGammaSize⟩
  have hGammaWitness : CompactAdditiveNatListListWitnessRows ruleTable width
      tokens.length gammaStart Gamma.length gammaFinish gammaBoundary
        (Nat.size gammaBoundary) :=
    ⟨hGammaStructure,
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hGammaElementRows,
      rfl, by simpa using hGammaSize⟩
  have slotCanonical (index : Nat) (values : List Nat)
      (hindex : index < chunks.length)
      (hchunk : chunks[index] = compactAdditiveEncode values) :
      CompactPackedNatListSlotCanonical ruleTable width tokens.length
        (compactPackedNatListSlot chunks index values) values := by
    simpa [ruleTable, width, tokens] using
      compactPackedNatListSlot_canonical chunks index values hindex hchunk
  have hBody : CompactPackedNatListSlotCanonical ruleTable width tokens.length
      bodySlot bodyTokens := by
    apply slotCanonical 0 bodyTokens (by omega)
    rw [show chunks[0] = chunks.getI 0 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, bodyTokens]
  have hRuleAxiom : CompactPackedNatListSlotCanonical ruleTable width
      tokens.length ruleAxiom certificateTokens := by
    apply slotCanonical 37 certificateTokens (by omega)
    rw [show chunks[37] = chunks.getI 37 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, certificateTokens]
  have hCandidate : CompactPackedNatListSlotCanonical ruleTable width
      tokens.length candidateSlot candidateTokens := by
    apply slotCanonical 38 candidateTokens (by omega)
    rw [show chunks[38] = chunks.getI 38 by
      exact (List.getI_eq_getElem chunks (by omega)).symm]
    simp [chunks, candidateTokens]
  have hnat : CompactGuardedInductionPackedNatRows
      ruleTable width tokens.length chunks data := by
    simpa [ruleTable, width, tokens, hchunks] using
      compactGuardedInductionPackedNatRows_canonical data extraChunks
  rcases
      exists_compactGuardedInductionSentenceRoute_with_publicCoordinateBounds
        bodyTokens extraChunks with
    ⟨route, hrouteRaw, hroutePublicRaw⟩
  have hroute : CompactGuardedInductionSentenceRoute
      ruleTable width tokens.length data.depth bodySlot zeroWitness
      openZeroWitness openSuccessorWitness captureOne empty base negatedBase
      stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence fvarList
      depthCapture fixed generated route := by
    simpa [ruleTable, width, tokens, hchunks, bodySlot, zeroWitness,
      openZeroWitness, openSuccessorWitness, captureOne, empty, base,
      negatedBase, stepZero, stepSuccessor, negatedStepZero, stepDisjunction,
      quantifiedStep, negatedQuantifiedStep, quantifiedFinal,
      innerDisjunction, sentence, fvarList, depthCapture, fixed, generated,
      data] using hrouteRaw
  have hroutePublic :
      CompactGuardedInductionSentenceRoutePublicCoordinateBounds
        ruleTable width tokens.length data.depth bodySlot zeroWitness
        openZeroWitness openSuccessorWitness captureOne empty base negatedBase
        stepZero stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal innerDisjunction sentence fvarList
        depthCapture fixed generated route ruleBound := by
    simpa [ruleTable, width, tokens, hchunks, bodySlot, zeroWitness,
      openZeroWitness, openSuccessorWitness, captureOne, empty, base,
      negatedBase, stepZero, stepSuccessor, negatedStepZero, stepDisjunction,
      quantifiedStep, negatedQuantifiedStep, quantifiedFinal,
      innerDisjunction, sentence, fvarList, depthCapture, fixed, generated,
      data, ruleInputWeight, ruleBound] using hroutePublicRaw
  have hconsLength : CompactAdditiveNatListConsRows ruleTable width
      tokens.length bodySlot.boundary bodyTokens.length ruleAxiom.boundary
      certificateTokens.length 22 := by
    exact (compactAdditiveNatListConsRows_iff_cons_of_rows
      hBody.elements hRuleAxiom.elements).2 (by
        simp [certificateTokens])
  have hcons : CompactAdditiveNatListConsRows ruleTable width tokens.length
      bodySlot.boundary bodySlot.count ruleAxiom.boundary ruleAxiom.count
      22 := by
    simpa only [hBody.1, hRuleAxiom.1] using hconsLength
  have hrule : CompactAdditiveInductionPAAxiomRuleCheck ruleTable width
      tokens.length gammaBoundary Gamma.length resultBool ruleAxiom bodySlot
      zeroWitness openZeroWitness openSuccessorWitness captureOne empty base
      negatedBase stepZero stepSuccessor negatedStepZero stepDisjunction
      quantifiedStep negatedQuantifiedStep quantifiedFinal innerDisjunction
      sentence fvarList depthCapture fixed generated candidateSlot data.depth
      route :=
    (compactAdditiveInductionPAAxiomRuleCheck_iff_of_route
      (resultBoolValue := resultBool) body candidate hcons hroute
      hGammaElementRows hBody.2.2.1 hCandidate.2.2.1).2 (by
        simp [resultBool, bodyTokens, candidateTokens, certificateTokens,
          compactPAAxiomCertificateTokens])
  have htokenCount : tokens.length <= ruleInputWeight :=
    compactAdditiveTokenList_length_le_weight tokens
  have hGammaCoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hGammaStructure
  have hGammaArea : (Gamma.length + 1) * tokens.length <=
      (ruleInputWeight + 1) * ruleInputWeight :=
    Nat.mul_le_mul
      (Nat.add_le_add_right (hGammaCoordinates.2.1.trans htokenCount) 1)
      htokenCount
  have hgammaBoundaryRule : Nat.size gammaBoundary <= ruleBound :=
    hGammaSize.trans (hGammaArea.trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      unfold compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
      omega))
  have hgammaBoundarySizeRule : Nat.size (Nat.size gammaBoundary) <=
      ruleBound :=
    (natSize_le_of_le hGammaSize).trans (hGammaArea.trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      unfold compactNumericVerifierPAAxiomJointLeafRuleListBoundarySizeBound
      omega))
  have hpositionRule {value : Nat} (hvalue : value <= tokens.length) :
      Nat.size value <= ruleBound :=
    (natSize_le_of_le (hvalue.trans htokenCount)).trans (by
      dsimp only [ruleBound]
      unfold compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound
      omega)
  have hgammaStartRule := hpositionRule hGammaCoordinates.1
  have hgammaFinishRule := hpositionRule hGammaCoordinates.2.2
  have hgammaCountRule := hpositionRule hGammaCoordinates.2.1
  have hRuleAxiomBounds :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hRuleAxiom htokenCount
  have hCandidateBounds :=
    CompactPackedNatListSlotCanonical.publicCoordinateBounds
      hCandidate htokenCount
  have hresultRule : Nat.size resultBool <= ruleBound := by
    simp only [resultBool, compactAdditiveBoolTag]
    split <;> simp [ruleBound,
      compactNumericVerifierPAAxiomJointLeafRuleCoordinateSizeBound]
  have hruleEnvironment : forall coordinate : Fin 184,
      Nat.size (compactAdditiveInductionPAAxiomRuleCheckEnvironment
        ruleTable width tokens.length gammaBoundary Gamma.length resultBool
        data.depth ruleAxiom bodySlot zeroWitness openZeroWitness
        openSuccessorWitness captureOne empty base negatedBase stepZero
        stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
        fvarList depthCapture fixed generated candidateSlot route coordinate) <=
      ruleBound :=
    compactAdditiveInductionPAAxiomRuleCheckEnvironment_size_le
      hroutePublic hgammaBoundaryRule hgammaCountRule hresultRule
      hRuleAxiomBounds.boundary hRuleAxiomBounds.count
      hCandidateBounds.start hCandidateBounds.finish
  have hformulaParser : compactFormulaTokenParser 1 bodyTokens = some [] := by
    simpa [bodyTokens] using compactFormulaTokenParser_canonical_append body []
  rcases
      exists_compactCertificateNodeInductionPAEndpointBoundedGraph_with_publicBounds
        bodyTokens [] hformulaParser with
    ⟨endpointTable, endpointWidth, endpointTokenCount, inputStart, inputFinish,
      endpointAxiomStart, endpointAxiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, endpointWitnessBound, hinput, hbounded,
      hendpointPublicRaw⟩
  rcases inductionEndpoint_of_boundedGraph hbounded hendpointPublicRaw with
    ⟨inductionEndpoint, hendpoint, hinductionCoordinateBoundsRaw⟩
  have hendpointPublic : CompactCertificateNodeInductionPAPublicCoordinateBounds
      endpointTable endpointWidth endpointTokenCount inputStart inputFinish
      endpointAxiomStart endpointAxiomFinish formulaStart formulaFinish
      suffixStart suffixFinish 1 endpointWitnessBound
      (compactCertificateNodeInductionPAPublicCoordinateSizeBound
        endpointInputWeight) := by
    simpa [endpointInputWeight,
      compactNumericVerifierPAAxiomJointLeafEndpointInputWeight,
      compactPAAxiomCertificateTokens, bodyTokens, certificateTokens] using
        hendpointPublicRaw
  have hinductionCoordinateBounds :
      CompactCertificateNodeInductionPAEndpointCoordinateSizeBounds
        inductionEndpoint
        (compactCertificateNodeInductionPAPublicCoordinateSizeBound
          endpointInputWeight) := by
    simpa [endpointInputWeight,
      compactNumericVerifierPAAxiomJointLeafEndpointInputWeight,
      compactPAAxiomCertificateTokens, bodyTokens, certificateTokens] using
        hinductionCoordinateBoundsRaw
  rcases hendpoint.sound with
    ⟨decodedInput, decodedAxiom, decodedSuffix, hdecodedInput,
      hdecodedAxiom, _hdecodedSuffix, hparser⟩
  have hinputEq : decodedInput = (1 :: 22 :: bodyTokens) :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hdecodedInput hinput).1.symm
  subst decodedInput
  have hpaParser : compactPAAxiomCertificateTokenParser certificateTokens =
      some [] := by
    simpa [certificateTokens, bodyTokens, compactPAAxiomCertificateTokens]
      using compactPAAxiomCertificateTokenParser_canonical_append
        (PAAxiomCertificate.induction body) []
  have hparserExpected : compactStructuralCertificateNodeParser
      (1 :: 22 :: bodyTokens) = some (1, (certificateTokens, [])) := by
    simp [compactStructuralCertificateNodeParser, certificateTokens,
      hpaParser, consumedTokenPrefix]
  rw [hparserExpected] at hparser
  simp only [Option.some.injEq, Prod.mk.injEq, true_and] at hparser
  have hdecodedAxiomEq : decodedAxiom = certificateTokens := by
    simpa using hparser.1.symm
  have hEndpointAxiom : CompactAdditiveNatListDirectLayout endpointTable
      endpointWidth endpointTokenCount endpointAxiomStart endpointAxiomFinish
      certificateTokens := by
    simpa [hdecodedAxiomEq] using hdecodedAxiom
  have hcross := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    hEndpointAxiom hRuleAxiom.2.2.1
  let c : CompactNumericVerifierPAAxiomJointLeafCoordinates :=
    { endpointTable := endpointTable
      endpointWidth := endpointWidth
      endpointTokenCount := endpointTokenCount
      ruleTable := ruleTable
      ruleWidth := width
      ruleTokenCount := tokens.length
      inputStart := inputStart
      inputFinish := inputFinish
      endpointAxiomStart := endpointAxiomStart
      endpointAxiomFinish := endpointAxiomFinish
      formulaStart := formulaStart
      formulaFinish := formulaFinish
      suffixStart := suffixStart
      suffixFinish := suffixFinish
      proofTag := 1
      certificateTag := 1
      gammaStart := gammaStart
      gammaFinish := gammaFinish
      gammaBoundary := gammaBoundary
      gammaCount := Gamma.length
      gammaBoundarySize := Nat.size gammaBoundary
      candidate := candidateSlot
      ruleAxiom := ruleAxiom
      resultBool := resultBool
      depth := data.depth
      fixedEndpoint := compactPAAxiomJointInactiveFixedEndpoint
      symbolEndpoint := compactPAAxiomJointInactiveSymbolEndpoint
      inductionEndpoint := inductionEndpoint
      body := bodySlot
      zeroWitness := zeroWitness
      openZeroWitness := openZeroWitness
      openSuccessorWitness := openSuccessorWitness
      captureOne := captureOne
      empty := empty
      base := base
      negatedBase := negatedBase
      stepZero := stepZero
      stepSuccessor := stepSuccessor
      negatedStepZero := negatedStepZero
      stepDisjunction := stepDisjunction
      quantifiedStep := quantifiedStep
      negatedQuantifiedStep := negatedQuantifiedStep
      quantifiedFinal := quantifiedFinal
      innerDisjunction := innerDisjunction
      sentence := sentence
      fvarList := fvarList
      depthCapture := depthCapture
      fixed := fixed
      generated := generated
      route := route }
  have hcanonical : CompactCanonicalNumericVerifierPAAxiomJointLeafRows
      Gamma candidate (PAAxiomCertificate.induction body) c := by
    dsimp [CompactCanonicalNumericVerifierPAAxiomJointLeafRows, c,
      CompactNumericVerifierPAAxiomJointLeafRows]
    refine ⟨?_, rfl, hGammaLayout', hCandidate.2.2.1,
      hRuleAxiom.2.2.1, ?_⟩
    · exact ⟨hGammaWitness, hCandidate.2.1, hRuleAxiom.2.1, hcross, rfl,
        Or.inr ⟨hendpoint, hrule⟩⟩
    · simpa [certificateTokens, bodyTokens, compactPAAxiomCertificateTokens]
        using hEndpointAxiom
  have hRuleToPublic : ruleBound <= publicBound := by
    dsimp only [publicBound]
    omega
  have hEndpointToPublic :
      compactCertificateNodeInductionPAPublicCoordinateSizeBound
          endpointInputWeight <= publicBound := by
    dsimp only [publicBound, endpointCoordinateBound]
    unfold compactNumericVerifierPAAxiomJointLeafEndpointCoordinateSizeBound
    omega
  have htail : CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
      c publicBound := by
    exact
      { endpointTable := hendpointPublic.tokenTable.trans hEndpointToPublic
        endpointWidth := hendpointPublic.width.trans hEndpointToPublic
        endpointTokenCount :=
          hendpointPublic.tokenCount.trans hEndpointToPublic
        inputStart := hendpointPublic.inputStart.trans hEndpointToPublic
        inputFinish := hendpointPublic.inputFinish.trans hEndpointToPublic
        endpointAxiomStart :=
          hendpointPublic.axiomStart.trans hEndpointToPublic
        endpointAxiomFinish :=
          hendpointPublic.axiomFinish.trans hEndpointToPublic
        formulaStart := hendpointPublic.formulaStart.trans hEndpointToPublic
        formulaFinish := hendpointPublic.formulaFinish.trans hEndpointToPublic
        suffixStart := hendpointPublic.suffixStart.trans hEndpointToPublic
        suffixFinish := hendpointPublic.suffixFinish.trans hEndpointToPublic
        proofTag := hendpointPublic.certificateTag.trans hEndpointToPublic
        certificateTag :=
          hendpointPublic.certificateTag.trans hEndpointToPublic
        gammaStart := hgammaStartRule.trans hRuleToPublic
        gammaFinish := hgammaFinishRule.trans hRuleToPublic
        gammaBoundarySize := hgammaBoundarySizeRule.trans hRuleToPublic
        candidate := hCandidateBounds.mono hRuleToPublic
        ruleAxiom := hRuleAxiomBounds.mono hRuleToPublic
        fixedEndpoint := inactiveFixedEndpoint_coordinateSizeBounds publicBound
        symbolEndpoint :=
          inactiveSymbolEndpoint_coordinateSizeBounds publicBound
        inductionEndpoint :=
          hinductionCoordinateBounds.mono hEndpointToPublic }
  have henvironment : forall coordinate : Fin 259,
      Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
        c coordinate) <= publicBound := by
    apply compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le
    · intro coordinate
      exact (hruleEnvironment coordinate).trans hRuleToPublic
    · exact htail
  refine ⟨c, hcanonical, ?_⟩
  simpa only [hpublicBound] using henvironment


set_option maxHeartbeats 4000000 in
/-- Canonical completeness with one explicit pointwise public bound for the
entire 259-column PA environment. -/
theorem CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical_with_publicBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    ∃ c, CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c /\
      forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <=
        compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
          Gamma candidate certificate := by
  rcases fixedPAAxiomCertificate_or_induction certificate with
    hfixed | ⟨body, rfl⟩
  · exact exists_fixedCanonicalJoint_with_publicBounds
      Gamma candidate certificate hfixed
  · exact exists_inductionCanonicalJoint_with_publicBounds
      Gamma candidate body

/-- Formula-facing converse, retaining the same public coordinate theorem. -/
theorem
    compactNumericVerifierPAAxiomJointLeafRowsDef_converse_with_publicBounds
    (Gamma : List (List Nat))
    (candidate : LO.FirstOrder.ArithmeticSentence)
    (certificate : PAAxiomCertificate) :
    ∃ c, compactNumericVerifierPAAxiomJointLeafRowsDef.val.Evalb
          (compactNumericVerifierPAAxiomJointLeafRowsEnvironment c) /\
      CompactCanonicalNumericVerifierPAAxiomJointLeafRows
        Gamma candidate certificate c /\
      forall coordinate : Fin 259,
        Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
          c coordinate) <=
        compactNumericVerifierPAAxiomJointLeafPublicCoordinateSizeBound
          Gamma candidate certificate := by
  rcases
      CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical_with_publicBounds
        Gamma candidate certificate with
    ⟨c, hcanonical, hbounds⟩
  exact ⟨c,
    compactNumericVerifierPAAxiomJointLeafRowsDef_spec c |>.2 hcanonical.1,
    hcanonical, hbounds⟩

/-- The parse branches that do not use PA coordinates install the recursively
zero coordinate record.  This proof goes through the 184+75 aggregate
theorems; it does not enumerate `Fin 259`. -/
theorem compactNumericVerifierParseUnusedPACoordinates_size_le_zero
    (coordinate : Fin 259) :
    Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
      compactNumericVerifierParseUnusedPACoordinates coordinate) <= 0 := by
  let c := compactNumericVerifierParseUnusedPACoordinates
  have hroute : CompactGuardedInductionSentenceRoutePublicCoordinateBounds
      c.ruleTable c.ruleWidth c.ruleTokenCount c.depth c.body c.zeroWitness
      c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
      c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
      c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
      c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
      c.depthCapture c.fixed c.generated c.route 0 := by
    dsimp [c, compactNumericVerifierParseUnusedPACoordinates]
    repeat constructor
  have hrule : forall ruleCoordinate : Fin 184,
      Nat.size (compactAdditiveInductionPAAxiomRuleCheckEnvironment
        c.ruleTable c.ruleWidth c.ruleTokenCount c.gammaBoundary c.gammaCount
        c.resultBool c.depth c.ruleAxiom c.body c.zeroWitness
        c.openZeroWitness c.openSuccessorWitness c.captureOne c.empty c.base
        c.negatedBase c.stepZero c.stepSuccessor c.negatedStepZero
        c.stepDisjunction c.quantifiedStep c.negatedQuantifiedStep
        c.quantifiedFinal c.innerDisjunction c.sentence c.fvarList
        c.depthCapture c.fixed c.generated c.candidate c.route
        ruleCoordinate) <= 0 := by
    apply compactAdditiveInductionPAAxiomRuleCheckEnvironment_size_le hroute
    all_goals
      dsimp [c, compactNumericVerifierParseUnusedPACoordinates]
      simp
  have htail : CompactNumericVerifierPAAxiomJointLeafTailCoordinateBounds
      c 0 := by
    dsimp [c, compactNumericVerifierParseUnusedPACoordinates]
    repeat constructor
  exact compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le
    hrule htail coordinate

theorem compactNumericVerifierParseUnusedPACoordinates_size_le
    (bound : Nat) (coordinate : Fin 259) :
    Nat.size (compactNumericVerifierPAAxiomJointLeafRowsEnvironment
      compactNumericVerifierParseUnusedPACoordinates coordinate) <= bound :=
  (compactNumericVerifierParseUnusedPACoordinates_size_le_zero coordinate).trans
    (Nat.zero_le bound)

#print axioms
  CompactNumericVerifierPAAxiomJointLeafRows.exists_canonical_with_publicBounds
#print axioms
  compactNumericVerifierPAAxiomJointLeafRowsDef_converse_with_publicBounds
#print axioms
  compactNumericVerifierPAAxiomJointLeafRowsEnvironment_size_le_at_429
#print axioms
  compactNumericVerifierParseUnusedPACoordinates_size_le_zero

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafStatePublicBounds
