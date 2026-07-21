import integration.FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
import integration.FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
import integration.FoundationCompactNumericListedDirectVerifierParseStateFormula

/-!
# Public bounds for the closed-leaf rule table

The closed branch uses a second, canonical token table for the context,
formula, negated formula, empty list, and complete negation trace.  This file
bounds the twenty-eight coordinates contributed by that table from the weight
of the original proof-token input.  In particular, no rule-table coordinate is
an argument of the public bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafStatePublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedStateBounds
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListWitnessRows
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformValueBounds
open FoundationCompactNumericListedDirectVerifierCombineAuxiliaryBounds
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCanonicalCompleteness
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleSelfContainedGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafParsedRuleGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafCrossTableBridgeGraph
open FoundationCompactNumericListedDirectVerifierLeafParseSuccessTransportGraph
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierClosedLeafStateGraph
open FoundationCompactNumericListedDirectVerifierParseStateFormula

/-- Weight of all five typed values serialized into the canonical closed-rule
table, bounded solely from the original proof-token weight. -/
def compactNumericVerifierClosedLeafCanonicalTokenWeightBound
    (proofWeight : Nat) : Nat :=
  compactNumericNestedListWeightBound proofWeight +
    proofWeight +
    compactFormulaTransformCanonicalOutputWeightBound proofWeight 1 +
    1 +
    compactFormulaTransformCanonicalTraceWeightBound proofWeight 1 0

def compactNumericVerifierClosedLeafCanonicalWidthBound
    (proofWeight : Nat) : Nat :=
  2 * compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight

def compactNumericVerifierClosedLeafCanonicalTableSizeBound
    (proofWeight : Nat) : Nat :=
  compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight *
    compactNumericVerifierClosedLeafCanonicalWidthBound proofWeight

def compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound
    (proofWeight : Nat) : Nat :=
  (compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight + 1) *
    compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight

def compactNumericVerifierClosedLeafCanonicalFuelBound
    (proofWeight : Nat) : Nat :=
  compactNumericCertificateParserFuelWeightBound proofWeight

def compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound
    (proofWeight : Nat) : Nat :=
  (compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight + 2) *
    compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight

def compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound
    (proofWeight : Nat) : Nat :=
  compactFormulaTransformCanonicalTableWidthBound
    (compactNumericVerifierClosedLeafCanonicalWidthBound proofWeight)
    (compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight)
    (compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight)

/-- A common bit-size budget for all twenty-eight closed-extra coordinates.
Every summand is an explicit function of the public proof-token weight. -/
def compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
    (proofWeight : Nat) : Nat :=
  compactNumericVerifierClosedLeafCanonicalTableSizeBound proofWeight +
    compactNumericVerifierClosedLeafCanonicalWidthBound proofWeight +
    compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight +
    compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound proofWeight +
    compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound proofWeight +
    compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight +
    compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound proofWeight +
    64

/-- The two semantic inputs to the closed-rule table are bounded by the
original proof-token weight through the successful proof-node parser. -/
theorem compactListedProofNodeFieldsParser_closedLeaf_sourceWeights
    {proofTokens : List Nat} {proofNode : CompactNumericVerifierTask}
    (hparser : compactListedProofNodeFieldsParser proofTokens = some proofNode) :
    compactAdditiveValueWeight proofNode.2.1 <=
        compactNumericNestedListWeightBound
          (compactAdditiveValueWeight proofTokens) /\
      compactAdditiveValueWeight proofNode.2.2.1 <=
        compactAdditiveValueWeight proofTokens := by
  have hcomponents :=
    compactListedProofNodeFieldsParser_componentsWithin hparser
  exact ⟨hcomponents.1, hcomponents.2.1⟩

/-- Pointwise bounds for the actual twenty-eight coordinates appended by the
closed branch. -/
structure CompactNumericVerifierClosedLeafClosedExtraCoordinateBounds
    (ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound bound : Nat) : Prop where
  ruleTable : Nat.size ruleTable <= bound
  ruleWidth : Nat.size ruleWidth <= bound
  ruleTokenCount : Nat.size ruleTokenCount <= bound
  ruleProofTag : Nat.size ruleProofTag <= bound
  ruleCertificateTag : Nat.size ruleCertificateTag <= bound
  ruleGammaStart : Nat.size ruleGammaStart <= bound
  ruleGammaFinish : Nat.size ruleGammaFinish <= bound
  ruleGammaBoundary : Nat.size ruleGammaBoundary <= bound
  ruleGammaCount : Nat.size ruleGammaCount <= bound
  ruleGammaBoundarySize : Nat.size ruleGammaBoundarySize <= bound
  ruleFormulaStart : Nat.size ruleFormulaStart <= bound
  ruleFormulaFinish : Nat.size ruleFormulaFinish <= bound
  ruleFormulaBoundary : Nat.size ruleFormulaBoundary <= bound
  ruleFormulaCount : Nat.size ruleFormulaCount <= bound
  ruleFormulaBoundarySize : Nat.size ruleFormulaBoundarySize <= bound
  ruleNegatedStart : Nat.size ruleNegatedStart <= bound
  ruleNegatedFinish : Nat.size ruleNegatedFinish <= bound
  ruleNegatedBoundary : Nat.size ruleNegatedBoundary <= bound
  ruleNegatedCount : Nat.size ruleNegatedCount <= bound
  ruleNegatedBoundarySize : Nat.size ruleNegatedBoundarySize <= bound
  ruleStateBoundary : Nat.size ruleStateBoundary <= bound
  ruleStateCount : Nat.size ruleStateCount <= bound
  ruleEmptyStart : Nat.size ruleEmptyStart <= bound
  ruleEmptyFinish : Nat.size ruleEmptyFinish <= bound
  ruleEmptyBoundary : Nat.size ruleEmptyBoundary <= bound
  ruleEmptyBoundarySize : Nat.size ruleEmptyBoundarySize <= bound
  ruleTableWidth : Nat.size ruleTableWidth <= bound
  ruleValueBound : Nat.size ruleValueBound <= bound

/-- The aggregate `Fin 28` form used by the parse-state environment. -/
theorem compactNumericVerifierParseClosedExtraEnvironment_size_le
    {ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound bound : Nat}
    (hbounds : CompactNumericVerifierClosedLeafClosedExtraCoordinateBounds
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound bound)
    (coordinate : Fin 28) :
    Nat.size
        (compactNumericVerifierParseClosedExtraEnvironment
          ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
          ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
          ruleGammaBoundarySize
          ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
          ruleFormulaBoundarySize
          ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
          ruleNegatedCount ruleNegatedBoundarySize
          ruleStateBoundary ruleStateCount
          ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
          ruleTableWidth ruleValueBound coordinate) <= bound := by
  rcases hbounds with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
      h20, h21, h22, h23, h24, h25, h26, h27⟩
  fin_cases coordinate <;>
    simp [compactNumericVerifierParseClosedExtraEnvironment] <;> assumption

/-- Numerical facts retained from the forward canonical construction.  The
self-contained graph supplies all list starts, finishes, counts, and list
boundary certificates; only facts not recoverable from an arbitrary padded
graph are retained here. -/
structure CompactNumericVerifierClosedLeafCanonicalNumericBounds
    (ruleTable ruleWidth ruleTokenCount ruleStateBoundary ruleStateCount
      ruleTableWidth ruleValueBound proofWeight : Nat) : Prop where
  ruleTable : Nat.size ruleTable <=
    compactNumericVerifierClosedLeafCanonicalTableSizeBound proofWeight
  ruleWidth : ruleWidth <=
    compactNumericVerifierClosedLeafCanonicalWidthBound proofWeight
  ruleTokenCount : ruleTokenCount <=
    compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight
  ruleStateBoundary : Nat.size ruleStateBoundary <=
    compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound proofWeight
  ruleStateCount : ruleStateCount <=
    compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight + 1
  ruleTableWidth_le : ruleTableWidth <=
    compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound proofWeight
  ruleValueBound_eq : ruleValueBound = 2 ^ ruleTableWidth

private theorem compactAdditiveTokenList_length_le_weight
    (tokens : List Nat) :
    tokens.length <= compactAdditiveTokenWeight tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      simp only [List.length_cons, compactAdditiveTokenWeight_cons]
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

theorem
    compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound left <=
      compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
        right := by
  have hnested := compactNumericNestedListWeightBound_mono h
  have houtput := compactFormulaTransformCanonicalOutputWeightBound_mono
    h (Nat.le_refl 1)
  have htrace := compactFormulaTransformCanonicalTraceWeightBound_mono
    h (Nat.le_refl 1) (Nat.le_refl 0)
  have htoken :
      compactNumericVerifierClosedLeafCanonicalTokenWeightBound left <=
        compactNumericVerifierClosedLeafCanonicalTokenWeightBound right := by
    unfold compactNumericVerifierClosedLeafCanonicalTokenWeightBound
    omega
  have hwidth :
      compactNumericVerifierClosedLeafCanonicalWidthBound left <=
        compactNumericVerifierClosedLeafCanonicalWidthBound right := by
    unfold compactNumericVerifierClosedLeafCanonicalWidthBound
    exact Nat.mul_le_mul_left 2 htoken
  have htable :
      compactNumericVerifierClosedLeafCanonicalTableSizeBound left <=
        compactNumericVerifierClosedLeafCanonicalTableSizeBound right := by
    unfold compactNumericVerifierClosedLeafCanonicalTableSizeBound
    exact Nat.mul_le_mul htoken hwidth
  have hlist :
      compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound left <=
        compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound
          right := by
    unfold compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound
    exact Nat.mul_le_mul (Nat.add_le_add_right htoken 1) htoken
  have hfuel :
      compactNumericVerifierClosedLeafCanonicalFuelBound left <=
        compactNumericVerifierClosedLeafCanonicalFuelBound right := by
    unfold compactNumericVerifierClosedLeafCanonicalFuelBound
    exact compactNumericCertificateParserFuelWeightBound_mono h
  have hstate :
      compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound left <=
        compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound
          right := by
    unfold compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound
    exact Nat.mul_le_mul (Nat.add_le_add_right hfuel 2) htoken
  have htransform :
      compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound left <=
        compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound
          right := by
    unfold compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound
    exact compactFormulaTransformCanonicalTableWidthBound_mono
      hwidth htoken hfuel
  unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
  omega

/- The real self-contained graph controls every ordinary list coordinate.
The canonical numeric package controls only the table code and transform data
that an arbitrarily padded satisfying graph could otherwise enlarge. -/
theorem
    CompactNumericVerifierClosedLeafRuleSelfContainedGraph.closedExtraCoordinateBounds_of_canonical
    {ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound resultBool proofWeight : Nat}
    (hgraph : CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
        ruleNegatedBoundarySize
      ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound resultBool)
    (hcanonical : CompactNumericVerifierClosedLeafCanonicalNumericBounds
      ruleTable ruleWidth ruleTokenCount ruleStateBoundary ruleStateCount
      ruleTableWidth ruleValueBound proofWeight) :
    CompactNumericVerifierClosedLeafClosedExtraCoordinateBounds
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound
      (compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
        proofWeight) := by
  rcases hgraph with ⟨hgamma, hformula, hnegated, hempty, hleaf⟩
  rcases hcanonical with
    ⟨htable, hwidth, htokenCount, hstateBoundary, hstateCount,
      htableWidth, hvalueBound⟩
  have hgammaCoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hgamma.1
  have hformulaCoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hformula.1
  have hnegatedCoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hnegated.1
  have hemptyCoordinates :=
    compactAdditiveStructuredListLayout_coordinates_le hempty.1
  let tokenBound :=
    compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight
  let tableBound :=
    compactNumericVerifierClosedLeafCanonicalTableSizeBound proofWeight
  let widthBound :=
    compactNumericVerifierClosedLeafCanonicalWidthBound proofWeight
  let listBoundaryBound :=
    compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound proofWeight
  let stateBoundaryBound :=
    compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound proofWeight
  let fuelBound :=
    compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight
  let transformWidthBound :=
    compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound proofWeight
  let publicBound :=
    compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      proofWeight
  have htablePublic : Nat.size ruleTable <= publicBound := by
    exact htable.trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have hwidthPublic : Nat.size ruleWidth <= publicBound := by
    exact (natSize_le_of_le hwidth).trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have htokenPublic : Nat.size ruleTokenCount <= publicBound := by
    exact (natSize_le_of_le htokenCount).trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have htokenValuePublic : ruleTokenCount <= tokenBound := by
    simpa only [tokenBound] using htokenCount
  have hpositionPublic {value : Nat} (hvalue : value <= ruleTokenCount) :
      Nat.size value <= publicBound := by
    exact (natSize_le_of_le (hvalue.trans htokenValuePublic)).trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have hlistBoundaryPublic
      {boundary count boundarySize : Nat}
      (hcount : count <= ruleTokenCount)
      (hsizeEq : boundarySize = Nat.size boundary)
      (hsize : boundarySize <= (count + 1) * ruleTokenCount) :
      Nat.size boundary <= publicBound /\
        Nat.size boundarySize <= publicBound := by
    have harea : (count + 1) * ruleTokenCount <=
        (tokenBound + 1) * tokenBound :=
      Nat.mul_le_mul
        (Nat.add_le_add_right (hcount.trans htokenValuePublic) 1)
        htokenValuePublic
    have hboundary : Nat.size boundary <= listBoundaryBound := by
      rw [← hsizeEq]
      exact hsize.trans (by
        simpa only [listBoundaryBound,
          compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound]
          using harea)
    have hboundarySize : Nat.size boundarySize <= listBoundaryBound :=
      (natSize_le_of_le (Nat.le_refl boundarySize)).trans
        (hsize.trans (by
          simpa only [listBoundaryBound,
            compactNumericVerifierClosedLeafCanonicalListBoundarySizeBound]
            using harea))
    exact ⟨hboundary.trans (by
        dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
          stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
        unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
        omega),
      hboundarySize.trans (by
        dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
          stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
        unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
        omega)⟩
  have hgammaBoundary := hlistBoundaryPublic
    hgammaCoordinates.2.1 hgamma.2.2.1 hgamma.2.2.2
  have hformulaBoundary := hlistBoundaryPublic
    hformulaCoordinates.2.1 hformula.2.2.1 hformula.2.2.2
  have hnegatedBoundary := hlistBoundaryPublic
    hnegatedCoordinates.2.1 hnegated.2.2.1 hnegated.2.2.2
  have hemptyBoundary := hlistBoundaryPublic
    hemptyCoordinates.2.1 hempty.2.2.1 hempty.2.2.2
  have hstateBoundaryPublic : Nat.size ruleStateBoundary <= publicBound :=
    hstateBoundary.trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have hstateCountPublic : Nat.size ruleStateCount <= publicBound :=
    (natSize_le_of_le hstateCount).trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have htableWidthPublic : Nat.size ruleTableWidth <= publicBound :=
    (natSize_le_of_le htableWidth).trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have hvalueBoundPublic : Nat.size ruleValueBound <= publicBound := by
    rw [hvalueBound, Nat.size_pow]
    exact (Nat.add_le_add_right htableWidth 1).trans (by
      dsimp only [tableBound, widthBound, tokenBound, listBoundaryBound,
        stateBoundaryBound, fuelBound, transformWidthBound, publicBound]
      unfold compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
      omega)
  have hproofTagPublic : Nat.size ruleProofTag <= publicBound := by
    rw [hleaf.1]
    simp only [Nat.size_zero, Nat.zero_le]
  have hcertificateTagPublic : Nat.size ruleCertificateTag <= publicBound := by
    rw [hleaf.2.1]
    simp only [Nat.size_zero, Nat.zero_le]
  exact
    { ruleTable := htablePublic
      ruleWidth := hwidthPublic
      ruleTokenCount := htokenPublic
      ruleProofTag := hproofTagPublic
      ruleCertificateTag := hcertificateTagPublic
      ruleGammaStart := hpositionPublic hgammaCoordinates.1
      ruleGammaFinish := hpositionPublic hgammaCoordinates.2.2
      ruleGammaBoundary := hgammaBoundary.1
      ruleGammaCount := hpositionPublic hgammaCoordinates.2.1
      ruleGammaBoundarySize := hgammaBoundary.2
      ruleFormulaStart := hpositionPublic hformulaCoordinates.1
      ruleFormulaFinish := hpositionPublic hformulaCoordinates.2.2
      ruleFormulaBoundary := hformulaBoundary.1
      ruleFormulaCount := hpositionPublic hformulaCoordinates.2.1
      ruleFormulaBoundarySize := hformulaBoundary.2
      ruleNegatedStart := hpositionPublic hnegatedCoordinates.1
      ruleNegatedFinish := hpositionPublic hnegatedCoordinates.2.2
      ruleNegatedBoundary := hnegatedBoundary.1
      ruleNegatedCount := hpositionPublic hnegatedCoordinates.2.1
      ruleNegatedBoundarySize := hnegatedBoundary.2
      ruleStateBoundary := hstateBoundaryPublic
      ruleStateCount := hstateCountPublic
      ruleEmptyStart := hpositionPublic hemptyCoordinates.1
      ruleEmptyFinish := hpositionPublic hemptyCoordinates.2.2
      ruleEmptyBoundary := hemptyBoundary.1
      ruleEmptyBoundarySize := hemptyBoundary.2
      ruleTableWidth := htableWidthPublic
      ruleValueBound := hvalueBoundPublic }

/- Canonical construction of the real closed-rule table, retaining the
forward numerical inequalities that the unbounded completeness theorem
intentionally discards. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericVerifierClosedLeafRuleSelfContainedGraph_with_publicBounds
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0)
    (proofWeight : Nat)
    (hGammaWeight : compactAdditiveValueWeight Gamma <=
      compactNumericNestedListWeightBound proofWeight)
    (hformulaWeight : compactAdditiveValueWeight
      (compactArithmeticFormulaTokens parsed) <= proofWeight) :
    let formula := compactArithmeticFormulaTokens parsed
    let negated := compactArithmeticFormulaTokens (∼parsed)
    exists tokenTable width tokenCount,
    exists gammaStart gammaFinish gammaBoundary gammaBoundarySize,
    exists formulaStart formulaFinish formulaBoundary formulaBoundarySize,
    exists negatedStart negatedFinish negatedBoundary negatedBoundarySize,
    exists stateBoundary,
    exists emptyStart emptyFinish emptyBoundary emptyBoundarySize,
    exists tableWidth valueBound,
      CompactNumericVerifierClosedLeafRuleSelfContainedGraph
        tokenTable width tokenCount 0 0
        gammaStart gammaFinish gammaBoundary Gamma.length gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formula.length
          formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negated.length
          negatedBoundarySize
        stateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound
        (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) /\
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount gammaStart gammaFinish Gamma /\
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount formulaStart formulaFinish formula /\
      CompactNumericVerifierClosedLeafCanonicalNumericBounds
        tokenTable width tokenCount stateBoundary
        (compactSyntaxRunFuelBound formula + 1) tableWidth valueBound
        proofWeight /\
      CompactNumericVerifierClosedLeafClosedExtraCoordinateBounds
        tokenTable width tokenCount 0 0
        gammaStart gammaFinish gammaBoundary Gamma.length gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formula.length
          formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negated.length
          negatedBoundarySize
        stateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound
        (compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
          proofWeight) /\
      forall coordinate : Fin 28,
        Nat.size
          (compactNumericVerifierParseClosedExtraEnvironment
            tokenTable width tokenCount 0 0
            gammaStart gammaFinish gammaBoundary Gamma.length gammaBoundarySize
            formulaStart formulaFinish formulaBoundary formula.length
              formulaBoundarySize
            negatedStart negatedFinish negatedBoundary negated.length
              negatedBoundarySize
            stateBoundary (compactSyntaxRunFuelBound formula + 1)
            emptyStart emptyFinish emptyBoundary emptyBoundarySize
            tableWidth valueBound coordinate) <=
          compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
            proofWeight := by
  dsimp only
  let formula := compactArithmeticFormulaTokens parsed
  let negated := compactArithmeticFormulaTokens (∼parsed)
  let empty : List Nat := []
  let trace := compactFormulaTransformStateTrace (3, [])
    (compactSyntaxRunFuelBound formula)
    (compactFormulaTransformInitialState 0 formula)
  let chunks := compactClosedLeafCanonicalChunks Gamma parsed
  let tokens := chunks.flatten
  let width := (compactBinaryNatPayloadBits tokens).length
  let tokenTable := compactFixedWidthTableCode width tokens
  let gammaStart := (compactPackedChunkPrefix chunks 0).length
  let gammaFinish := gammaStart + (compactAdditiveEncode Gamma).length
  let gammaBoundary := compactPackedNatListListBoundary chunks 0 Gamma
  let formulaSlot := compactPackedNatListSlot chunks 1 formula
  let negatedSlot := compactPackedNatListSlot chunks 2 negated
  let emptySlot := compactPackedNatListSlot chunks 3 empty
  let stateBoundary := compactPackedFormulaTransformStateBoundary chunks 4 trace
  have hnegatedWeightRaw :
      compactAdditiveValueWeight negated <=
        compactFormulaTransformCanonicalOutputWeightBound
          (compactAdditiveValueWeight formula) 1 := by
    simpa [formula, negated] using
      (compactFormulaNegationExact_getD_weight_le 0 formula)
  have hnegatedWeight :
      compactAdditiveValueWeight negated <=
        compactFormulaTransformCanonicalOutputWeightBound proofWeight 1 :=
    hnegatedWeightRaw.trans
      (compactFormulaTransformCanonicalOutputWeightBound_mono
        (by simpa only [formula] using hformulaWeight)
        (Nat.le_refl 1))
  have htraceWeightRaw :
      compactAdditiveValueWeight trace <=
        compactFormulaTransformCanonicalTraceWeightBound
          (compactAdditiveValueWeight formula) 1 0 := by
    simpa [trace] using
      (compactFormulaTransformCanonicalStateTrace_weight_le
        3 0 [] formula (by omega))
  have htraceWeight :
      compactAdditiveValueWeight trace <=
        compactFormulaTransformCanonicalTraceWeightBound proofWeight 1 0 :=
    htraceWeightRaw.trans
      (compactFormulaTransformCanonicalTraceWeightBound_mono
        (by simpa only [formula] using hformulaWeight)
        (Nat.le_refl 1) (Nat.le_refl 0))
  have htokenWeightExact :
      compactAdditiveTokenWeight tokens =
        compactAdditiveValueWeight Gamma +
          compactAdditiveValueWeight formula +
          compactAdditiveValueWeight negated +
          compactAdditiveValueWeight empty +
          compactAdditiveValueWeight trace := by
    change compactAdditiveTokenWeight
      (compactAdditiveEncode Gamma ++
        (compactAdditiveEncode formula ++
          (compactAdditiveEncode negated ++
            (compactAdditiveEncode empty ++
              (compactAdditiveEncode trace ++ []))))) = _
    simp only [compactAdditiveTokenWeight_append,
      compactAdditiveTokenWeight_nil]
    change compactAdditiveValueWeight Gamma +
      (compactAdditiveValueWeight formula +
        (compactAdditiveValueWeight negated +
          (compactAdditiveValueWeight empty +
            (compactAdditiveValueWeight trace + 0)))) = _
    omega
  have htokenWeight :
      compactAdditiveTokenWeight tokens <=
        compactNumericVerifierClosedLeafCanonicalTokenWeightBound
          proofWeight := by
    rw [htokenWeightExact]
    have hformulaWeight' : compactAdditiveValueWeight formula <= proofWeight := by
      simpa only [formula] using hformulaWeight
    have hemptyWeight : compactAdditiveValueWeight empty = 1 := by
      simp [empty]
    rw [hemptyWeight]
    unfold compactNumericVerifierClosedLeafCanonicalTokenWeightBound
    omega
  have htokenCount :
      tokens.length <=
        compactNumericVerifierClosedLeafCanonicalTokenWeightBound proofWeight :=
    (compactAdditiveTokenList_length_le_weight tokens).trans htokenWeight
  have hwidth :
      width <=
        compactNumericVerifierClosedLeafCanonicalWidthBound proofWeight := by
    change compactAdditiveTokenBitLength tokens <= _
    rw [compactAdditiveTokenBitLength_eq_two_mul_weight]
    unfold compactNumericVerifierClosedLeafCanonicalWidthBound
    exact Nat.mul_le_mul_left 2 htokenWeight
  have htable :
      Nat.size tokenTable <=
        compactNumericVerifierClosedLeafCanonicalTableSizeBound proofWeight := by
    exact (compactFixedWidthTableCode_size_le width tokens).trans
      (by
        unfold compactNumericVerifierClosedLeafCanonicalTableSizeBound
        exact Nat.mul_le_mul htokenCount hwidth)
  have hfuel :
      compactSyntaxRunFuelBound formula <=
        compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight := by
    unfold compactNumericVerifierClosedLeafCanonicalFuelBound
    exact compactSyntaxRunFuelBound_le_weightBound
      (by simpa only [formula] using hformulaWeight)
  have hformulaSlot := compactPackedNatListSlot_canonical chunks 1 formula
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, formula])
  have hnegatedSlot := compactPackedNatListSlot_canonical chunks 2 negated
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, negated])
  have hemptySlot := compactPackedNatListSlot_canonical chunks 3 empty
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, empty])
  have htraceRows :=
    compactPackedFormulaTransformStateRows_canonical_with_size
      chunks 4 trace
      (by simp [chunks, compactClosedLeafCanonicalChunks])
      (by simp [chunks, compactClosedLeafCanonicalChunks, trace, formula])
  dsimp only at hformulaSlot hnegatedSlot hemptySlot htraceRows
  let gammaFront := compactPackedChunkPrefix chunks 0
  let gammaBack := compactPackedChunkSuffix chunks 0
  have hgammaTokens :
      gammaFront ++ compactAdditiveEncode Gamma ++ gammaBack =
        chunks.flatten := by
    simp only [gammaFront, gammaBack]
    exact compactPackedChunkPrefix_append_getElem_append_suffix chunks 0
      (by simp [chunks, compactClosedLeafCanonicalChunks])
  have hgammaRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactAdditiveNatListDirectLayout
      compactAdditiveNatListDirectLayout_canonical gammaFront Gamma gammaBack
  dsimp only at hgammaRaw
  rw [hgammaTokens] at hgammaRaw
  have hgammaStructure : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length gammaStart Gamma.length gammaFinish
        gammaBoundary := by
    simpa [tokenTable, width, tokens, gammaStart, gammaFinish, gammaBoundary,
      compactPackedNatListListBoundary, gammaFront] using hgammaRaw.1
  have hgammaSize : Nat.size gammaBoundary <=
      (Gamma.length + 1) * tokens.length := by
    simpa [tokens, gammaStart, gammaBoundary,
      compactPackedNatListListBoundary, gammaFront] using hgammaRaw.2.2
  have hgammaRows : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokens.length
        gammaBoundary Gamma := by
    simpa [tokenTable, width, tokens, gammaStart, gammaBoundary, gammaFront,
      compactPackedNatListListBoundary] using hgammaRaw.2.1
  have hgammaLayout : CompactAdditiveNatListListDirectLayout
      tokenTable width tokens.length gammaStart gammaFinish Gamma :=
    ⟨gammaBoundary, hgammaStructure, hgammaRows, hgammaSize⟩
  have hgammaWitness : CompactAdditiveNatListListWitnessRows
      tokenTable width tokens.length gammaStart Gamma.length gammaFinish
      gammaBoundary (Nat.size gammaBoundary) :=
    ⟨hgammaStructure,
      FoundationCompactNumericListedDirectNatListListRowsFormula.CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hgammaRows,
      rfl, hgammaSize⟩
  have hformulaLayout : CompactAdditiveNatListDirectLayout
      tokenTable width tokens.length formulaSlot.start formulaSlot.finish formula :=
    hformulaSlot.layout
  have hformulaRows := hformulaSlot.elements
  have hnegatedLayout := hnegatedSlot.layout
  have hnegatedRows := hnegatedSlot.elements
  have hemptyLayout := hemptySlot.layout
  have hemptyRows := hemptySlot.elements
  have htraceRows' : CompactFormulaTransformStateListRowLayouts
      tokenTable width tokens.length stateBoundary trace := by
    simpa [tokenTable, width, tokens, stateBoundary] using htraceRows.1
  have hstateBoundary : Nat.size stateBoundary <=
      compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound
        proofWeight := by
    have hraw : Nat.size stateBoundary <=
        (trace.length + 1) * tokens.length := by
      simpa [tokenTable, width, tokens, stateBoundary] using htraceRows.2
    have htraceLength : trace.length + 1 <=
        compactNumericVerifierClosedLeafCanonicalFuelBound proofWeight + 2 := by
      simp only [trace, compactFormulaTransformStateTrace_length]
      omega
    exact hraw.trans (by
      unfold compactNumericVerifierClosedLeafCanonicalStateBoundarySizeBound
      exact Nat.mul_le_mul htraceLength htokenCount)
  have hnegatedExact : compactFormulaNegationExact 0 formula = some negated := by
    simp [formula, negated]
  rcases
      CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace_with_width_bound
        htraceRows' hemptyLayout rfl hformulaRows hnegatedRows hemptyRows
        (by
          rw [compactFormulaTransformResult_negation]
          change negated = (compactFormulaNegationExact 0 formula).getD []
          rw [hnegatedExact]
          simp) with
    ⟨tableWidth, htransform, htableWidthRaw⟩
  have htableWidth : tableWidth <=
      compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound
        proofWeight := by
    exact htableWidthRaw.trans (by
      unfold
        compactNumericVerifierClosedLeafCanonicalTransformTableWidthBound
      exact compactFormulaTransformCanonicalTableWidthBound_mono
        hwidth htokenCount hfuel)
  have hleaf : CompactNumericVerifierClosedLeafRuleRows
      tokenTable width tokens.length 0 0 gammaBoundary Gamma.length
      formulaSlot.start formulaSlot.finish formulaSlot.boundary formula.length
      negatedSlot.start negatedSlot.finish negatedSlot.boundary negated.length
      stateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptySlot.start emptySlot.finish emptySlot.boundary
      tableWidth (2 ^ tableWidth)
      (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) :=
    CompactNumericVerifierClosedLeafRuleRows.of_components
      htransform hgammaRows hformulaLayout hformulaRows hnegatedLayout
      hnegatedRows hemptyLayout hemptyRows ⟨parsed, rfl⟩
  have hself : CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      tokenTable width tokens.length 0 0
      gammaStart gammaFinish gammaBoundary Gamma.length
        (Nat.size gammaBoundary)
      formulaSlot.start formulaSlot.finish formulaSlot.boundary formula.length
        formulaSlot.boundarySize
      negatedSlot.start negatedSlot.finish negatedSlot.boundary negated.length
        negatedSlot.boundarySize
      stateBoundary (compactSyntaxRunFuelBound formula + 1)
      emptySlot.start emptySlot.finish emptySlot.boundary emptySlot.boundarySize
      tableWidth (2 ^ tableWidth)
      (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) :=
    ⟨hgammaWitness, hformulaSlot.rows, hnegatedSlot.rows,
      hemptySlot.rows, hleaf⟩
  have hcanonical : CompactNumericVerifierClosedLeafCanonicalNumericBounds
      tokenTable width tokens.length stateBoundary
      (compactSyntaxRunFuelBound formula + 1)
      tableWidth (2 ^ tableWidth) proofWeight :=
    { ruleTable := htable
      ruleWidth := hwidth
      ruleTokenCount := htokenCount
      ruleStateBoundary := hstateBoundary
      ruleStateCount := Nat.add_le_add_right hfuel 1
      ruleTableWidth_le := htableWidth
      ruleValueBound_eq := rfl }
  have hcoordinateBounds :=
    CompactNumericVerifierClosedLeafRuleSelfContainedGraph.closedExtraCoordinateBounds_of_canonical
      hself hcanonical
  have henvironmentBounds :=
    compactNumericVerifierParseClosedExtraEnvironment_size_le
      hcoordinateBounds
  exact ⟨tokenTable, width, tokens.length,
    gammaStart, gammaFinish, gammaBoundary, Nat.size gammaBoundary,
    formulaSlot.start, formulaSlot.finish, formulaSlot.boundary,
      formulaSlot.boundarySize,
    negatedSlot.start, negatedSlot.finish, negatedSlot.boundary,
      negatedSlot.boundarySize,
    stateBoundary,
    emptySlot.start, emptySlot.finish, emptySlot.boundary,
      emptySlot.boundarySize,
    tableWidth, 2 ^ tableWidth,
    hself, hgammaLayout, hformulaLayout, hcanonical,
    hcoordinateBounds, henvironmentBounds⟩

/- The bounded canonical table is connected to the exposed parser root by the
same real cross-table bridge used by the closed-state graph. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericVerifierClosedLeafParsedRuleGraph_with_publicBounds
    {stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize proofWeight : Nat}
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0)
    (hsuccess : CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize)
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish Gamma)
    (hrootFormula : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount rootGammaFinish firstFinish
        (compactArithmeticFormulaTokens parsed))
    (hproofTag : proofTag = 0)
    (hcertificateTag : certificateTag = 0)
    (hGammaWeight : compactAdditiveValueWeight Gamma <=
      compactNumericNestedListWeightBound proofWeight)
    (hformulaWeight : compactAdditiveValueWeight
      (compactArithmeticFormulaTokens parsed) <= proofWeight) :
    let formula := compactArithmeticFormulaTokens parsed
    let negated := compactArithmeticFormulaTokens (∼parsed)
    exists ruleTable ruleWidth ruleTokenCount,
    exists ruleGammaStart ruleGammaFinish ruleGammaBoundary
      ruleGammaBoundarySize,
    exists ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
      ruleFormulaBoundarySize,
    exists ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
      ruleNegatedBoundarySize,
    exists ruleStateBoundary,
    exists ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
      ruleEmptyBoundarySize,
    exists ruleTableWidth ruleValueBound,
      CompactNumericVerifierClosedLeafParsedRuleGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart
          stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula)))
        ruleTable ruleWidth ruleTokenCount 0 0
        ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
          ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary formula.length
          ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary negated.length
          ruleNegatedBoundarySize
        ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
        ruleTableWidth ruleValueBound /\
      CompactNumericVerifierClosedLeafCanonicalNumericBounds
        ruleTable ruleWidth ruleTokenCount ruleStateBoundary
        (compactSyntaxRunFuelBound formula + 1)
        ruleTableWidth ruleValueBound proofWeight /\
      CompactNumericVerifierClosedLeafClosedExtraCoordinateBounds
        ruleTable ruleWidth ruleTokenCount 0 0
        ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
          ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary formula.length
          ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary negated.length
          ruleNegatedBoundarySize
        ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
        ruleTableWidth ruleValueBound
        (compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
          proofWeight) /\
      forall coordinate : Fin 28,
        Nat.size
          (compactNumericVerifierParseClosedExtraEnvironment
            ruleTable ruleWidth ruleTokenCount 0 0
            ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
              ruleGammaBoundarySize
            ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
              formula.length ruleFormulaBoundarySize
            ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
              negated.length ruleNegatedBoundarySize
            ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
            ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
              ruleEmptyBoundarySize
            ruleTableWidth ruleValueBound coordinate) <=
          compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
            proofWeight := by
  dsimp only
  let formula := compactArithmeticFormulaTokens parsed
  let negated := compactArithmeticFormulaTokens (∼parsed)
  rcases
      exists_compactNumericVerifierClosedLeafRuleSelfContainedGraph_with_publicBounds
        Gamma parsed proofWeight hGammaWeight hformulaWeight with
    ⟨ruleTable, ruleWidth, ruleTokenCount,
      ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
      ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
      ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize,
      ruleStateBoundary,
      ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize,
      ruleTableWidth, ruleValueBound,
      hrule, hruleGamma, hruleFormula, hcanonical,
      hcoordinateBounds, henvironmentBounds⟩
  have hbridge : CompactNumericVerifierClosedLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      rootGammaFinish firstFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish :=
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph.of_layouts
      hrootGamma hruleGamma hrootFormula hruleFormula
  have hparsed : CompactNumericVerifierClosedLeafParsedRuleGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula)))
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary formula.length
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary negated.length
        ruleNegatedBoundarySize
      ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound :=
    ⟨hsuccess, hrule, hproofTag, hcertificateTag, hbridge⟩
  exact ⟨ruleTable, ruleWidth, ruleTokenCount,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize,
    ruleStateBoundary,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize,
    ruleTableWidth, ruleValueBound,
    hparsed, hcanonical, hcoordinateBounds, henvironmentBounds⟩

/-- Direct projection from the real closed state graph.  The proof uses its
actual parsed-rule/self-contained conjunct, rather than an unrelated list of
twenty-eight inequalities. -/
theorem
    CompactNumericVerifierClosedLeafStateGraph.closedExtraEnvironment_size_le_of_canonical
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound proofWeight : Nat}
    (hgraph : CompactNumericVerifierClosedLeafStateGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound)
    (hcanonical : CompactNumericVerifierClosedLeafCanonicalNumericBounds
      ruleTable ruleWidth ruleTokenCount ruleStateBoundary ruleStateCount
      ruleTableWidth ruleValueBound proofWeight)
    (coordinate : Fin 28) :
    Nat.size
        (compactNumericVerifierParseClosedExtraEnvironment
          ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
          ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
          ruleGammaBoundarySize
          ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
          ruleFormulaBoundarySize
          ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
          ruleNegatedCount ruleNegatedBoundarySize
          ruleStateBoundary ruleStateCount
          ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
          ruleTableWidth ruleValueBound coordinate) <=
      compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
        proofWeight := by
  exact compactNumericVerifierParseClosedExtraEnvironment_size_le
    (CompactNumericVerifierClosedLeafRuleSelfContainedGraph.closedExtraCoordinateBounds_of_canonical
      hgraph.2.2.1 hcanonical)
    coordinate

/- A bounded closed state is obtained by attaching the bounded canonical rule
table to an already constructed successful leaf transport. -/
set_option maxHeartbeats 2400000 in
theorem
    exists_compactNumericVerifierClosedLeafStateGraph_with_publicBounds_of_transport
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      proofWeight : Nat}
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0)
    (htransport : CompactNumericVerifierLeafParseSuccessTransportGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag
        (compactClosedRuleCheck
          (Gamma, compactArithmeticFormulaTokens parsed))))
    (hrootGamma : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) rootGammaFinish Gamma)
    (hrootFormula : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount rootGammaFinish firstFinish
        (compactArithmeticFormulaTokens parsed))
    (hproofTag : proofTag = 0)
    (hcertificateTag : certificateTag = 0)
    (hGammaWeight : compactAdditiveValueWeight Gamma <=
      compactNumericNestedListWeightBound proofWeight)
    (hformulaWeight : compactAdditiveValueWeight
      (compactArithmeticFormulaTokens parsed) <= proofWeight) :
    let formula := compactArithmeticFormulaTokens parsed
    let negated := compactArithmeticFormulaTokens (∼parsed)
    exists ruleTable ruleWidth ruleTokenCount,
    exists ruleGammaStart ruleGammaFinish ruleGammaBoundary
      ruleGammaBoundarySize,
    exists ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
      ruleFormulaBoundarySize,
    exists ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
      ruleNegatedBoundarySize,
    exists ruleStateBoundary,
    exists ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
      ruleEmptyBoundarySize,
    exists ruleTableWidth ruleValueBound,
      CompactNumericVerifierClosedLeafStateGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish stateCertificateStart
          stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        rootGammaBoundarySize
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize
        (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula)))
        ruleTable ruleWidth ruleTokenCount 0 0
        ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
          ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary formula.length
          ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary negated.length
          ruleNegatedBoundarySize
        ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
        ruleTableWidth ruleValueBound /\
      CompactNumericVerifierClosedLeafCanonicalNumericBounds
        ruleTable ruleWidth ruleTokenCount ruleStateBoundary
        (compactSyntaxRunFuelBound formula + 1)
        ruleTableWidth ruleValueBound proofWeight /\
      CompactNumericVerifierClosedLeafClosedExtraCoordinateBounds
        ruleTable ruleWidth ruleTokenCount 0 0
        ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
          ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary formula.length
          ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary negated.length
          ruleNegatedBoundarySize
        ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
        ruleTableWidth ruleValueBound
        (compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
          proofWeight) /\
      forall coordinate : Fin 28,
        Nat.size
          (compactNumericVerifierParseClosedExtraEnvironment
            ruleTable ruleWidth ruleTokenCount 0 0
            ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
              ruleGammaBoundarySize
            ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
              formula.length ruleFormulaBoundarySize
            ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
              negated.length ruleNegatedBoundarySize
            ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
            ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
              ruleEmptyBoundarySize
            ruleTableWidth ruleValueBound coordinate) <=
          compactNumericVerifierClosedLeafClosedExtraPublicCoordinateSizeBound
            proofWeight := by
  dsimp only
  let formula := compactArithmeticFormulaTokens parsed
  let negated := compactArithmeticFormulaTokens (∼parsed)
  rcases
      exists_compactNumericVerifierClosedLeafParsedRuleGraph_with_publicBounds
        Gamma parsed htransport.1 hrootGamma hrootFormula
        hproofTag hcertificateTag hGammaWeight hformulaWeight with
    ⟨ruleTable, ruleWidth, ruleTokenCount,
      ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
      ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
      ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize,
      ruleStateBoundary,
      ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize,
      ruleTableWidth, ruleValueBound,
      hparsed, hcanonical, hcoordinateBounds, henvironmentBounds⟩
  have hstate : CompactNumericVerifierClosedLeafStateGraph
      stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize
      (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula)))
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary Gamma.length
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary formula.length
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary negated.length
        ruleNegatedBoundarySize
      ruleStateBoundary (compactSyntaxRunFuelBound formula + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound :=
    ⟨htransport, hparsed⟩
  exact ⟨ruleTable, ruleWidth, ruleTokenCount,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize,
    ruleStateBoundary,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize,
    ruleTableWidth, ruleValueBound,
    hstate, hcanonical, hcoordinateBounds, henvironmentBounds⟩

#print axioms compactNumericVerifierParseClosedExtraEnvironment_size_le
#print axioms compactListedProofNodeFieldsParser_closedLeaf_sourceWeights
#print axioms
  CompactNumericVerifierClosedLeafRuleSelfContainedGraph.closedExtraCoordinateBounds_of_canonical
#print axioms
  exists_compactNumericVerifierClosedLeafRuleSelfContainedGraph_with_publicBounds
#print axioms
  exists_compactNumericVerifierClosedLeafParsedRuleGraph_with_publicBounds
#print axioms
  CompactNumericVerifierClosedLeafStateGraph.closedExtraEnvironment_size_le_of_canonical
#print axioms
  exists_compactNumericVerifierClosedLeafStateGraph_with_publicBounds_of_transport

end FoundationCompactNumericListedDirectVerifierClosedLeafStatePublicBounds
