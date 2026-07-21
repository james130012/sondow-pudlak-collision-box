import integration.FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula
import integration.FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
import integration.FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
import integration.FoundationCompactNumericListedDirectTraceBounds

/-!
# Public bounds for sequent-only proof-root success

Tags `2`, `7`, and `8` contain a count-prefixed sequent and no additional
formula or term.  This module reconstructs their exact successful root-parser
endpoint in the canonical shared table and bounds every exposed coordinate by
an explicit function of the public input weight.

Unlike the older `exists_bounded` endpoint, the bound below is not the sum of
coordinates chosen after the fact.  Every suffix, nested parser trace, table
parameter, boundary code, and endpoint witness is first bounded from the
original input.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactProofTokenMachine
open FoundationCompactParserDirectTrace
open FoundationCompactNumericSyntaxValueParser
open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedRootFieldsDecomposition
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectNatListSliceEquality
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListConsRows
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectBinaryNatStreamStepWitnessBound
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessBound
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepWitnessTable
open FoundationCompactNumericListedDirectParserSyntaxTraceBounds
open FoundationCompactNumericListedDirectSequentFormulaTracePublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointInstallation
open FoundationCompactNumericListedDirectProofRootSequentOnlyEndpoint
open FoundationCompactNumericListedDirectProofRootSequentOnlyBoundedFormula
open FoundationCompactNumericListedDirectProofRootCanonicalSharedRowsPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaCanonicalData
open FoundationCompactNumericListedDirectSequentFormulaCanonicalDataPublicBounds
open FoundationCompactNumericListedDirectSequentFormulaEndpointPublicBounds
open FoundationCompactNumericListedDirectTraceBounds
open FoundationCompactNumericListedStateBounds

private theorem nat_le_two_pow_of_size_le
    {value sizeBound : Nat} (hsize : Nat.size value <= sizeBound) :
    value <= 2 ^ sizeBound :=
  (Nat.size_le.mp hsize).le

theorem
    compactSequentFormulaCanonicalSuffixesWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactSequentFormulaCanonicalSuffixesWeightBound left <=
      compactSequentFormulaCanonicalSuffixesWeightBound right := by
  have hsize : Nat.size (left + 1) <= Nat.size (right + 1) :=
    Nat.size_le_size (Nat.add_le_add_right h 1)
  have hproduct : (left + 1) * left <= (right + 1) * right :=
    Nat.mul_le_mul (Nat.add_le_add_right h 1) h
  unfold compactSequentFormulaCanonicalSuffixesWeightBound
  omega

theorem
    compactSequentFormulaCanonicalParserTracesWeightBound_mono
    {left right : Nat} (h : left <= right) :
    compactSequentFormulaCanonicalParserTracesWeightBound left <=
      compactSequentFormulaCanonicalParserTracesWeightBound right := by
  have hsize : Nat.size left <= Nat.size right := Nat.size_le_size h
  have htrace :=
    compactNumericRootSyntaxParserTraceWeightBound_mono h
  have hproduct :
      left * compactNumericRootSyntaxParserTraceWeightBound left <=
        right * compactNumericRootSyntaxParserTraceWeightBound right :=
    Nat.mul_le_mul h htrace
  unfold compactSequentFormulaCanonicalParserTracesWeightBound
  omega

theorem compactBinaryNatStreamStepWitnessPublicWidth_mono
    {left right : Nat} (h : left <= right) :
    compactBinaryNatStreamStepWitnessPublicWidth left <=
      compactBinaryNatStreamStepWitnessPublicWidth right := by
  have hproduct : (left + 1) * left <= (right + 1) * right :=
    Nat.mul_le_mul (Nat.add_le_add_right h 1) h
  unfold compactBinaryNatStreamStepWitnessPublicWidth
  omega

theorem compactParserSyntaxAdjacentStepPublicWidth_mono
    {leftWidth rightWidth leftCount rightCount : Nat}
    (hwidth : leftWidth <= rightWidth)
    (hcount : leftCount <= rightCount) :
    compactParserSyntaxAdjacentStepPublicWidth leftWidth leftCount <=
      compactParserSyntaxAdjacentStepPublicWidth rightWidth rightCount := by
  have hstream :=
    compactBinaryNatStreamStepWitnessPublicWidth_mono hcount
  unfold compactParserSyntaxAdjacentStepPublicWidth
    compactFormulaTransformAdjacentStepPublicWidth
  omega

theorem compactParserSyntaxCanonicalTableWidthBound_mono
    {leftWidth rightWidth leftCount rightCount leftFuel rightFuel : Nat}
    (hwidth : leftWidth <= rightWidth)
    (hcount : leftCount <= rightCount)
    (hfuel : leftFuel <= rightFuel) :
    compactParserSyntaxCanonicalTableWidthBound
        leftWidth leftCount leftFuel <=
      compactParserSyntaxCanonicalTableWidthBound
        rightWidth rightCount rightFuel := by
  have hstep :=
    compactParserSyntaxAdjacentStepPublicWidth_mono hwidth hcount
  have hfuelColumns :
      leftFuel * compactParserSyntaxAdjacentStepWitnessColumnCount <=
        rightFuel * compactParserSyntaxAdjacentStepWitnessColumnCount :=
    Nat.mul_le_mul_right
      compactParserSyntaxAdjacentStepWitnessColumnCount hfuel
  have hrows :
      leftFuel * compactParserSyntaxAdjacentStepWitnessColumnCount *
          compactParserSyntaxAdjacentStepPublicWidth
            leftWidth leftCount <=
        rightFuel * compactParserSyntaxAdjacentStepWitnessColumnCount *
          compactParserSyntaxAdjacentStepPublicWidth
            rightWidth rightCount :=
    Nat.mul_le_mul hfuelColumns hstep
  have harea :
      (leftCount + 1) * leftCount <=
        (rightCount + 1) * rightCount :=
    Nat.mul_le_mul (Nat.add_le_add_right hcount 1) hcount
  have htail :
      23 * compactParserSyntaxAdjacentStepPublicWidth
          leftWidth leftCount <=
        23 * compactParserSyntaxAdjacentStepPublicWidth
          rightWidth rightCount :=
    Nat.mul_le_mul_left 23 hstep
  unfold compactParserSyntaxCanonicalTableWidthBound
  omega

theorem compactSequentFormulaPublicParserFuelBound_mono
    {left right : Nat} (h : left <= right) :
    compactSequentFormulaPublicParserFuelBound left <=
      compactSequentFormulaPublicParserFuelBound right := by
  have hplus : left + 1 <= right + 1 := Nat.add_le_add_right h 1
  have hsquare :
      (left + 1) * (left + 1) <=
        (right + 1) * (right + 1) :=
    Nat.mul_le_mul hplus hplus
  have hscaled :
      16 * (left + 1) * (left + 1) <=
        16 * (right + 1) * (right + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 16 hplus) hplus
  unfold compactSequentFormulaPublicParserFuelBound
  omega

theorem compactSequentFormulaStepPublicCoordinateSizeBound_mono
    {leftWidth rightWidth leftCount rightCount : Nat}
    (hwidth : leftWidth <= rightWidth)
    (hcount : leftCount <= rightCount) :
    compactSequentFormulaStepPublicCoordinateSizeBound
        leftWidth leftCount <=
      compactSequentFormulaStepPublicCoordinateSizeBound
        rightWidth rightCount := by
  have hfuel :=
    compactSequentFormulaPublicParserFuelBound_mono hcount
  have harea :
      (leftCount + 1) * leftCount <=
        (rightCount + 1) * rightCount :=
    Nat.mul_le_mul (Nat.add_le_add_right hcount 1) hcount
  have hfuelArea :
      (compactSequentFormulaPublicParserFuelBound leftCount + 2) *
          leftCount <=
        (compactSequentFormulaPublicParserFuelBound rightCount + 2) *
          rightCount :=
    Nat.mul_le_mul (Nat.add_le_add_right hfuel 2) hcount
  have hparser :=
    compactParserSyntaxCanonicalTableWidthBound_mono
      hwidth hcount hfuel
  unfold compactSequentFormulaStepPublicCoordinateSizeBound
  omega

theorem compactSequentFormulaTracePublicTableWidthBound_mono
    {leftWidth rightWidth leftCount rightCount : Nat}
    (hwidth : leftWidth <= rightWidth)
    (hcount : leftCount <= rightCount) :
    compactSequentFormulaTracePublicTableWidthBound
        leftWidth leftCount <=
      compactSequentFormulaTracePublicTableWidthBound
        rightWidth rightCount := by
  have hcolumns : leftCount * 18 <= rightCount * 18 :=
    Nat.mul_le_mul_right 18 hcount
  have hstep :=
    compactSequentFormulaStepPublicCoordinateSizeBound_mono
      hwidth hcount
  unfold compactSequentFormulaTracePublicTableWidthBound
  exact Nat.mul_le_mul hcolumns hstep

theorem
    compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
    {leftWidth rightWidth leftCount rightCount : Nat}
    (hwidth : leftWidth <= rightWidth)
    (hcount : leftCount <= rightCount) :
    compactSequentFormulaEndpointPublicCoordinateSizeBound
        leftWidth leftCount <=
      compactSequentFormulaEndpointPublicCoordinateSizeBound
        rightWidth rightCount := by
  have harea :
      (leftCount + 2) * leftCount <=
        (rightCount + 2) * rightCount :=
    Nat.mul_le_mul (Nat.add_le_add_right hcount 2) hcount
  have htrace :=
    compactSequentFormulaTracePublicTableWidthBound_mono
      hwidth hcount
  unfold compactSequentFormulaEndpointPublicCoordinateSizeBound
  omega

def compactProofRootSequentOnlySharedDataWeightBound
    (inputWeight : Nat) : Nat :=
  inputWeight +
    compactNumericVerifierTaskWeightBound inputWeight +
    inputWeight +
    compactSequentFormulaCanonicalSuffixesWeightBound inputWeight +
    compactSequentFormulaCanonicalParserTracesWeightBound inputWeight +
    2

def compactProofRootSequentOnlySharedCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootCanonicalSharedCoordinateSizeBound
    (compactProofRootSequentOnlySharedDataWeightBound inputWeight)

def compactProofRootSequentOnlyEndpointCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootSequentOnlySharedCoordinateSizeBound inputWeight
  compactSequentFormulaEndpointPublicCoordinateSizeBound
    sharedBound sharedBound

def compactProofRootSequentOnlyLocalCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  let sharedBound :=
    compactProofRootSequentOnlySharedCoordinateSizeBound inputWeight
  sharedBound +
    (sharedBound + 1) * sharedBound +
    (inputWeight + 1) * sharedBound +
    compactProofRootSequentOnlyEndpointCoordinateSizeBound inputWeight +
    inputWeight + 8

def compactProofRootSequentOnlyPublicCoordinateSizeBound
    (inputWeight : Nat) : Nat :=
  compactProofRootSequentOnlyLocalCoordinateSizeBound inputWeight + 1

theorem compactProofRootSequentOnlyPublicCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootSequentOnlyPublicCoordinateSizeBound left <=
      compactProofRootSequentOnlyPublicCoordinateSizeBound right := by
  have htask := compactNumericVerifierTaskWeightBound_mono h
  have hsuffixes :=
    compactSequentFormulaCanonicalSuffixesWeightBound_mono h
  have htraces :=
    compactSequentFormulaCanonicalParserTracesWeightBound_mono h
  have hdata :
      compactProofRootSequentOnlySharedDataWeightBound left <=
        compactProofRootSequentOnlySharedDataWeightBound right := by
    unfold compactProofRootSequentOnlySharedDataWeightBound
    omega
  have htwice :
      2 * compactProofRootSequentOnlySharedDataWeightBound left <=
        2 * compactProofRootSequentOnlySharedDataWeightBound right :=
    Nat.mul_le_mul_left 2 hdata
  have hdataProduct :
      compactProofRootSequentOnlySharedDataWeightBound left *
          (2 * compactProofRootSequentOnlySharedDataWeightBound left) <=
        compactProofRootSequentOnlySharedDataWeightBound right *
          (2 * compactProofRootSequentOnlySharedDataWeightBound right) :=
    Nat.mul_le_mul hdata htwice
  have hshared :
      compactProofRootSequentOnlySharedCoordinateSizeBound left <=
        compactProofRootSequentOnlySharedCoordinateSizeBound right := by
    unfold compactProofRootSequentOnlySharedCoordinateSizeBound
      compactProofRootCanonicalSharedCoordinateSizeBound
    omega
  have hendpoint :
      compactProofRootSequentOnlyEndpointCoordinateSizeBound left <=
        compactProofRootSequentOnlyEndpointCoordinateSizeBound right := by
    unfold compactProofRootSequentOnlyEndpointCoordinateSizeBound
    exact compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
      hshared hshared
  have hsharedArea :
      (compactProofRootSequentOnlySharedCoordinateSizeBound left + 1) *
          compactProofRootSequentOnlySharedCoordinateSizeBound left <=
        (compactProofRootSequentOnlySharedCoordinateSizeBound right + 1) *
          compactProofRootSequentOnlySharedCoordinateSizeBound right :=
    Nat.mul_le_mul (Nat.add_le_add_right hshared 1) hshared
  have hmixed :
      (left + 1) * compactProofRootSequentOnlySharedCoordinateSizeBound left <=
        (right + 1) *
          compactProofRootSequentOnlySharedCoordinateSizeBound right :=
    Nat.mul_le_mul (Nat.add_le_add_right h 1) hshared
  simp only [compactProofRootSequentOnlyPublicCoordinateSizeBound,
    compactProofRootSequentOnlyLocalCoordinateSizeBound]
  omega

structure CompactProofRootSequentOnlyPublicCoordinateBounds
    (tokenTable width tokenCount inputStart inputFinish
      rootStart rootFinish bodyStart bodyFinish endpointBound bound : Nat) :
    Prop where
  tokenTable : Nat.size tokenTable <= bound
  width_value : width <= bound
  width : Nat.size width <= bound
  tokenCount_value : tokenCount <= bound
  tokenCount : Nat.size tokenCount <= bound
  inputStart : Nat.size inputStart <= bound
  inputFinish : Nat.size inputFinish <= bound
  rootStart : Nat.size rootStart <= bound
  rootFinish : Nat.size rootFinish <= bound
  bodyStart : Nat.size bodyStart <= bound
  bodyFinish : Nat.size bodyFinish <= bound
  endpointBound : Nat.size endpointBound <= bound

theorem compactProofRootCanonicalSharedCoordinateSizeBound_mono
    {left right : Nat} (h : left <= right) :
    compactProofRootCanonicalSharedCoordinateSizeBound left <=
      compactProofRootCanonicalSharedCoordinateSizeBound right := by
  have htwice : 2 * left <= 2 * right :=
    Nat.mul_le_mul_left 2 h
  have hproduct : left * (2 * left) <= right * (2 * right) :=
    Nat.mul_le_mul h htwice
  unfold compactProofRootCanonicalSharedCoordinateSizeBound
  omega

/-- A successful sequent-only parse constructs the exact bounded endpoint,
with every table parameter and every local witness bounded from the public
input weight. -/
theorem
    exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_results_with_publicBounds
    (tag : Nat) (body : List Nat) (values : List (List Nat))
    (suffix : List Nat)
    (htag : tag = 2 ∨ tag = 7 ∨ tag = 8)
    (hsequent : compactSequentTokenValueParser body =
      some (values, suffix)) :
    let input := tag :: body
    let root : CompactNumericProofRoot :=
      (tag, (values, ([], ([], ([], suffix)))))
    let inputWeight := compactAdditiveValueWeight input
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentOnlyEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootSequentOnlyPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootSequentOnlyPublicCoordinateSizeBound
              inputWeight) := by
  let input := tag :: body
  let root : CompactNumericProofRoot :=
    (tag, (values, ([], ([], ([], suffix)))))
  let inputWeight := compactAdditiveValueWeight input
  have hrootParser :
      compactListedProofNodeFieldsParser input = some root := by
    rcases htag with htag2 | htag78
    · subst tag
      simp [input, root, compactListedProofNodeFieldsParser,
        compactTagNumericNodeFields, compactNodeSequentOnlyFields,
        hsequent]
    · rcases htag78 with htag7 | htag8
      · subst tag
        simp [input, root, compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, compactNodeSequentOnlyFields,
          hsequent]
      · subst tag
        simp [input, root, compactListedProofNodeFieldsParser,
          compactTagNumericNodeFields, compactNodeSequentOnlyFields,
          hsequent]
  have hrootTag : root.1 <= 10 := by
    dsimp only [root]
    rcases htag with rfl | rfl | rfl <;> omega
  have hrootWeight :
      compactAdditiveValueWeight root <=
        compactNumericVerifierTaskWeightBound inputWeight := by
    exact (show CompactNumericVerifierTaskWithin inputWeight root from
      ⟨hrootTag,
        compactListedProofNodeFieldsParser_componentsWithin
          hrootParser⟩).weight_le
  have hbodyWeight :
      compactAdditiveValueWeight body <= inputWeight := by
    exact compactAdditiveValueWeight_suffix_le
      (show body <:+ input from ⟨[tag], by simp [input]⟩)
  rcases compactSequentTokenValueParser_sound hsequent with
    ⟨Gamma, hbody, hvalues⟩
  subst body
  subst values
  rcases
      exists_compactSequentFormulaCanonicalDirectData_with_publicBounds
        Gamma suffix with
    ⟨suffixes, parserTraces, hsuffixCount, hparserCount,
      hfirst, hfinal, hsteps, hsuffixWeight, hparserWeight⟩
  have hsuffixWeightPublic :
      compactAdditiveValueWeight suffixes <=
        compactSequentFormulaCanonicalSuffixesWeightBound
          inputWeight :=
    hsuffixWeight.trans
      (compactSequentFormulaCanonicalSuffixesWeightBound_mono
        hbodyWeight)
  have hparserWeightPublic :
      compactAdditiveValueWeight parserTraces <=
        compactSequentFormulaCanonicalParserTracesWeightBound
          inputWeight :=
    hparserWeight.trans
      (compactSequentFormulaCanonicalParserTracesWeightBound_mono
        hbodyWeight)
  rcases
      exists_compactProofRootCanonicalSharedRows_with_publicBounds
        input root (compactSequentListTokens Gamma ++ suffix)
        suffixes parserTraces [] [] with
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish,
      _sequentSuffixBoundary, _intermediateSuffixBoundary,
      hshared, hsharedPublic⟩
  have hsharedDataWeight :
      compactProofRootCanonicalSharedDataWeight
          input root (compactSequentListTokens Gamma ++ suffix)
          suffixes parserTraces [] [] <=
        compactProofRootSequentOnlySharedDataWeightBound
          inputWeight := by
    have hemptySuffixes :
        compactAdditiveValueWeight ([] : List (List Nat)) = 1 := by
      simp [compactAdditiveValueWeight_list]
    have hemptyParserTraces :
        compactAdditiveValueWeight
            ([] : List (List CompactUnifiedParserState)) = 1 := by
      simp [compactAdditiveValueWeight_list]
    unfold compactProofRootCanonicalSharedDataWeight
      compactProofRootSequentOnlySharedDataWeightBound
    rw [hemptySuffixes, hemptyParserTraces]
    omega
  have hsharedCoordinateBound :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ suffix)
              suffixes parserTraces [] []) <=
        compactProofRootSequentOnlySharedCoordinateSizeBound
          inputWeight := by
    unfold compactProofRootSequentOnlySharedCoordinateSizeBound
    exact
      compactProofRootCanonicalSharedCoordinateSizeBound_mono
        hsharedDataWeight
  let sharedBound :=
    compactProofRootSequentOnlySharedCoordinateSizeBound inputWeight
  have hwidthValue : width <= sharedBound :=
    hsharedPublic.width_value.trans (by
      simpa only [sharedBound] using hsharedCoordinateBound)
  have htokenCountValue : tokenCount <= sharedBound :=
    hsharedPublic.tokenCount_value.trans (by
      simpa only [sharedBound] using hsharedCoordinateBound)
  rcases
      CompactNumericVerifierTaskDirectLayout.toCoreGraph
        hshared.rootLayout with
    ⟨rootCoordinates, rootSize, hrootStart, hrootFinish,
      hrootTagCoordinate, hrootCore⟩
  rcases
      CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
        hrootCore with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaCount, _hfirstLayout, hfirstCount,
      _hsecondLayout, hsecondCount, _hwitnessLayout, hwitnessCount,
      hsuffixLayout, _hsuffixCount⟩
  have hrealizedEq : realizedRoot = root :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hrootCore
        (by simpa [hrootStart, hrootFinish] using hshared.rootLayout)
        hrealizedRoot
  subst realizedRoot
  have hgammaStructure := hrootCore.2.1
  rw [← hgammaCount] at hgammaStructure
  have hgammaSize :
      Nat.size rootCoordinates.gammaBoundary <=
        (root.2.1.length + 1) * tokenCount := by
    rw [hgammaCount]
    exact hrootCore.bounds.gammaBoundary_size_le
  have hparserRows :
      ∀ index < (Gamma.map compactArithmeticFormulaTokens).length,
        ∃ parserStateBoundary,
          FoundationCompactNumericListedDirectParserStateListLayout.CompactUnifiedParserStateListRowLayouts
              tokenTable width tokenCount parserStateBoundary
                (parserTraces.getI index) ∧
            Nat.size parserStateBoundary <=
              ((parserTraces.getI index).length + 1) * tokenCount := by
    intro index hindex
    apply hshared.sequentParserRows index
    rw [hparserCount]
    simpa using hindex
  have hsteps' :
      ∀ index < (Gamma.map compactArithmeticFormulaTokens).length,
        CompactFormulaTokenParserDirectTraceValid
            0 (suffixes.getI index) (suffixes.getI (index + 1))
              (parserTraces.getI index) ∧
          suffixes.getI index =
            (Gamma.map compactArithmeticFormulaTokens).getI index ++
              suffixes.getI (index + 1) := by
    intro index hindex
    apply hsteps index
    simpa using hindex
  have hsuffixCount' :
      suffixes.length =
        (Gamma.map compactArithmeticFormulaTokens).length + 1 := by
    simpa using hsuffixCount
  have hparserCount' :
      parserTraces.length =
        (Gamma.map compactArithmeticFormulaTokens).length := by
    simpa using hparserCount
  have hbodyFirst :
      compactSequentListTokens Gamma ++ suffix =
        (Gamma.map compactArithmeticFormulaTokens).length ::
          suffixes.getI 0 := by
    rw [hfirst]
    simp [compactSequentListTokens]
  have hfinal' : suffixes.getI root.2.1.length = suffix := by
    simpa [root] using hfinal
  rcases
      exists_compactSequentFormulaEndpointGraph_of_rows_with_publicBounds
        hshared.bodyLayout hshared.sequentSuffixRows
        hshared.sequentSuffixBoundary_size_le
        hgammaStructure hgammaRows hgammaSize
        hparserRows hsuffixCount' hparserCount' hsteps'
        hbodyFirst hfinal' with
    ⟨finalStart, finalFinish, sequentCoordinates,
      hsequentGraph, hsequentPublic⟩
  rcases
      CompactAdditiveNatListDirectLayout.exists_witnessRows
        hshared.inputLayout with
    ⟨inputBoundary, inputBoundarySize, hinputWitness⟩
  rcases hinputWitness.realize with
    ⟨witnessInput, hwitnessInputCount, hwitnessInputLayout,
      hwitnessInputRows⟩
  have hwitnessInputEq : witnessInput = input :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.inputLayout hwitnessInputLayout).1
  subst witnessInput
  rcases hsequentGraph.1.realize with
    ⟨witnessBody, hwitnessBodyCount, hwitnessBodyLayout,
      hwitnessBodyRows⟩
  have hwitnessBodyEq : witnessBody =
      compactSequentListTokens Gamma ++ suffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.bodyLayout hwitnessBodyLayout).1
  subst witnessBody
  have hcons :
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount sequentCoordinates.inputBoundary
          sequentCoordinates.inputCount inputBoundary input.length tag := by
    have hraw :=
      CompactAdditiveStructuredListElementRowLayouts.natConsRows
        hwitnessBodyRows hwitnessInputRows
          (show input =
            tag :: (compactSequentListTokens Gamma ++ suffix) by rfl)
    simpa only [hwitnessBodyCount, hwitnessInputCount] using hraw
  rcases hsequentGraph.sound with
    ⟨endpointBody, endpointValues, endpointSuffix,
      hendpointBodyLayout, _hendpointValuesLayout,
      hendpointSuffixLayout, hendpointParser⟩
  have hendpointBodyEq : endpointBody =
      compactSequentListTokens Gamma ++ suffix :=
    (FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy.CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
      hshared.bodyLayout hendpointBodyLayout).1
  subst endpointBody
  have hendpointResult :
      (endpointValues, endpointSuffix) =
        (Gamma.map compactArithmeticFormulaTokens, suffix) :=
    Option.some.inj
      (hendpointParser.symm.trans (by simpa using hsequent))
  have hendpointSuffix : endpointSuffix = suffix :=
    congrArg Prod.snd hendpointResult
  have hfinalSlices :
      CompactFixedWidthTokenSlicesEq
        tokenTable width tokenCount finalStart finalFinish
          rootCoordinates.witnessFinish rootCoordinates.finish := by
    apply CompactAdditiveNatListDirectLayout.slicesEq_of_eq
      hendpointSuffixLayout hsuffixLayout
    simpa [root, hendpointSuffix]
  have hfirstZero : rootCoordinates.firstCount = 0 := by
    simpa [root] using hfirstCount.symm
  have hsecondZero : rootCoordinates.secondCount = 0 := by
    simpa [root] using hsecondCount.symm
  have hwitnessZero : rootCoordinates.witnessCount = 0 := by
    simpa [root] using hwitnessCount.symm
  have hcoordinateTag : rootCoordinates.tag = tag := by
    simpa [root] using hrootTagCoordinate
  have hcoordinateTagCases :
      rootCoordinates.tag = 2 ∨
        rootCoordinates.tag = 7 ∨ rootCoordinates.tag = 8 := by
    rw [hcoordinateTag]
    exact htag
  have hconsCoordinateTag :
      CompactAdditiveNatListConsRows
        tokenTable width tokenCount sequentCoordinates.inputBoundary
          sequentCoordinates.inputCount inputBoundary input.length
          rootCoordinates.tag := by
    simpa only [hcoordinateTag] using hcons
  let coordinates : CompactProofRootSequentOnlyEndpointCoordinates :=
    { inputBoundary := inputBoundary
      inputCount := input.length
      inputBoundarySize := inputBoundarySize
      root := rootCoordinates
      rootSize := rootSize
      finalStart := finalStart
      finalFinish := finalFinish
      sequent := sequentCoordinates }
  have hgraph :
      CompactProofRootSequentOnlyEndpointGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish coordinates := by
    unfold CompactProofRootSequentOnlyEndpointGraph
    dsimp only [coordinates]
    exact ⟨hinputWitness, hrootStart, hrootFinish, hrootCore,
      hcoordinateTagCases, hfirstZero, hsecondZero, hwitnessZero,
      hconsCoordinateTag, hsequentGraph, hfinalSlices⟩
  let endpointCoordinateBound :=
    compactProofRootSequentOnlyEndpointCoordinateSizeBound inputWeight
  have hendpointCoordinateBound :
      compactSequentFormulaEndpointPublicCoordinateSizeBound
          width tokenCount <= endpointCoordinateBound := by
    dsimp only [endpointCoordinateBound,
      compactProofRootSequentOnlyEndpointCoordinateSizeBound]
    exact
      compactSequentFormulaEndpointPublicCoordinateSizeBound_mono
        hwidthValue htokenCountValue
  let localBound :=
    compactProofRootSequentOnlyLocalCoordinateSizeBound inputWeight
  have hsharedToLocal : sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootSequentOnlyLocalCoordinateSizeBound]
    omega
  have hrootAreaToLocal :
      (sharedBound + 1) * sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootSequentOnlyLocalCoordinateSizeBound]
    omega
  have hinputAreaToLocal :
      (inputWeight + 1) * sharedBound <= localBound := by
    dsimp only [sharedBound, localBound,
      compactProofRootSequentOnlyLocalCoordinateSizeBound]
    omega
  have hendpointToLocal : endpointCoordinateBound <= localBound := by
    dsimp only [endpointCoordinateBound, localBound,
      compactProofRootSequentOnlyLocalCoordinateSizeBound]
    omega
  have hinputWeightToLocal : inputWeight <= localBound := by
    dsimp only [localBound,
      compactProofRootSequentOnlyLocalCoordinateSizeBound]
    omega
  have hrootBounds := hrootCore.bounds
  have hrootSmall
      {value : Nat} (hvalue : value <= tokenCount) :
      Nat.size value <= localBound :=
    (natSize_le_of_le hvalue).trans
      (htokenCountValue.trans hsharedToLocal)
  have hrootTagSize :
      Nat.size rootCoordinates.tag <= localBound :=
    hrootBounds.tag_size_le.trans
      (hwidthValue.trans hsharedToLocal)
  have hrootGammaArea :
      (rootCoordinates.gammaCount + 1) * tokenCount <=
        (sharedBound + 1) * sharedBound :=
    Nat.mul_le_mul
      (Nat.add_le_add_right
        (hrootBounds.gammaCount_le.trans htokenCountValue) 1)
      htokenCountValue
  have hrootGammaBoundarySize :
      Nat.size rootCoordinates.gammaBoundary <= localBound :=
    hrootBounds.gammaBoundary_size_le.trans
      (hrootGammaArea.trans hrootAreaToLocal)
  have hrootGammaBoundarySizeWitness :
      Nat.size rootSize.gammaBoundarySize <= localBound :=
    (natSize_le_of_le hrootBounds.gammaBoundarySize_le).trans
      (hrootGammaArea.trans hrootAreaToLocal)
  have hinputLength : input.length <= inputWeight :=
    compactAdditiveValueWeight_natList_length_le input
  have hinputArea :
      (input.length + 1) * tokenCount <=
        (inputWeight + 1) * sharedBound :=
    Nat.mul_le_mul (Nat.add_le_add_right hinputLength 1)
      htokenCountValue
  have hinputBoundarySizeRaw :
      Nat.size inputBoundary <=
        (input.length + 1) * tokenCount := by
    rw [← hinputWitness.2.2.1]
    exact hinputWitness.2.2.2
  have hinputBoundarySize :
      Nat.size inputBoundary <= localBound :=
    hinputBoundarySizeRaw.trans
      (hinputArea.trans hinputAreaToLocal)
  have hinputCountSize :
      Nat.size input.length <= localBound :=
    (natSize_le_of_le hinputLength).trans hinputWeightToLocal
  have hinputBoundarySizeWitness :
      Nat.size inputBoundarySize <= localBound :=
    (natSize_le_of_le hinputWitness.2.2.2).trans
      (hinputArea.trans hinputAreaToLocal)
  have hfinalStartSize : Nat.size finalStart <= localBound :=
    hsequentPublic.finalStart_size_le.trans
      (hendpointCoordinateBound.trans hendpointToLocal)
  have hfinalFinishSize : Nat.size finalFinish <= localBound :=
    hsequentPublic.finalFinish_size_le.trans
      (hendpointCoordinateBound.trans hendpointToLocal)
  have hsequentSize
      {value : Nat}
      (hvalue :
        value ∈
          compactSequentFormulaEndpointCoordinateValues
            sequentCoordinates) :
      Nat.size value <= localBound :=
    (hsequentPublic.value_size_le value hvalue).trans
      (hendpointCoordinateBound.trans hendpointToLocal)
  let endpointBound := 2 ^ localBound
  have hbounded :
      CompactProofRootSequentOnlyEndpointBoundedGraph
        tokenTable width tokenCount inputStart inputFinish
          rootStart rootFinish bodyStart bodyFinish endpointBound := by
    unfold CompactProofRootSequentOnlyEndpointBoundedGraph
    refine
      ⟨inputBoundary, nat_le_two_pow_of_size_le hinputBoundarySize,
        input.length, nat_le_two_pow_of_size_le hinputCountSize,
        inputBoundarySize,
          nat_le_two_pow_of_size_le hinputBoundarySizeWitness,
        rootCoordinates.start,
          nat_le_two_pow_of_size_le (hrootSmall hrootBounds.start_le),
        rootCoordinates.finish,
          nat_le_two_pow_of_size_le (hrootSmall hrootBounds.finish_le),
        rootCoordinates.tag,
          nat_le_two_pow_of_size_le hrootTagSize,
        rootCoordinates.gammaFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.gammaFinish_le),
        rootCoordinates.gammaCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.gammaCount_le),
        rootCoordinates.gammaBoundary,
          nat_le_two_pow_of_size_le hrootGammaBoundarySize,
        rootCoordinates.firstFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.firstFinish_le),
        rootCoordinates.firstCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.firstCount_le),
        rootCoordinates.secondFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.secondFinish_le),
        rootCoordinates.secondCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.secondCount_le),
        rootCoordinates.witnessFinish,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.witnessFinish_le),
        rootCoordinates.witnessCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.witnessCount_le),
        rootCoordinates.suffixCount,
          nat_le_two_pow_of_size_le
            (hrootSmall hrootBounds.suffixCount_le),
        rootSize.gammaBoundarySize,
          nat_le_two_pow_of_size_le hrootGammaBoundarySizeWitness,
        finalStart, nat_le_two_pow_of_size_le hfinalStartSize,
        finalFinish, nat_le_two_pow_of_size_le hfinalFinishSize,
        sequentCoordinates.inputBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.inputCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.inputBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstStart,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstFinish,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.firstBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.suffixBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.suffixCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.valueBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.valueCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.valueBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.finalBoundary,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.finalCount,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.finalBoundarySize,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.traceTableWidth,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        sequentCoordinates.traceValueBound,
          nat_le_two_pow_of_size_le
            (hsequentSize (by
              simp [compactSequentFormulaEndpointCoordinateValues])),
        ?_⟩
    simpa only [coordinates,
      compactProofRootSequentOnlyEndpointCoordinatesOfValues] using hgraph
  let publicBound :=
    compactProofRootSequentOnlyPublicCoordinateSizeBound inputWeight
  have hlocalToPublic : localBound <= publicBound := by
    dsimp only [localBound, publicBound,
      compactProofRootSequentOnlyPublicCoordinateSizeBound]
    omega
  have hsharedToPublic : sharedBound <= publicBound :=
    hsharedToLocal.trans hlocalToPublic
  have hactualSharedToShared :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ suffix)
              suffixes parserTraces [] []) <= sharedBound := by
    simpa only [sharedBound] using hsharedCoordinateBound
  have hactualSharedToPublic :
      compactProofRootCanonicalSharedCoordinateSizeBound
          (compactProofRootCanonicalSharedDataWeight
            input root (compactSequentListTokens Gamma ++ suffix)
              suffixes parserTraces [] []) <= publicBound :=
    hactualSharedToShared.trans hsharedToPublic
  have htablePublic : Nat.size tokenTable <= publicBound :=
    hsharedPublic.tokenTable.trans hactualSharedToPublic
  have hwidthPublic : Nat.size width <= publicBound :=
    hsharedPublic.width_size.trans hactualSharedToPublic
  have htokenCountPublic : Nat.size tokenCount <= publicBound :=
    hsharedPublic.tokenCount_size.trans hactualSharedToPublic
  have hinputStartPublic : Nat.size inputStart <= publicBound :=
    hsharedPublic.inputStart.trans hactualSharedToPublic
  have hinputFinishPublic : Nat.size inputFinish <= publicBound :=
    hsharedPublic.inputFinish.trans hactualSharedToPublic
  have hrootStartPublic : Nat.size rootStart <= publicBound :=
    hsharedPublic.rootStart.trans hactualSharedToPublic
  have hrootFinishPublic : Nat.size rootFinish <= publicBound :=
    hsharedPublic.rootFinish.trans hactualSharedToPublic
  have hbodyStartPublic : Nat.size bodyStart <= publicBound :=
    hsharedPublic.bodyStart.trans hactualSharedToPublic
  have hbodyFinishPublic : Nat.size bodyFinish <= publicBound :=
    hsharedPublic.bodyFinish.trans hactualSharedToPublic
  have hendpointBoundPublic : Nat.size endpointBound <= publicBound := by
    dsimp only [endpointBound, publicBound,
      compactProofRootSequentOnlyPublicCoordinateSizeBound]
    rw [Nat.size_pow]
  refine
    ⟨tokenTable, width, tokenCount, inputStart, inputFinish,
      rootStart, rootFinish, bodyStart, bodyFinish, endpointBound,
      ?_, hbounded, ?_⟩
  · simpa only [input] using hshared.inputLayout
  · exact
      { tokenTable := htablePublic
        width := hwidthPublic
        width_value := hwidthValue.trans hsharedToPublic
        tokenCount := htokenCountPublic
        tokenCount_value := htokenCountValue.trans hsharedToPublic
        inputStart := hinputStartPublic
        inputFinish := hinputFinishPublic
        rootStart := hrootStartPublic
        rootFinish := hrootFinishPublic
        bodyStart := hbodyStartPublic
        bodyFinish := hbodyFinishPublic
        endpointBound := hendpointBoundPublic }

/-- Public root-parser success for tags `2`, `7`, or `8` feeds the concrete
constructor above; no endpoint coordinate or bound is supplied as input. -/
theorem
    exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_publicBounds
    {input : List Nat} {root : CompactNumericProofRoot}
    (hparser : compactListedProofNodeFieldsParser input = some root)
    (htag : root.1 = 2 ∨ root.1 = 7 ∨ root.1 = 8) :
    ∃ tokenTable width tokenCount inputStart inputFinish,
    ∃ rootStart rootFinish bodyStart bodyFinish endpointBound,
      CompactAdditiveNatListDirectLayout
          tokenTable width tokenCount inputStart inputFinish input ∧
        CompactProofRootSequentOnlyEndpointBoundedGraph
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound ∧
        CompactProofRootSequentOnlyPublicCoordinateBounds
          tokenTable width tokenCount inputStart inputFinish
            rootStart rootFinish bodyStart bodyFinish endpointBound
            (compactProofRootSequentOnlyPublicCoordinateSizeBound
              (compactAdditiveValueWeight input)) := by
  rw [compactListedProofNodeFieldsParser_eq_some_iff_branchValid] at hparser
  cases input with
  | nil =>
      simp [CompactNumericProofRootBranchValid] at hparser
  | cons inputTag body =>
      rcases htag with htag2 | htag78
      · have hinputTag : inputTag = 2 := by
          by_contra hne
          simp [CompactNumericProofRootBranchValid, hne, htag2] at hparser
        subst inputTag
        have hfields : compactNodeSequentOnlyFields body = some root.2 := by
          simpa [CompactNumericProofRootBranchValid, htag2] using hparser
        cases hsequent : compactSequentTokenValueParser body with
        | none =>
            simp [compactNodeSequentOnlyFields, hsequent] at hfields
        | some parsed =>
            rcases parsed with ⟨values, suffix⟩
            have hroot :
                root =
                  (2, (values, ([], ([], ([], suffix))))) := by
              simp [compactNodeSequentOnlyFields, hsequent] at hfields
              exact Prod.ext htag2 (by simpa using hfields.symm)
            subst root
            simpa using
              exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_results_with_publicBounds
                2 body values suffix (Or.inl rfl) hsequent
      · rcases htag78 with htag7 | htag8
        · have hinputTag : inputTag = 7 := by
            by_contra hne
            simp [CompactNumericProofRootBranchValid, hne, htag7] at hparser
          subst inputTag
          have hfields :
              compactNodeSequentOnlyFields body = some root.2 := by
            simpa [CompactNumericProofRootBranchValid, htag7] using hparser
          cases hsequent : compactSequentTokenValueParser body with
          | none =>
              simp [compactNodeSequentOnlyFields, hsequent] at hfields
          | some parsed =>
              rcases parsed with ⟨values, suffix⟩
              have hroot :
                  root =
                    (7, (values, ([], ([], ([], suffix))))) := by
                simp [compactNodeSequentOnlyFields, hsequent] at hfields
                exact Prod.ext htag7 (by simpa using hfields.symm)
              subst root
              simpa using
                exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_results_with_publicBounds
                  7 body values suffix (Or.inr (Or.inl rfl)) hsequent
        · have hinputTag : inputTag = 8 := by
            by_contra hne
            simp [CompactNumericProofRootBranchValid, hne, htag8] at hparser
          subst inputTag
          have hfields :
              compactNodeSequentOnlyFields body = some root.2 := by
            simpa [CompactNumericProofRootBranchValid, htag8] using hparser
          cases hsequent : compactSequentTokenValueParser body with
          | none =>
              simp [compactNodeSequentOnlyFields, hsequent] at hfields
          | some parsed =>
              rcases parsed with ⟨values, suffix⟩
              have hroot :
                  root =
                    (8, (values, ([], ([], ([], suffix))))) := by
                simp [compactNodeSequentOnlyFields, hsequent] at hfields
                exact Prod.ext htag8 (by simpa using hfields.symm)
              subst root
              simpa using
                exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_results_with_publicBounds
                  8 body values suffix (Or.inr (Or.inr rfl)) hsequent

#print axioms
  exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_results_with_publicBounds
#print axioms
  exists_compactProofRootSequentOnlyEndpointBoundedGraph_of_success_with_publicBounds

end FoundationCompactNumericListedDirectProofRootSequentOnlyPublicBounds
