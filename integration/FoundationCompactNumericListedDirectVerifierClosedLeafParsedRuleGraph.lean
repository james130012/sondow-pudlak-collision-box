import integration.FoundationCompactNumericListedDirectVerifierClosedLeafCrossTableBridgeGraph
import integration.FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectVerifierClosedLeafRuleSelfContainedGraph
import integration.FoundationCompactNumericListedDirectProofRootLeafFieldSemantics

/-!
# Parsed closed leaf with an audited rule table

The parser table is retained unchanged.  The closed-rule trace is held in a
separate canonical table and is connected to the parser root by two bounded
cross-table slice equalities, for `Gamma` and the first formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierClosedLeafParsedRuleGraph

open FoundationCompactNumericListedNodeFields
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskFieldRealization
open FoundationCompactNumericListedDirectNodeTransitionCases
open FoundationCompactNumericListedDirectVerifierStepCases
open FoundationCompactNumericListedDirectVerifierParsePayloadSuccessExposedSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleSelfContainedGraph
open FoundationCompactNumericListedDirectVerifierClosedLeafCrossTableBridgeGraph
open FoundationCompactNumericListedDirectProofRootLeafFieldSemantics

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericSuccIndSentence
open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectNatListWitnessRows
open FoundationCompactNumericListedDirectNatListListWitnessRows
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectFormulaTransformStateLayout
open FoundationCompactNumericListedDirectFormulaTransformTotalExactFormula
open FoundationCompactNumericListedDirectFormulaTransformTotalExactCompleteness
open FoundationCompactNumericListedDirectClosedRuleCheck
open FoundationCompactNumericListedDirectPackedRouteTable
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRows
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCompleteness
open FoundationCompactNumericListedDirectVerifierClosedLeafRuleRowsCanonicalCompleteness

theorem exists_closedRuleTable_with_rootLayouts
    (Gamma : List (List Nat))
    (parsed : LO.FirstOrder.ArithmeticSemiformula Nat 0) :
    let formula := compactArithmeticFormulaTokens parsed
    let negated := compactArithmeticFormulaTokens (∼parsed)
    ∃ tokenTable width tokenCount
        gammaStart gammaFinish gammaBoundary gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negatedBoundarySize
        stateBoundary emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound,
      CompactNumericVerifierClosedLeafRuleSelfContainedGraph
        tokenTable width tokenCount 0 0
        gammaStart gammaFinish gammaBoundary Gamma.length gammaBoundarySize
        formulaStart formulaFinish formulaBoundary formula.length formulaBoundarySize
        negatedStart negatedFinish negatedBoundary negated.length negatedBoundarySize
        stateBoundary (compactSyntaxRunFuelBound formula + 1)
        emptyStart emptyFinish emptyBoundary emptyBoundarySize
        tableWidth valueBound
        (compactAdditiveBoolTag (compactClosedRuleCheck (Gamma, formula))) ∧
      CompactAdditiveNatListListDirectLayout
        tokenTable width tokenCount gammaStart gammaFinish Gamma ∧
      CompactAdditiveNatListDirectLayout
        tokenTable width tokenCount formulaStart formulaFinish formula := by
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
  have hformulaSlot := compactPackedNatListSlot_canonical chunks 1 formula
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, formula])
  have hnegatedSlot := compactPackedNatListSlot_canonical chunks 2 negated
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, negated])
  have hemptySlot := compactPackedNatListSlot_canonical chunks 3 empty
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, empty])
  have htraceRows := compactPackedFormulaTransformStateRows_canonical
    chunks 4 trace
    (by simp [chunks, compactClosedLeafCanonicalChunks])
    (by simp [chunks, compactClosedLeafCanonicalChunks, trace, formula])
  dsimp only at hformulaSlot hnegatedSlot hemptySlot htraceRows
  let gammaFront := compactPackedChunkPrefix chunks 0
  let gammaBack := compactPackedChunkSuffix chunks 0
  have hgammaTokens : gammaFront ++ compactAdditiveEncode Gamma ++ gammaBack =
      chunks.flatten := by
    simp only [gammaFront, gammaBack]
    exact compactPackedChunkPrefix_append_getElem_append_suffix chunks 0
      (by simp [chunks, compactClosedLeafCanonicalChunks])
  have hgammaRaw := compactAdditiveStructuredListElementLayouts_canonical
    CompactAdditiveNatListDirectLayout compactAdditiveNatListDirectLayout_canonical
      gammaFront Gamma gammaBack
  dsimp only at hgammaRaw
  rw [hgammaTokens] at hgammaRaw
  have hgammaStructure : CompactAdditiveStructuredListLayout
      tokenTable width tokens.length gammaStart Gamma.length gammaFinish
        gammaBoundary := by
    simpa [tokenTable, width, tokens, gammaStart, gammaFinish, gammaBoundary,
      compactPackedNatListListBoundary, gammaFront] using hgammaRaw.1
  have hgammaSize : Nat.size gammaBoundary ≤
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
      CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
        hgammaRows, rfl, hgammaSize⟩
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
    simpa [tokenTable, width, tokens, stateBoundary] using htraceRows
  have hnegatedExact : compactFormulaNegationExact 0 formula = some negated := by
    simp [formula, negated]
  rcases CompactFormulaTransformTotalExactBoundedGraph.of_canonical_trace
      htraceRows' hemptyLayout rfl hformulaRows hnegatedRows hemptyRows
      (by
        rw [compactFormulaTransformResult_negation]
        change negated = (compactFormulaNegationExact 0 formula).getD []
        rw [hnegatedExact]
        simp) with ⟨tableWidth, htransform⟩
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
  exact ⟨tokenTable, width, tokens.length,
    gammaStart, gammaFinish, gammaBoundary, Nat.size gammaBoundary,
    formulaSlot.start, formulaSlot.finish, formulaSlot.boundary,
      formulaSlot.boundarySize,
    negatedSlot.start, negatedSlot.finish, negatedSlot.boundary,
      negatedSlot.boundarySize,
    stateBoundary, emptySlot.start, emptySlot.finish, emptySlot.boundary,
      emptySlot.boundarySize, tableWidth, 2 ^ tableWidth,
    ⟨hgammaWitness, hformulaSlot.rows, hnegatedSlot.rows, hemptySlot.rows, hleaf⟩,
    hgammaLayout, hformulaLayout⟩

def CompactNumericVerifierClosedLeafParsedRuleGraph
    (stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound : Nat) : Prop :=
  CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
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
      rootGammaBoundarySize ∧
    CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
        ruleNegatedBoundarySize
      ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound resultBool ∧
    proofTag = ruleProofTag ∧ certificateTag = ruleCertificateTag ∧
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      rootGammaFinish firstFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish

def compactNumericVerifierClosedLeafParsedRuleGraphDef :
    𝚺₀.Semisentence 69 := .mkSigma
  “stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound.
    !(compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef)
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
      rootGammaBoundarySize ∧
    !(compactNumericVerifierClosedLeafRuleSelfContainedGraphDef)
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
        ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
        ruleNegatedBoundarySize
      ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound resultBool ∧
    proofTag = ruleProofTag ∧ certificateTag = ruleCertificateTag ∧
    !(compactNumericVerifierClosedLeafCrossTableBridgeGraphDef)
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      rootGammaFinish firstFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish”

def compactNumericVerifierClosedLeafParsedRuleGraphEnvironment
    (stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound : Nat) : Fin 69 → Nat :=
  ![stateTable, stateWidth, stateTokenCount, stateProofStart, stateProofFinish,
    stateCertificateStart, stateCertificateFinish,
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    rootGammaBoundarySize, resultBool,
    ruleTable, ruleWidth, ruleTokenCount, ruleProofTag, ruleCertificateTag,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary, ruleGammaCount,
    ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary, ruleFormulaCount,
    ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary, ruleNegatedCount,
    ruleNegatedBoundarySize, ruleStateBoundary, ruleStateCount,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary, ruleEmptyBoundarySize,
    ruleTableWidth, ruleValueBound]

set_option maxRecDepth 65536 in
@[simp] theorem compactNumericVerifierClosedLeafParsedRuleGraphDef_spec
    (stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
      ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound : Nat) :
    compactNumericVerifierClosedLeafParsedRuleGraphDef.val.Evalb
        (compactNumericVerifierClosedLeafParsedRuleGraphEnvironment
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
          rootGammaBoundarySize resultBool
          ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
          ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
          ruleGammaBoundarySize
          ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
          ruleFormulaBoundarySize
          ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
          ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
          ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
          ruleTableWidth ruleValueBound) ↔
      CompactNumericVerifierClosedLeafParsedRuleGraph
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
        rootGammaBoundarySize resultBool
        ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
        ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
        ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
        ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
        ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
        ruleTableWidth ruleValueBound := by
  let env := compactNumericVerifierClosedLeafParsedRuleGraphEnvironment
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
    rootGammaBoundarySize resultBool
    ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
    ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
    ruleGammaBoundarySize
    ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
    ruleFormulaBoundarySize
    ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
    ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
    ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
    ruleTableWidth ruleValueBound
  change compactNumericVerifierClosedLeafParsedRuleGraphDef.val.Evalb env ↔ _
  have hparseEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 69), #1, #2, #3, #4, #5, #6,
          #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
          #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
          #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]) =
        ![stateTable, stateWidth, stateTokenCount, stateProofStart,
          stateProofFinish, stateCertificateStart, stateCertificateFinish,
          proofTable, proofWidth, proofTokenCount, proofInputStart,
          proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateInputStart, certificateInputFinish,
          axiomStart, axiomFinish, formulaStart, formulaFinish,
          suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
          rootGammaFinish, rootGammaCount, rootGammaBoundary, firstFinish,
          firstCount, secondFinish, secondCount, witnessFinish, witnessCount,
          suffixCount, rootGammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hruleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#41 : Semiterm ℒₒᵣ Empty 69), #42, #43, #44, #45,
          #46, #47, #48, #49, #50, #51, #52, #53, #54, #55, #56,
          #57, #58, #59, #60, #61, #62, #63, #64, #65, #66, #67, #68,
          #40]) =
        ![ruleTable, ruleWidth, ruleTokenCount, ruleProofTag, ruleCertificateTag,
          ruleGammaStart, ruleGammaFinish, ruleGammaBoundary, ruleGammaCount,
          ruleGammaBoundarySize, ruleFormulaStart, ruleFormulaFinish,
          ruleFormulaBoundary, ruleFormulaCount, ruleFormulaBoundarySize,
          ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
          ruleNegatedCount, ruleNegatedBoundarySize, ruleStateBoundary,
          ruleStateCount, ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
          ruleEmptyBoundarySize, ruleTableWidth, ruleValueBound, resultBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hbridgeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#7 : Semiterm ℒₒᵣ Empty 69), #8, #9, ‘(#12 + 1)’, #29,
          #29, #32, #41, #42, #43, #46, #47, #51, #52]) =
        ![proofTable, proofWidth, proofTokenCount, rootStart + 1,
          rootGammaFinish, rootGammaFinish, firstFinish,
          ruleTable, ruleWidth, ruleTokenCount, ruleGammaStart, ruleGammaFinish,
    ruleFormulaStart, ruleFormulaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hparse := compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef_spec
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
    rootGammaBoundarySize
  simp only [compactNumericParsePayloadSuccessExposedSeparatedTablesGraphEnvironment]
    at hparse
  have hrule := compactNumericVerifierClosedLeafRuleSelfContainedGraphDef_spec
    ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
    ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
    ruleGammaBoundarySize
    ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
    ruleFormulaBoundarySize
    ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary ruleNegatedCount
    ruleNegatedBoundarySize ruleStateBoundary ruleStateCount
    ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
    ruleTableWidth ruleValueBound resultBool
  have hbridge := compactNumericVerifierClosedLeafCrossTableBridgeGraphDef_spec
    proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
    rootGammaFinish firstFinish
    ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
    ruleFormulaStart ruleFormulaFinish
  simp only [compactNumericVerifierClosedLeafParsedRuleGraphDef,
    CompactNumericVerifierClosedLeafParsedRuleGraph]
  apply and_congr
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#0 : Semiterm ℒₒᵣ Empty 69), #1, #2, #3, #4, #5, #6,
        #7, #8, #9, #10, #11, #12, #13, #14, #15, #16, #17, #18,
        #19, #20, #21, #22, #23, #24, #25, #26, #27, #28, #29,
        #30, #31, #32, #33, #34, #35, #36, #37, #38, #39]
      compactNumericParsePayloadSuccessExposedSeparatedTablesGraphDef.val).trans ?_
    rw [hparseEnv]
    exact hparse
  apply and_congr
  · refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
      ![(#41 : Semiterm ℒₒᵣ Empty 69), #42, #43, #44, #45,
        #46, #47, #48, #49, #50, #51, #52, #53, #54, #55, #56,
        #57, #58, #59, #60, #61, #62, #63, #64, #65, #66, #67, #68,
        #40]
      compactNumericVerifierClosedLeafRuleSelfContainedGraphDef.val).trans ?_
    rw [hruleEnv]
    exact hrule
  apply and_congr
  · exact Iff.rfl
  apply and_congr
  · exact Iff.rfl
  refine (Semiformula.eval_substs (b := env) (f := Empty.elim)
    ![(#7 : Semiterm ℒₒᵣ Empty 69), #8, #9, ‘(#12 + 1)’, #29,
      #29, #32, #41, #42, #43, #46, #47, #51, #52]
    compactNumericVerifierClosedLeafCrossTableBridgeGraphDef.val).trans ?_
  rw [hbridgeEnv]
  exact hbridge

theorem compactNumericVerifierClosedLeafParsedRuleGraphDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierClosedLeafParsedRuleGraphDef.val := by
  simp [compactNumericVerifierClosedLeafParsedRuleGraphDef]

theorem CompactNumericVerifierClosedLeafParsedRuleGraph.sound
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
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
      ruleFormulaCount ruleFormulaBoundarySize ruleNegatedStart ruleNegatedFinish
      ruleNegatedBoundary ruleNegatedCount ruleNegatedBoundarySize ruleStateBoundary
      ruleStateCount ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
      ruleEmptyBoundarySize ruleTableWidth ruleValueBound : Nat}
    (hgraph : CompactNumericVerifierClosedLeafParsedRuleGraph
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize resultBool
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
      ruleFormulaCount ruleFormulaBoundarySize ruleNegatedStart ruleNegatedFinish
      ruleNegatedBoundary ruleNegatedCount ruleNegatedBoundarySize ruleStateBoundary
      ruleStateCount ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
      ruleEmptyBoundarySize ruleTableWidth ruleValueBound) :
    CompactNumericParsePayloadSuccessExposedSeparatedTablesGraph
      stateTable stateWidth stateTokenCount stateProofStart stateProofFinish
      stateCertificateStart stateCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish axiomStart axiomFinish formulaStart
      formulaFinish suffixStart suffixFinish certificateTag certificateEndpointBound
      rootGammaFinish rootGammaCount rootGammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      rootGammaBoundarySize ∧
    CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      ruleTable ruleWidth ruleTokenCount ruleProofTag ruleCertificateTag
      ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
      ruleFormulaCount ruleFormulaBoundarySize ruleNegatedStart ruleNegatedFinish
      ruleNegatedBoundary ruleNegatedCount ruleNegatedBoundarySize ruleStateBoundary
      ruleStateCount ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
      ruleEmptyBoundarySize ruleTableWidth ruleValueBound resultBool ∧
    proofTag = ruleProofTag ∧ certificateTag = ruleCertificateTag ∧
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      rootGammaFinish firstFinish
      ruleTable ruleWidth ruleTokenCount ruleGammaStart ruleGammaFinish
      ruleFormulaStart ruleFormulaFinish := hgraph

theorem exists_compactNumericVerifierClosedLeafParsedRuleGraph_of_parsers
    {stateTable stateWidth stateTokenCount
      stateProofStart stateProofFinish stateCertificateStart
        stateCertificateFinish : Nat}
    {proofTokens certificateTokens : List Nat}
    {root : CompactNumericVerifierTask}
    {certificateNode : CompactNumericCertificateNode}
    {restTasks : List CompactNumericVerifierTask}
    {values : List CompactNumericChildResult}
    (hproofLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish proofTokens)
    (hcertificateLayout : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        stateCertificateStart stateCertificateFinish certificateTokens)
    (hproofParser : compactListedProofNodeFieldsParser proofTokens = some root)
    (hcertificateParser :
      compactStructuralCertificateNodeParser certificateTokens =
        some certificateNode)
    (hrootTag : root.1 = 0)
    (hcertificateTag : certificateNode.1 = 0) :
    ∃ proofTable proofWidth proofTokenCount proofInputStart proofInputFinish,
    ∃ rootStart rootFinish proofTag proofEndpointBound,
    ∃ certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish,
    ∃ axiomStart axiomFinish formulaStart formulaFinish,
    ∃ suffixStart suffixFinish certificateTag certificateEndpointBound,
    ∃ gammaFinish gammaCount gammaBoundary firstFinish firstCount
      secondFinish secondCount witnessFinish witnessCount suffixCount
      gammaBoundarySize,
    ∃ ruleTable ruleWidth ruleTokenCount,
    ∃ ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
      ruleGammaBoundarySize,
    ∃ ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary ruleFormulaCount
      ruleFormulaBoundarySize,
    ∃ ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
      ruleNegatedCount ruleNegatedBoundarySize ruleStateBoundary ruleStateCount,
    ∃ ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
      ruleEmptyBoundarySize ruleTableWidth ruleValueBound,
      CompactNumericVerifierClosedLeafParsedRuleGraph
        stateTable stateWidth stateTokenCount
        stateProofStart stateProofFinish
        stateCertificateStart stateCertificateFinish
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound
        gammaFinish gammaCount gammaBoundary firstFinish firstCount
        secondFinish secondCount witnessFinish witnessCount suffixCount
        gammaBoundarySize
        (compactAdditiveBoolTag
          (compactClosedRuleCheck (root.2.1, root.2.2.1)))
        ruleTable ruleWidth ruleTokenCount 0 0
        ruleGammaStart ruleGammaFinish ruleGammaBoundary ruleGammaCount
          ruleGammaBoundarySize
        ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
          ruleFormulaCount ruleFormulaBoundarySize
        ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
          ruleNegatedCount ruleNegatedBoundarySize
        ruleStateBoundary ruleStateCount
        ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary
          ruleEmptyBoundarySize ruleTableWidth ruleValueBound := by
  rcases compactListedProofNodeFieldsParser_tag_zero_firstFormula
      hproofParser hrootTag with
    ⟨parsedFormula, hparsedFormula⟩
  have htagMatch : CompactNumericNodeTransitionTagMatch
      root.1 certificateNode.1 := by
    rw [hrootTag, hcertificateTag]
    exact Or.inl ⟨rfl, rfl⟩
  rcases (compactNumericNodeTransition_exists_iff_tagMatch
      root certificateNode restTasks values).2 htagMatch with
    ⟨parsed, htransition⟩
  have hparse : compactNumericParsePayload
      ((proofTokens, certificateTokens), (restTasks, values)) = some parsed :=
    (compactNumericParsePayload_eq_some_iff _ _).2
      ⟨root, certificateNode, hproofParser, hcertificateParser, htransition⟩
  rcases
      exists_compactNumericParsePayloadSuccessExposedSeparatedTablesGraph_of_exists_some
        hproofLayout hcertificateLayout ⟨parsed, hparse⟩ with
    ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
      proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateInputStart, certificateInputFinish,
      axiomStart, axiomFinish, formulaStart, formulaFinish,
      suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
      gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
      secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
      gammaBoundarySize, hsuccess⟩
  rcases hsuccess.1.2.2.1.sound with
    ⟨decodedInput, decodedRoot, hdecodedInput, hdecodedRoot,
      hdecodedParser, hdecodedTag⟩
  have hdecodedInputEq : decodedInput = proofTokens :=
    hsuccess.1.1.natListValues_eq hproofLayout hdecodedInput
  subst decodedInput
  have hdecodedRootEq : decodedRoot = root :=
    Option.some.inj (hdecodedParser.symm.trans hproofParser)
  subst decodedRoot
  have hproofTag : proofTag = 0 := hdecodedTag.symm.trans hrootTag
  have hcoordTagMatch := hsuccess.1.2.2.2.2
  have hcertificateTagCoord : certificateTag = 0 := by
    rw [hproofTag] at hcoordTagMatch
    simpa [CompactNumericNodeTransitionTagMatch] using hcoordTagMatch
  rcases CompactNumericVerifierTaskCoreGraph.realizeDirectLayoutWithFields
      hsuccess.2 with
    ⟨realizedRoot, hrealizedRoot, _hrealizedTag,
      hgammaRows, hgammaLength, hfirstLayout, _hfirstLength,
      _hsecondLayout, _hsecondLength, _hwitnessLayout, _hwitnessLength,
      _hsuffixLayout, _hsuffixLength⟩
  have hrealizedEq : realizedRoot = root :=
    CompactNumericVerifierTaskCoreGraph.realizedTask_eq
      hsuccess.2 hdecodedRoot hrealizedRoot
  subst realizedRoot
  have hcoreSaved := hsuccess.2
  rcases hcoreSaved with
    ⟨_hrootTagCell, hgammaStructureRaw, _hgammaRowsRaw,
      hgammaSizeEqRaw, hgammaSizeRaw,
      _hfirstSlice, _hsecondSlice, _hwitnessSlice, _hsuffixSlice⟩
  have hgammaLength' : root.2.1.length = gammaCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaLength
  have hgammaStructure : CompactAdditiveStructuredListLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) root.2.1.length gammaFinish gammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf, hgammaLength'] using
      hgammaStructureRaw
  have hgammaSizeEq : gammaBoundarySize = Nat.size gammaBoundary := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeEqRaw
  have hgammaSize :
      gammaBoundarySize ≤ (gammaCount + 1) * proofTokenCount := by
    simpa [compactNumericVerifierTaskRowCoordinatesOf] using hgammaSizeRaw
  have hgammaBoundaryBound : Nat.size gammaBoundary ≤
      (root.2.1.length + 1) * proofTokenCount := by
    rw [hgammaLength', ← hgammaSizeEq]
    exact hgammaSize
  have hrootGammaLayout : CompactAdditiveNatListListDirectLayout
      proofTable proofWidth proofTokenCount
        (rootStart + 1) gammaFinish root.2.1 :=
    ⟨gammaBoundary, hgammaStructure, hgammaRows, hgammaBoundaryBound⟩
  have hrootFormulaLayout : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount gammaFinish firstFinish
        (compactArithmeticFormulaTokens parsedFormula) := by
    simpa [hparsedFormula, compactNumericVerifierTaskRowCoordinatesOf] using
      hfirstLayout
  rcases exists_closedRuleTable_with_rootLayouts root.2.1 parsedFormula with
    ⟨ruleTable, ruleWidth, ruleTokenCount,
      ruleGammaStart, ruleGammaFinish, ruleGammaBoundary,
      ruleGammaBoundarySize,
      ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
      ruleFormulaBoundarySize,
      ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
      ruleNegatedBoundarySize, ruleStateBoundary,
      ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
      ruleEmptyBoundarySize, ruleTableWidth, ruleValueBound,
      hrule, hruleGammaLayout, hruleFormulaLayout⟩
  have hbridge :=
    CompactNumericVerifierClosedLeafCrossTableBridgeGraph.of_layouts
      hrootGammaLayout hruleGammaLayout
      hrootFormulaLayout hruleFormulaLayout
  have hrule' : CompactNumericVerifierClosedLeafRuleSelfContainedGraph
      ruleTable ruleWidth ruleTokenCount 0 0
      ruleGammaStart ruleGammaFinish ruleGammaBoundary root.2.1.length
        ruleGammaBoundarySize
      ruleFormulaStart ruleFormulaFinish ruleFormulaBoundary
        root.2.2.1.length ruleFormulaBoundarySize
      ruleNegatedStart ruleNegatedFinish ruleNegatedBoundary
        (compactArithmeticFormulaTokens (∼parsedFormula)).length
        ruleNegatedBoundarySize
      ruleStateBoundary (compactSyntaxRunFuelBound root.2.2.1 + 1)
      ruleEmptyStart ruleEmptyFinish ruleEmptyBoundary ruleEmptyBoundarySize
      ruleTableWidth ruleValueBound
      (compactAdditiveBoolTag
        (compactClosedRuleCheck (root.2.1, root.2.2.1))) := by
    simpa [hparsedFormula] using hrule
  exact ⟨proofTable, proofWidth, proofTokenCount, proofInputStart,
    proofInputFinish, rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound,
    gammaFinish, gammaCount, gammaBoundary, firstFinish, firstCount,
    secondFinish, secondCount, witnessFinish, witnessCount, suffixCount,
    gammaBoundarySize,
    ruleTable, ruleWidth, ruleTokenCount,
    ruleGammaStart, ruleGammaFinish, ruleGammaBoundary, root.2.1.length,
    ruleGammaBoundarySize,
    ruleFormulaStart, ruleFormulaFinish, ruleFormulaBoundary,
    root.2.2.1.length,
    ruleFormulaBoundarySize,
    ruleNegatedStart, ruleNegatedFinish, ruleNegatedBoundary,
    (compactArithmeticFormulaTokens (∼parsedFormula)).length,
    ruleNegatedBoundarySize, ruleStateBoundary,
    compactSyntaxRunFuelBound root.2.2.1 + 1,
    ruleEmptyStart, ruleEmptyFinish, ruleEmptyBoundary,
    ruleEmptyBoundarySize, ruleTableWidth, ruleValueBound,
    hsuccess, hrule', hproofTag, hcertificateTagCoord, hbridge⟩

#print axioms compactNumericVerifierClosedLeafParsedRuleGraphDef_spec
#print axioms compactNumericVerifierClosedLeafParsedRuleGraphDef_sigmaZero
#print axioms CompactNumericVerifierClosedLeafParsedRuleGraph.sound
#print axioms exists_compactNumericVerifierClosedLeafParsedRuleGraph_of_parsers

end FoundationCompactNumericListedDirectVerifierClosedLeafParsedRuleGraph
