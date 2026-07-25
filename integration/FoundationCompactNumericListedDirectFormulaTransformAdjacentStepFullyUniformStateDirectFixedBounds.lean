import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexBranchDirectBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Uniform state bounds for one formula-transform adjacent row

Both state-row children are charged to fixed public polynomials.  The checked
six-way transform-step certificate remains visible through its deterministic
public-finite resource.  This is the exact intermediate endpoint needed before
the step resource is compressed under the common coordinate bound.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFullyUniformStateDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAClosedHybridContextTransport
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStepFormula
open FoundationCompactNumericListedDirectFormulaTransformStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStepRowsPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepAtValuationIndexPublicBounds

private theorem arithmeticAddTerm_eq_func_uniformAdjacent
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
    Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables_uniformAdjacent
    (functionSymbol : LO.FirstOrder.Language.Func ℒₒᵣ 2)
    (left right : ValuationTerm) :
    (LO.FirstOrder.Semiterm.func functionSymbol
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables := by
  ext candidate
  constructor
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact Finset.mem_union_left _ hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero => exact Finset.mem_union_right _ hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  · intro hcandidate
    rw [LO.FirstOrder.Semiterm.freeVariables_func]
    rcases Finset.mem_union.mp hcandidate with hleft | hright
    · exact Finset.mem_biUnion.mpr ⟨0, Finset.mem_univ 0, hleft⟩
    · exact Finset.mem_biUnion.mpr ⟨1, Finset.mem_univ 1, hright⟩

private theorem arithmeticAddTerm_freeVariables_uniformAdjacent
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func_uniformAdjacent]
  exact binaryFunctionTerm_freeVariables_uniformAdjacent
    Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty_uniformAdjacent :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd_uniformAdjacent
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_uniformAdjacent]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_uniformAdjacent
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
    (indexTerm : ValuationTerm) (numericBound bitBound stepResource : Nat) :
    Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let contextResource :=
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length
  let currentResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      indexTerm numericBound bitBound
  let nextResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      nextIndexTerm numericBound bitBound
  contextResource + currentResource + nextResource + stepResource +
    2 * (binaryNatCode 4).length + 1

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial
    (tokenTable width tokenCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let currentResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      indexTerm numericBound bitBound
  let nextResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      nextIndexTerm numericBound bitBound
  let stepResource := compactFormulaTransformStepRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let syntaxResource :=
    compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      indexTerm numericBound bitBound stepResource
  let nextStepResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource nextResource stepResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource currentResource
    nextStepResource

noncomputable def
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hzero : valuation 0 <= numericBound)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcurrentParserTokensCount :
      row.currentCoordinates.parserTokensCount <= numericBound)
    (hcurrentParserTasksCount :
      row.currentCoordinates.parserTasksCount <= numericBound)
    (hcurrentOutputCount :
      row.currentCoordinates.outputCount <= numericBound)
    (hnextParserTokensCount :
      row.nextCoordinates.parserTokensCount <= numericBound)
    (hnextParserTasksCount :
      row.nextCoordinates.parserTasksCount <= numericBound)
    (hnextOutputCount :
      row.nextCoordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcurrentParserTokensTableSize :
      Nat.size row.currentCoordinates.parserTokensBoundary <= bitBound)
    (hcurrentParserTasksTableSize :
      Nat.size row.currentCoordinates.parserTasksBoundary <= bitBound)
    (hcurrentOutputTableSize :
      Nat.size row.currentCoordinates.outputBoundary <= bitBound)
    (hnextParserTokensTableSize :
      Nat.size row.nextCoordinates.parserTokensBoundary <= bitBound)
    (hnextParserTasksTableSize :
      Nat.size row.nextCoordinates.parserTasksBoundary <= bitBound)
    (hnextOutputTableSize :
      Nat.size row.nextCoordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm mode witnessStart
        witnessFinish witnessCount row)
      (compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial
        tokenTable width tokenCount indexTerm mode witnessStart witnessFinish
        witnessCount numericBound bitBound row) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_uniformAdjacent,
      arithmeticOneTerm_freeVariables_eq_empty_uniformAdjacent]
    simpa using hindexVariables
  have hnextAtTerm : CompactFormulaTransformStateAtRows tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [nextIndexTerm, termValue_arithmeticAdd_uniformAdjacent,
      termValue_arithmeticOne_uniformAdjacent] using hnext
  let currentFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula := compactFormulaTransformStepRowsClosedFormula tokenTable
    width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let nextStepFormula := nextFormula ⋏ stepFormula
  let explicitFormula := currentFormula ⋏ nextStepFormula
  let currentResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      indexTerm numericBound bitBound
  let nextResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
      nextIndexTerm numericBound bitBound
  let stepResource := compactFormulaTransformStepRowsPublicFinitePayloadEnvelope
    tokenTable width tokenCount row.currentCoordinates row.nextCoordinates mode
    row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
    witnessCount
  let syntaxResource :=
    compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      indexTerm numericBound bitBound stepResource
  let nextStepResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource nextResource stepResource
  let currentBound :=
    compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize numericBound bitBound
      hindexVariables hcurrent hzero hwidthBound htokenCount hstateCount
      hcurrentParserTokensCount hcurrentParserTasksCount hcurrentOutputCount
      htokenTableSize hstateBoundarySize hcurrentParserTokensTableSize
      hcurrentParserTasksTableSize hcurrentOutputTableSize hnumericSize
      hnumericBit
  let nextBound :=
    compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize numericBound bitBound
      hnextIndexVariables hnextAtTerm hzero hwidthBound htokenCount hstateCount
      hnextParserTokensCount hnextParserTasksCount hnextOutputCount
      htokenTableSize hstateBoundarySize hnextParserTokensTableSize
      hnextParserTasksTableSize hnextOutputTableSize hnumericSize hnumericBit
  let stepCertificate :=
    compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph tokenTable
      width tokenCount row.currentCoordinates row.nextCoordinates mode
      row.stepWitness row.consumedCount row.mappedHead witnessStart witnessFinish
      witnessCount hstep
  have hstepClosed :=
    compactFormulaTransformStepRowsClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
      mode row.stepWitness row.consumedCount row.mappedHead witnessStart
      witnessFinish witnessCount
  let stepProof := compileClosedHybridAtValuation (target := valuation)
    stepCertificate hstepClosed
  have hstepProof : stepProof.payloadLength <= stepResource :=
    (compileClosedHybridAtValuation_payloadLength_le_structural
      (target := valuation) stepCertificate hstepClosed).trans
        (compactFormulaTransformStepRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
          tokenTable width tokenCount row.currentCoordinates
          row.nextCoordinates mode row.stepWitness row.consumedCount
          row.mappedHead witnessStart witnessFinish witnessCount hstep)
  have hcurrentCode :
      (binaryFormulaCode currentFormula).length <= currentResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      currentBound.proof).trans currentBound.payloadLength_le
  have hnextCode :
      (binaryFormulaCode nextFormula).length <= nextResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      nextBound.proof).trans nextBound.payloadLength_le
  have hstepCode :
      (binaryFormulaCode stepFormula).length <= stepResource :=
    (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
      stepProof).trans hstepProof
  have hnextStepCode :
      (binaryFormulaCode nextStepFormula).length <=
        nextResource + stepResource + (binaryNatCode 4).length := by
    dsimp only [nextStepFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hexplicitCode :
      (binaryFormulaCode explicitFormula).length <=
        currentResource + nextResource + stepResource +
          2 * (binaryNatCode 4).length := by
    dsimp only [explicitFormula, nextStepFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hcurrentVariables : currentFormula.freeVariables ⊆ {0} := by
    exact
      compactFormulaTransformStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
        tokenTable width tokenCount stateBoundary stateCount indexTerm
        row.currentCoordinates row.currentSize hindexVariables
  have hnextVariables : nextFormula.freeVariables ⊆ {0} := by
    exact
      compactFormulaTransformStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
        tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
        row.nextCoordinates row.nextSize hnextIndexVariables
  have hstepVariables : stepFormula.freeVariables ⊆ {0} := by
    rw [hstepClosed]
    simp
  have hnextStepVariables : nextStepFormula.freeVariables ⊆ {0} := by
    dsimp only [nextStepFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hnextVariables hstepVariables
  have hexplicitVariables : explicitFormula.freeVariables ⊆ {0} := by
    dsimp only [explicitFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hcurrentVariables hnextStepVariables
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource
      compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
    dsimp only [nextIndexTerm, currentResource, nextResource, stepResource]
    omega
  have hcontextNextStep :
      formulaCodeSum
          (valuationContext nextStepFormula.freeVariables valuation) <=
        syntaxResource := by
    exact
      (compactFormulaTransformValuationContextFormulaCodeSum_le_singleton
        valuation nextStepFormula numericBound hnextStepVariables hzero).trans
        (by
          unfold syntaxResource
            compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
          dsimp only [nextIndexTerm, currentResource, nextResource,
            stepResource]
          omega)
  have hcontextExplicit :
      formulaCodeSum
          (valuationContext explicitFormula.freeVariables valuation) <=
        syntaxResource := by
    exact
      (compactFormulaTransformValuationContextFormulaCodeSum_le_singleton
        valuation explicitFormula numericBound hexplicitVariables hzero).trans
        (by
          unfold syntaxResource
            compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
          dsimp only [nextIndexTerm, currentResource, nextResource,
            stepResource]
          omega)
  have hcurrentSyntax :
      (binaryFormulaCode currentFormula).length <= syntaxResource :=
    hcurrentCode.trans (by
      unfold syntaxResource
        compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      dsimp only [nextIndexTerm, currentResource, nextResource, stepResource]
      omega)
  have hnextSyntax :
      (binaryFormulaCode nextFormula).length <= syntaxResource :=
    hnextCode.trans (by
      unfold syntaxResource
        compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      dsimp only [nextIndexTerm, currentResource, nextResource, stepResource]
      omega)
  have hstepSyntax :
      (binaryFormulaCode stepFormula).length <= syntaxResource :=
    hstepCode.trans (by
      unfold syntaxResource
        compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      dsimp only [nextIndexTerm, currentResource, nextResource, stepResource]
      omega)
  have hnextStepSyntax :
      (binaryFormulaCode nextStepFormula).length <= syntaxResource :=
    hnextStepCode.trans (by
      unfold syntaxResource
        compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      dsimp only [nextIndexTerm, currentResource, nextResource, stepResource]
      omega)
  have hexplicitSyntax :
      (binaryFormulaCode explicitFormula).length <= syntaxResource :=
    hexplicitCode.trans (by
      unfold syntaxResource
        compactFormulaTransformAdjacentStepUniformStateAssemblySyntaxPolynomial
      dsimp only [nextIndexTerm, currentResource, nextResource, stepResource]
      omega)
  let nextStepProof := compileDirectConjunction nextBound.proof stepProof
  have hnextStepRaw := compileDirectConjunction_payloadLength_le nextBound.proof
    stepProof nextResource stepResource nextBound.payloadLength_le hstepProof
  have hnextStepEnvelope :
      transparentHybridConjunctionPayloadEnvelope valuation nextFormula
          stepFormula nextResource stepResource <=
        nextStepResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation nextFormula
        stepFormula nextResource stepResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      nextFormula stepFormula nextResource stepResource syntaxResource
      hpositive hcontextNextStep hnextSyntax hstepSyntax hnextStepSyntax
  have hnextStepProof :
      nextStepProof.payloadLength <= nextStepResource :=
    hnextStepRaw.trans hnextStepEnvelope
  let explicitProof := compileDirectConjunction currentBound.proof nextStepProof
  have hexplicitRaw := compileDirectConjunction_payloadLength_le
    currentBound.proof nextStepProof currentResource nextStepResource
    currentBound.payloadLength_le hnextStepProof
  have hexplicitEnvelope :
      transparentHybridConjunctionPayloadEnvelope valuation currentFormula
          nextStepFormula currentResource nextStepResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource currentResource
          nextStepResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation currentFormula
        nextStepFormula currentResource nextStepResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      currentFormula nextStepFormula currentResource nextStepResource
      syntaxResource hpositive hcontextExplicit hcurrentSyntax hnextStepSyntax
      hexplicitSyntax
  have hexplicit :
      explicitProof.payloadLength <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource currentResource
          nextStepResource :=
    hexplicitRaw.trans hexplicitEnvelope
  have hformula :
      compactFormulaTransformAdjacentStepRowAtValuationIndexExplicitFormula
          tokenTable width tokenCount stateBoundary stateCount indexTerm mode
          witnessStart witnessFinish witnessCount row =
        compactFormulaTransformAdjacentStepRowAtValuationIndexFormula tokenTable
          width tokenCount stateBoundary stateCount indexTerm mode witnessStart
          witnessFinish witnessCount row :=
    (compactFormulaTransformAdjacentStepRowAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm mode
      witnessStart witnessFinish witnessCount row).symm
  let proof := castValuationContextProof hformula explicitProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula explicitProof]
  simpa only [
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial,
    nextIndexTerm, currentResource, nextResource, stepResource, syntaxResource,
    nextStepResource, currentFormula, nextFormula, stepFormula,
    nextStepFormula, explicitFormula, currentBound, nextBound, stepCertificate,
    stepProof, nextStepProof, explicitProof] using hexplicit

theorem
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (row : CompactFormulaTransformAdjacentStepRow)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformAdjacentStepRowGraph tokenTable width
      tokenCount stateBoundary stateCount (termValue valuation indexTerm) mode
      witnessStart witnessFinish witnessCount row)
    (hzero : valuation 0 <= numericBound)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcurrentParserTokensCount :
      row.currentCoordinates.parserTokensCount <= numericBound)
    (hcurrentParserTasksCount :
      row.currentCoordinates.parserTasksCount <= numericBound)
    (hcurrentOutputCount :
      row.currentCoordinates.outputCount <= numericBound)
    (hnextParserTokensCount :
      row.nextCoordinates.parserTokensCount <= numericBound)
    (hnextParserTasksCount :
      row.nextCoordinates.parserTasksCount <= numericBound)
    (hnextOutputCount :
      row.nextCoordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcurrentParserTokensTableSize :
      Nat.size row.currentCoordinates.parserTokensBoundary <= bitBound)
    (hcurrentParserTasksTableSize :
      Nat.size row.currentCoordinates.parserTasksBoundary <= bitBound)
    (hcurrentOutputTableSize :
      Nat.size row.currentCoordinates.outputBoundary <= bitBound)
    (hnextParserTokensTableSize :
      Nat.size row.nextCoordinates.parserTokensBoundary <= bitBound)
    (hnextParserTasksTableSize :
      Nat.size row.nextCoordinates.parserTasksBoundary <= bitBound)
    (hnextOutputTableSize :
      Nat.size row.nextCoordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound) :
    (compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      mode witnessStart witnessFinish witnessCount numericBound bitBound row
      hindexVariables hgraph hzero hwidthBound htokenCount hstateCount
      hcurrentParserTokensCount hcurrentParserTasksCount hcurrentOutputCount
      hnextParserTokensCount hnextParserTasksCount hnextOutputCount
      htokenTableSize hstateBoundarySize hcurrentParserTokensTableSize
      hcurrentParserTasksTableSize hcurrentOutputTableSize
      hnextParserTokensTableSize hnextParserTasksTableSize hnextOutputTableSize
      hnumericSize hnumericBit).proof.payloadLength <=
    compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepPayloadPolynomial
      tokenTable width tokenCount indexTerm mode witnessStart witnessFinish
      witnessCount numericBound bitBound row :=
  (compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound
    valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
    mode witnessStart witnessFinish witnessCount numericBound bitBound row
    hindexVariables hgraph hzero hwidthBound htokenCount hstateCount
    hcurrentParserTokensCount hcurrentParserTasksCount hcurrentOutputCount
    hnextParserTokensCount hnextParserTasksCount hnextOutputCount
    htokenTableSize hstateBoundarySize hcurrentParserTokensTableSize
    hcurrentParserTasksTableSize hcurrentOutputTableSize
    hnextParserTokensTableSize hnextParserTasksTableSize hnextOutputTableSize
    hnumericSize hnumericBit).payloadLength_le

#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound
#print axioms
  compactFormulaTransformAdjacentStepRowAtValuationIndexUniformStatePublicFiniteStepDirectBound_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformAdjacentStepFullyUniformStateDirectFixedBounds
