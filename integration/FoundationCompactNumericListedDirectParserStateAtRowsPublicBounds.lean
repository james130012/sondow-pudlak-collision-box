import integration.FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateCorePublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resources for parser-state rows

Both the numeral-index endpoint and the valuation-index endpoint use the same
open-index fixed-width entry bounds and the same checked parser-state core.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryHybridCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCorePublicBounds

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem binaryFunctionTerm_freeVariables
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

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func]
  exact binaryFunctionTerm_freeVariables Language.Add.add left right

private theorem arithmeticOneTerm_freeVariables_eq_empty :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem compactUnifiedParserStateCoreClosedFormula_freeVariables
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness) :
    (compactUnifiedParserStateCoreClosedFormula tokenTable width tokenCount
      coordinates.start coordinates.finish coordinates.tokensFinish
      coordinates.tasksFinish coordinates.tokensBoundary
      coordinates.tokensCount coordinates.tasksBoundary
      coordinates.tasksCount sizeWitness.tokensBoundarySize
      sizeWitness.tasksBoundarySize).freeVariables = ∅ := by
  unfold compactUnifiedParserStateCoreClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

def compactParserStateAtRowsLtStructuralPayloadPolynomial
    (indexTerm : ValuationTerm) (stateCount : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial compactParserStateAtRowsZeroValuation
    Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm stateCount]

theorem
    compactParserStateAtRowsClosedLtCertificate_structuralPayloadBound_le_public
    (index stateCount : Nat) (hindex : index < stateCount) :
    hybridFormulaStructuralPayloadBound
        (compactParserStateAtRowsClosedLtCertificate index stateCount hindex) <=
      compactParserStateAtRowsLtStructuralPayloadPolynomial
        (shortBinaryNumeralTerm index) stateCount := by
  have hleft : (shortBinaryNumeralTerm index).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (shortBinaryNumeralTerm stateCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    compactParserStateAtRowsZeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm index, shortBinaryNumeralTerm stateCount]
    hleft hright
  simpa only [compactParserStateAtRowsClosedLtCertificate,
    hybridFormulaStructuralPayloadBound,
    compactParserStateAtRowsLtStructuralPayloadPolynomial] using hpublic

theorem
    compactParserStateAtRowsValuationLtCertificate_structuralPayloadBound_le_public
    (indexTerm : ValuationTerm) (stateCount : Nat)
    (hvariables : indexTerm.freeVariables ⊆ {0})
    (hindex : termValue compactParserStateAtRowsZeroValuation indexTerm <
      stateCount) :
    hybridFormulaStructuralPayloadBound
        (compactParserStateAtRowsValuationLtCertificate indexTerm stateCount
          hindex) <=
      compactParserStateAtRowsLtStructuralPayloadPolynomial indexTerm
        stateCount := by
  have hright : (shortBinaryNumeralTerm stateCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    compactParserStateAtRowsZeroValuation Language.ORing.Rel.lt
    ![indexTerm, shortBinaryNumeralTerm stateCount] hvariables hright
  simpa only [compactParserStateAtRowsValuationLtCertificate,
    hybridFormulaStructuralPayloadBound,
    compactParserStateAtRowsLtStructuralPayloadPolynomial] using hpublic

noncomputable def compactUnifiedParserStateAtRowsAtIndexTermPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      coordinates sizeWitness) : Nat := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let indexFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
  let startFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm coordinates.start)
  let finishFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount) nextIndexTerm
    (shortBinaryNumeralTerm coordinates.finish)
  let coreFormula := compactUnifiedParserStateCoreClosedFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  let indexResource := compactParserStateAtRowsLtStructuralPayloadPolynomial
    indexTerm stateCount
  let startResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      compactParserStateAtRowsZeroValuation
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm coordinates.start)
  let finishResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      compactParserStateAtRowsZeroValuation
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) nextIndexTerm
      (shortBinaryNumeralTerm coordinates.finish)
  let coreResource :=
    compactUnifiedParserStateCorePublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates sizeWitness
  let finishCoreResource := transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation finishFormula coreFormula
    finishResource coreResource
  let startTailResource := transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation startFormula
    (finishFormula ⋏ coreFormula) startResource finishCoreResource
  exact transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation indexFormula
    (startFormula ⋏ (finishFormula ⋏ coreFormula)) indexResource
    startTailResource

theorem
    compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      coordinates sizeWitness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness hgraph) <=
      compactUnifiedParserStateAtRowsAtIndexTermPayloadEnvelope tokenTable
        width tokenCount stateBoundary stateCount indexTerm coordinates
        sizeWitness hgraph := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let tableTerm := shortBinaryNumeralTerm stateBoundary
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm coordinates.start
  let finishTerm := shortBinaryNumeralTerm coordinates.finish
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simpa using hindexVariables
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstartTerm : startTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start
  have hfinishTerm : finishTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.finish
  have hstartAtTerms : CompactFixedWidthEntry
      (termValue compactParserStateAtRowsZeroValuation tableTerm)
      (termValue compactParserStateAtRowsZeroValuation widthTerm)
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      (termValue compactParserStateAtRowsZeroValuation startTerm) := by
    simpa only [tableTerm, widthTerm, startTerm,
      termValue_shortBinaryNumeralTerm] using hstart
  have hfinishAtTerms : CompactFixedWidthEntry
      (termValue compactParserStateAtRowsZeroValuation tableTerm)
      (termValue compactParserStateAtRowsZeroValuation widthTerm)
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      (termValue compactParserStateAtRowsZeroValuation finishTerm) := by
    simpa [tableTerm, widthTerm, finishTerm, nextIndexTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hfinish
  let indexCertificate := compactParserStateAtRowsValuationLtCertificate
    indexTerm stateCount hindex
  let startCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      compactParserStateAtRowsZeroValuation tableTerm widthTerm indexTerm
      startTerm hstartAtTerms
  let finishCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      compactParserStateAtRowsZeroValuation tableTerm widthTerm nextIndexTerm
      finishTerm hfinishAtTerms
  let coreCertificate :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph tokenTable
      width tokenCount coordinates sizeWitness hcore
  have hindexResource :=
    compactParserStateAtRowsValuationLtCertificate_structuralPayloadBound_le_public
      indexTerm stateCount hindexVariables hindex
  have hstartResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      compactParserStateAtRowsZeroValuation tableTerm widthTerm indexTerm
      startTerm htable hwidth hindexVariables hstartTerm hstartAtTerms
  have hfinishResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      compactParserStateAtRowsZeroValuation tableTerm widthTerm nextIndexTerm
      finishTerm htable hwidth hnextIndexVariables hfinishTerm hfinishAtTerms
  have hcoreResource :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount coordinates sizeWitness hcore
  let finishCore := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    finishCertificate coreCertificate
  have hfinishCore := transparentHybridConjunctionPayloadBound_le
    finishCertificate coreCertificate _ _ hfinishResource hcoreResource
  let startTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    startCertificate finishCore
  have hstartTail := transparentHybridConjunctionPayloadBound_le
    startCertificate finishCore _ _ hstartResource hfinishCore
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    indexCertificate startTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    indexCertificate startTail _ _ hindexResource hstartTail
  unfold
    compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
  unfold compactUnifiedParserStateAtRowsAtIndexTermPayloadEnvelope
  simp only [hybridFormulaStructuralPayloadBound]
  simpa only [tableTerm, widthTerm, startTerm, finishTerm, nextIndexTerm,
    indexCertificate, startCertificate, finishCertificate, coreCertificate,
    finishCore, startTail, parts, hybridFormulaStructuralPayloadBound] using
    hparts

noncomputable def compactUnifiedParserStateAtRowsPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount index coordinates sizeWitness) : Nat := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let indexTerm := shortBinaryNumeralTerm index
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let indexFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
  let startFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount) indexTerm
    (shortBinaryNumeralTerm coordinates.start)
  let finishFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount) nextIndexTerm
    (shortBinaryNumeralTerm coordinates.finish)
  let coreFormula := compactUnifiedParserStateCoreClosedFormula tokenTable
    width tokenCount coordinates.start coordinates.finish
    coordinates.tokensFinish coordinates.tasksFinish
    coordinates.tokensBoundary coordinates.tokensCount
    coordinates.tasksBoundary coordinates.tasksCount
    sizeWitness.tokensBoundarySize sizeWitness.tasksBoundarySize
  let indexResource := compactParserStateAtRowsLtStructuralPayloadPolynomial
    indexTerm stateCount
  let startResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      compactParserStateAtRowsZeroValuation
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm coordinates.start)
  let finishResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      compactParserStateAtRowsZeroValuation
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) nextIndexTerm
      (shortBinaryNumeralTerm coordinates.finish)
  let coreResource :=
    compactUnifiedParserStateCorePublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates sizeWitness
  let finishCoreResource := transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation finishFormula coreFormula
    finishResource coreResource
  let startTailResource := transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation startFormula
    (finishFormula ⋏ coreFormula) startResource finishCoreResource
  exact transparentHybridConjunctionPayloadEnvelope
    compactParserStateAtRowsZeroValuation indexFormula
    (startFormula ⋏ (finishFormula ⋏ coreFormula)) indexResource
    startTailResource

theorem
    compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount index coordinates sizeWitness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount stateBoundary stateCount index coordinates
          sizeWitness hgraph) <=
      compactUnifiedParserStateAtRowsPayloadEnvelope tokenTable width tokenCount
        stateBoundary stateCount index coordinates sizeWitness hgraph := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let indexTerm := shortBinaryNumeralTerm index
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  let tableTerm := shortBinaryNumeralTerm stateBoundary
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm coordinates.start
  let finishTerm := shortBinaryNumeralTerm coordinates.finish
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simpa using hindexVariables
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstartTerm : startTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start
  have hfinishTerm : finishTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.finish
  have hstartAtTerms : CompactFixedWidthEntry
      (termValue compactParserStateAtRowsZeroValuation tableTerm)
      (termValue compactParserStateAtRowsZeroValuation widthTerm)
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      (termValue compactParserStateAtRowsZeroValuation startTerm) := by
    simpa only [tableTerm, widthTerm, indexTerm, startTerm,
      termValue_shortBinaryNumeralTerm] using hstart
  have hfinishAtTerms : CompactFixedWidthEntry
      (termValue compactParserStateAtRowsZeroValuation tableTerm)
      (termValue compactParserStateAtRowsZeroValuation widthTerm)
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      (termValue compactParserStateAtRowsZeroValuation finishTerm) := by
    simpa [tableTerm, widthTerm, indexTerm, finishTerm, nextIndexTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hfinish
  let indexCertificate := compactParserStateAtRowsClosedLtCertificate index
    stateCount hindex
  let startCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      compactParserStateAtRowsZeroValuation tableTerm widthTerm indexTerm
      startTerm hstartAtTerms
  let finishCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      compactParserStateAtRowsZeroValuation tableTerm widthTerm nextIndexTerm
      finishTerm hfinishAtTerms
  let coreCertificate :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph tokenTable
      width tokenCount coordinates sizeWitness hcore
  have hindexResource :=
    compactParserStateAtRowsClosedLtCertificate_structuralPayloadBound_le_public
      index stateCount hindex
  have hstartResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      compactParserStateAtRowsZeroValuation tableTerm widthTerm indexTerm
      startTerm htable hwidth hindexVariables hstartTerm hstartAtTerms
  have hfinishResource :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      compactParserStateAtRowsZeroValuation tableTerm widthTerm nextIndexTerm
      finishTerm htable hwidth hnextIndexVariables hfinishTerm hfinishAtTerms
  have hcoreResource :=
    compactUnifiedParserStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount coordinates sizeWitness hcore
  let finishCore := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    finishCertificate coreCertificate
  have hfinishCore := transparentHybridConjunctionPayloadBound_le
    finishCertificate coreCertificate _ _ hfinishResource hcoreResource
  let startTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    startCertificate finishCore
  have hstartTail := transparentHybridConjunctionPayloadBound_le
    startCertificate finishCore _ _ hstartResource hfinishCore
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    indexCertificate startTail
  have hparts := transparentHybridConjunctionPayloadBound_le
    indexCertificate startTail _ _ hindexResource hstartTail
  unfold compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph
  unfold compactUnifiedParserStateAtRowsPayloadEnvelope
  simp only [hybridFormulaStructuralPayloadBound]
  simpa only [indexTerm, tableTerm, widthTerm, startTerm, finishTerm,
    nextIndexTerm, indexCertificate, startCertificate, finishCertificate,
    coreCertificate, finishCore, startTail, parts,
    hybridFormulaStructuralPayloadBound] using hparts

#print axioms
  compactParserStateAtRowsClosedLtCertificate_structuralPayloadBound_le_public
#print axioms
  compactParserStateAtRowsValuationLtCertificate_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserStateAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserStateAtRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds
