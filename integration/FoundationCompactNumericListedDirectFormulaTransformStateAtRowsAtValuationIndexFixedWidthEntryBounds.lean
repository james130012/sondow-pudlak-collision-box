import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStateCoreFixedWidthEntryBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformStateCoreFullyUniformDirectFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds

/-!
# Fixed-width entry closure inside one formula-transform state row

This layer replaces the two open-index fixed-width entry resources in a state
row by the complete scale-only endpoint.  The index relation, state core, and
outer connective costs remain explicit for the next quantitative layer.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAClosedHybridContextTransport
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds
open FoundationCompactNumericListedDirectFormulaTransformStateCoreFixedWidthEntryBounds
open FoundationCompactNumericListedDirectFormulaTransformStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula

private theorem arithmeticAddTerm_freeVariables_fixedWidthEntry
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables =
        left.freeVariables ∪ right.freeVariables
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

private theorem arithmeticOneTerm_freeVariables_fixedWidthEntry :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

def compactFormulaTransformStateAtRowsFixedWidthEntryScale
    (valuation : Nat -> Nat)
    (stateBoundary tokenCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  fixedWidthOpenIndexAtomicCoordinateScale valuation
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm coordinates.start) +
    fixedWidthOpenIndexAtomicCoordinateScale valuation
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) nextIndexTerm
      (shortBinaryNumeralTerm coordinates.finish)

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let indexFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
  let startFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount)
    indexTerm (shortBinaryNumeralTerm coordinates.start)
  let finishFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount)
    nextIndexTerm (shortBinaryNumeralTerm coordinates.finish)
  let coreFormula := compactFormulaTransformStateCoreClosedFormula
    tokenTable width tokenCount coordinates sizeWitness
  let scale := compactFormulaTransformStateAtRowsFixedWidthEntryScale valuation
    stateBoundary tokenCount indexTerm coordinates
  let indexResource := valuationLtAtIndexStructuralPayloadPolynomial
    valuation indexTerm stateCount
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let coreResource :=
    compactFormulaTransformStateCorePublicFiniteStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates sizeWitness
  let finishCoreResource := transparentHybridConjunctionPayloadEnvelope
    valuation finishFormula coreFormula entryResource coreResource
  let startTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation startFormula (finishFormula ⋏ coreFormula)
    entryResource finishCoreResource
  transparentHybridConjunctionPayloadEnvelope valuation indexFormula
    (startFormula ⋏ (finishFormula ⋏ coreFormula))
    indexResource startTailResource

theorem
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope_le_fixedWidthEntry
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness <=
      compactFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
          coordinates sizeWitness := by
  let tableTerm := shortBinaryNumeralTerm stateBoundary
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm coordinates.start
  let finishTerm := shortBinaryNumeralTerm coordinates.finish
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let scale := compactFormulaTransformStateAtRowsFixedWidthEntryScale valuation
    stateBoundary tokenCount indexTerm coordinates
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
      arithmeticOneTerm_freeVariables_fixedWidthEntry]
    simpa using hindexVariables
  have htable : tableTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary
  have hwidth : widthTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount
  have hstart : startTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start
  have hfinish : finishTerm.freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.finish
  have hstartScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm startTerm <= scale := by
    dsimp only [scale,
      compactFormulaTransformStateAtRowsFixedWidthEntryScale, tableTerm,
      widthTerm, startTerm, finishTerm, nextIndexTerm]
    omega
  have hfinishScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          nextIndexTerm finishTerm <= scale := by
    dsimp only [scale,
      compactFormulaTransformStateAtRowsFixedWidthEntryScale, tableTerm,
      widthTerm, startTerm, finishTerm, nextIndexTerm]
    omega
  have hstartResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm indexTerm startTerm scale hstartScale
        htable hwidth hindexVariables hstart
  have hfinishResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm nextIndexTerm finishTerm scale hfinishScale
        htable hwidth hnextIndexVariables hfinish
  unfold
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
    compactFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryPayloadEnvelope
  dsimp only [tableTerm, widthTerm, startTerm, finishTerm, nextIndexTerm, scale]
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ hstartResource
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
        hfinishResource le_rfl))

private theorem arithmeticAddTerm_eq_func_fixedCore
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_fixedCore
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_fixedCore]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_fixedCore (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private theorem
    compactFormulaTransformStateCoreClosedFormula_freeVariables_fixedCore
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) :
    (compactFormulaTransformStateCoreClosedFormula
      tokenTable width tokenCount coordinates sizeWitness).freeVariables =
        ∅ := by
  unfold compactFormulaTransformStateCoreClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

def compactFormulaTransformStateCoreCanonicalNumericBound
    (width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) : Nat :=
  width + tokenCount + coordinates.parserTokensCount +
    coordinates.parserTasksCount + coordinates.outputCount

def compactFormulaTransformStateCoreCanonicalBitBound
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactFormulaTransformStateRowCoordinates) : Nat :=
  Nat.size tokenTable +
    Nat.size coordinates.parserTokensBoundary +
    Nat.size coordinates.parserTasksBoundary +
    Nat.size coordinates.outputBoundary +
    Nat.size
      (compactFormulaTransformStateCoreCanonicalNumericBound width tokenCount
        coordinates)

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let indexFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
  let startFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount)
    indexTerm (shortBinaryNumeralTerm coordinates.start)
  let finishFormula := compactFixedWidthEntryAtValuationFormula
    (shortBinaryNumeralTerm stateBoundary)
    (shortBinaryNumeralTerm tokenCount)
    nextIndexTerm (shortBinaryNumeralTerm coordinates.finish)
  let coreFormula := compactFormulaTransformStateCoreClosedFormula
    tokenTable width tokenCount coordinates sizeWitness
  let scale := compactFormulaTransformStateAtRowsFixedWidthEntryScale valuation
    stateBoundary tokenCount indexTerm coordinates
  let indexResource := valuationLtAtIndexStructuralPayloadPolynomial
    valuation indexTerm stateCount
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let coreNumericBound :=
    compactFormulaTransformStateCoreCanonicalNumericBound width tokenCount
      coordinates
  let coreBitBound :=
    compactFormulaTransformStateCoreCanonicalBitBound tokenTable width
      tokenCount coordinates
  let coreResource :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
      coreNumericBound coreBitBound
  let finishCoreResource := transparentHybridConjunctionPayloadEnvelope
    valuation finishFormula coreFormula entryResource coreResource
  let startTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation startFormula (finishFormula ⋏ coreFormula)
    entryResource finishCoreResource
  transparentHybridConjunctionPayloadEnvelope valuation indexFormula
    (startFormula ⋏ (finishFormula ⋏ coreFormula))
    indexResource startTailResource

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraphFixedCore
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) coordinates sizeWitness) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness)
      (compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        indexTerm coordinates sizeWitness) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let tableTerm := shortBinaryNumeralTerm stateBoundary
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm coordinates.start
  let finishTerm := shortBinaryNumeralTerm coordinates.finish
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let scale := compactFormulaTransformStateAtRowsFixedWidthEntryScale valuation
    stateBoundary tokenCount indexTerm coordinates
  let coreNumericBound :=
    compactFormulaTransformStateCoreCanonicalNumericBound width tokenCount
      coordinates
  let coreBitBound :=
    compactFormulaTransformStateCoreCanonicalBitBound tokenTable width
      tokenCount coordinates
  have hcoreWidth : width <= coreNumericBound := by
    dsimp only [coreNumericBound,
      compactFormulaTransformStateCoreCanonicalNumericBound]
    omega
  have hcoreTokenCount : tokenCount <= coreNumericBound := by
    dsimp only [coreNumericBound,
      compactFormulaTransformStateCoreCanonicalNumericBound]
    omega
  have hcoreParserTokens :
      coordinates.parserTokensCount <= coreNumericBound := by
    dsimp only [coreNumericBound,
      compactFormulaTransformStateCoreCanonicalNumericBound]
    omega
  have hcoreParserTasks :
      coordinates.parserTasksCount <= coreNumericBound := by
    dsimp only [coreNumericBound,
      compactFormulaTransformStateCoreCanonicalNumericBound]
    omega
  have hcoreOutput : coordinates.outputCount <= coreNumericBound := by
    dsimp only [coreNumericBound,
      compactFormulaTransformStateCoreCanonicalNumericBound]
    omega
  have hcoreTokenTableSize : Nat.size tokenTable <= coreBitBound := by
    dsimp only [coreBitBound,
      compactFormulaTransformStateCoreCanonicalBitBound]
    omega
  have hcoreParserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= coreBitBound := by
    dsimp only [coreBitBound,
      compactFormulaTransformStateCoreCanonicalBitBound]
    omega
  have hcoreParserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= coreBitBound := by
    dsimp only [coreBitBound,
      compactFormulaTransformStateCoreCanonicalBitBound]
    omega
  have hcoreOutputTableSize :
      Nat.size coordinates.outputBoundary <= coreBitBound := by
    dsimp only [coreBitBound,
      compactFormulaTransformStateCoreCanonicalBitBound]
    omega
  have hcoreNumericSize : Nat.size coreNumericBound <= coreBitBound := by
    dsimp only [coreBitBound, coreNumericBound,
      compactFormulaTransformStateCoreCanonicalBitBound]
    omega
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_fixedWidthEntry,
      arithmeticOneTerm_freeVariables_fixedWidthEntry]
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
      (termValue valuation tableTerm) (termValue valuation widthTerm)
      (termValue valuation indexTerm) (termValue valuation startTerm) := by
    simpa only [tableTerm, widthTerm, startTerm,
      termValue_shortBinaryNumeralTerm] using hstart
  have hfinishAtTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm) (termValue valuation widthTerm)
      (termValue valuation nextIndexTerm)
      (termValue valuation finishTerm) := by
    simpa [tableTerm, widthTerm, finishTerm, nextIndexTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd_fixedCore,
      termValue_arithmeticOne_fixedCore] using hfinish
  have hstartScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          indexTerm startTerm <= scale := by
    dsimp only [scale,
      compactFormulaTransformStateAtRowsFixedWidthEntryScale, tableTerm,
      widthTerm, startTerm, finishTerm, nextIndexTerm]
    omega
  have hfinishScale :
      fixedWidthOpenIndexAtomicCoordinateScale valuation tableTerm widthTerm
          nextIndexTerm finishTerm <= scale := by
    dsimp only [scale,
      compactFormulaTransformStateAtRowsFixedWidthEntryScale, tableTerm,
      widthTerm, startTerm, finishTerm, nextIndexTerm]
    omega
  let indexCertificate := valuationLtAtIndexCertificate
    valuation indexTerm stateCount hindex
  let startCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm indexTerm startTerm hstartAtTerms
  let finishCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm nextIndexTerm finishTerm hfinishAtTerms
  let indexProof := indexCertificate.compile
  let startProof := startCertificate.compile
  let finishProof := finishCertificate.compile
  let coreBound :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedBound tokenTable
      width tokenCount coordinates sizeWitness hcore coreNumericBound
      coreBitBound hcoreWidth hcoreTokenCount hcoreParserTokens
      hcoreParserTasks hcoreOutput hcoreTokenTableSize
      hcoreParserTokensTableSize hcoreParserTasksTableSize
      hcoreOutputTableSize hcoreNumericSize
  let coreClosedProof := coreBound.proof
  have hcoreContext : (∅ : Finset ValuationFormula) =
      valuationContext
        (compactFormulaTransformStateCoreClosedFormula tokenTable width
          tokenCount coordinates sizeWitness).freeVariables valuation := by
    rw [
      compactFormulaTransformStateCoreClosedFormula_freeVariables_fixedCore]
    simp [valuationContext]
  let coreProof := CertifiedPAContextProof.castContext hcoreContext
    coreClosedProof
  let indexResource := valuationLtAtIndexStructuralPayloadPolynomial
    valuation indexTerm stateCount
  let entryResource :=
    compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial scale
  let coreResource :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
      coreNumericBound coreBitBound
  have hindexResource : indexProof.payloadLength <= indexResource :=
    (compile_payloadLength_le_structuralPayloadBound indexCertificate).trans
      (valuationLtAtIndexCertificate_structuralPayloadBound_le_public
        valuation indexTerm stateCount hindexVariables hindex)
  have hstartOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm indexTerm startTerm
      htable hwidth hindexVariables hstartTerm hstartAtTerms
  have hstartFixed :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm indexTerm startTerm scale hstartScale
      htable hwidth hindexVariables hstartTerm
  have hstartResource : startProof.payloadLength <= entryResource :=
    (compile_payloadLength_le_structuralPayloadBound startCertificate).trans
      (hstartOpen.trans hstartFixed)
  have hfinishOpen :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
      valuation tableTerm widthTerm nextIndexTerm finishTerm
      htable hwidth hnextIndexVariables hfinishTerm hfinishAtTerms
  have hfinishFixed :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial_le_fullyFixed
      valuation tableTerm widthTerm nextIndexTerm finishTerm scale
      hfinishScale htable hwidth hnextIndexVariables hfinishTerm
  have hfinishResource : finishProof.payloadLength <= entryResource :=
    (compile_payloadLength_le_structuralPayloadBound finishCertificate).trans
      (hfinishOpen.trans hfinishFixed)
  have hcoreResource : coreProof.payloadLength <= coreResource :=
    by
      dsimp only [coreProof]
      rw [CertifiedPAContextProof.castContext_payloadLength]
      exact coreBound.payloadLength_le
  let finishCoreProof := compileDirectConjunction finishProof coreProof
  have hfinishCore := compileDirectConjunction_payloadLength_le
    finishProof coreProof entryResource coreResource
    hfinishResource hcoreResource
  let startTailProof := compileDirectConjunction startProof finishCoreProof
  have hstartTail := compileDirectConjunction_payloadLength_le
    startProof finishCoreProof entryResource
    (transparentHybridConjunctionPayloadEnvelope valuation
      (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm
        nextIndexTerm finishTerm)
      (compactFormulaTransformStateCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness)
      entryResource coreResource)
    hstartResource hfinishCore
  let explicitProof := compileDirectConjunction indexProof startTailProof
  have hexplicit := compileDirectConjunction_payloadLength_le
    indexProof startTailProof indexResource
    (transparentHybridConjunctionPayloadEnvelope valuation
      (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm
        indexTerm startTerm)
      (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm
          nextIndexTerm finishTerm ⋏
        compactFormulaTransformStateCoreClosedFormula
          tokenTable width tokenCount coordinates sizeWitness)
      entryResource
      (transparentHybridConjunctionPayloadEnvelope valuation
        (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm
          nextIndexTerm finishTerm)
        (compactFormulaTransformStateCoreClosedFormula
          tokenTable width tokenCount coordinates sizeWitness)
        entryResource coreResource))
    hindexResource hstartTail
  have hformula :=
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness).symm
  let proof := castValuationContextProof hformula explicitProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula explicitProof]
  simpa only [
    compactFormulaTransformStateAtRowsAtValuationIndexFixedCorePayloadEnvelope,
    tableTerm, widthTerm, startTerm, finishTerm, nextIndexTerm, scale,
    indexCertificate, startCertificate, finishCertificate,
    coreBound, coreClosedProof, hcoreContext, indexProof, startProof,
    finishProof, coreProof, indexResource, entryResource, coreNumericBound,
    coreBitBound, coreResource,
    finishCoreProof, startTailProof, explicitProof]
    using hexplicit

#print axioms
  compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope_le_fixedWidthEntry
#print axioms
  compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraphFixedCore

end FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryBounds
