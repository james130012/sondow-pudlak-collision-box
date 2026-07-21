import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAClosedHybridContextTransport
import integration.FoundationCompactPADirectConnectiveTransparentBounds
import integration.FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities

/-!
# Direct public bounds for formula-transform state rows

The row index remains an arbitrary valuation term.  The two table lookups and
the closed state core are compiled independently and joined by direct PA
connective constructors.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds

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
open FoundationCompactPAClosedHybridContextTransport
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateCorePublicBounds

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

private theorem compactFormulaTransformStateCoreClosedFormula_freeVariables
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

noncomputable def valuationLtAtIndexCertificate
    (valuation : Nat -> Nat) (indexTerm : ValuationTerm)
    (stateCount : Nat)
    (hindex : termValue valuation indexTerm < stateCount) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)” := by
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
      valuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm stateCount] (by
        change termValue valuation indexTerm <
          termValue valuation (shortBinaryNumeralTerm stateCount)
        simpa only [termValue_shortBinaryNumeralTerm] using hindex)
  exact .cast (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct

def valuationLtAtIndexStructuralPayloadPolynomial
    (valuation : Nat -> Nat) (indexTerm : ValuationTerm)
    (stateCount : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial valuation
    Language.ORing.Rel.lt ![indexTerm, shortBinaryNumeralTerm stateCount]

theorem valuationLtAtIndexCertificate_structuralPayloadBound_le_public
    (valuation : Nat -> Nat) (indexTerm : ValuationTerm)
    (stateCount : Nat)
    (hvariables : indexTerm.freeVariables ⊆ {0})
    (hindex : termValue valuation indexTerm < stateCount) :
    hybridFormulaStructuralPayloadBound
        (valuationLtAtIndexCertificate
          valuation indexTerm stateCount hindex) ≤
      valuationLtAtIndexStructuralPayloadPolynomial
        valuation indexTerm stateCount := by
  have hright : (shortBinaryNumeralTerm stateCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    valuation Language.ORing.Rel.lt
    ![indexTerm, shortBinaryNumeralTerm stateCount]
    hvariables hright
  simpa only [valuationLtAtIndexCertificate,
    hybridFormulaStructuralPayloadBound,
    valuationLtAtIndexStructuralPayloadPolynomial] using hpublic

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) coordinates sizeWitness) : Nat := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
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
  let indexResource := valuationLtAtIndexStructuralPayloadPolynomial
    valuation indexTerm stateCount
  let startResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm coordinates.start)
  let finishResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) nextIndexTerm
      (shortBinaryNumeralTerm coordinates.finish)
  let coreResource :=
    compactFormulaTransformStateCoreGraphStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates sizeWitness hcore
  let finishCoreResource := transparentHybridConjunctionPayloadEnvelope
    valuation finishFormula coreFormula finishResource coreResource
  let startTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation startFormula (finishFormula ⋏ coreFormula)
    startResource finishCoreResource
  exact transparentHybridConjunctionPayloadEnvelope valuation indexFormula
    (startFormula ⋏ (finishFormula ⋏ coreFormula))
    indexResource startTailResource

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraph
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
      (compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope
        valuation tokenTable width tokenCount stateBoundary stateCount
        indexTerm coordinates sizeWitness hgraph) := by
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
      (termValue valuation tableTerm) (termValue valuation widthTerm)
      (termValue valuation indexTerm) (termValue valuation startTerm) := by
    simpa only [tableTerm, widthTerm, startTerm,
      termValue_shortBinaryNumeralTerm] using hstart
  have hfinishAtTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm) (termValue valuation widthTerm)
      (termValue valuation nextIndexTerm)
      (termValue valuation finishTerm) := by
    simpa [tableTerm, widthTerm, finishTerm, nextIndexTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hfinish
  let indexCertificate := valuationLtAtIndexCertificate
    valuation indexTerm stateCount hindex
  let startCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm indexTerm startTerm hstartAtTerms
  let finishCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm nextIndexTerm finishTerm hfinishAtTerms
  let coreCertificate :=
    compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph
      tokenTable width tokenCount coordinates sizeWitness hcore
  let indexProof := indexCertificate.compile
  let startProof := startCertificate.compile
  let finishProof := finishCertificate.compile
  let coreProof := compileClosedHybridAtValuation
    (target := valuation) coreCertificate
    (compactFormulaTransformStateCoreClosedFormula_freeVariables
      tokenTable width tokenCount coordinates sizeWitness)
  let indexResource := valuationLtAtIndexStructuralPayloadPolynomial
    valuation indexTerm stateCount
  let startResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm indexTerm startTerm
  let finishResource :=
    compactFixedWidthEntryAtValuationOpenIndexStructuralPayloadPolynomial
      valuation tableTerm widthTerm nextIndexTerm finishTerm
  let coreResource :=
    compactFormulaTransformStateCoreGraphStructuralPayloadEnvelope
      tokenTable width tokenCount coordinates sizeWitness hcore
  have hindexResource : indexProof.payloadLength ≤ indexResource :=
    (compile_payloadLength_le_structuralPayloadBound indexCertificate).trans
      (valuationLtAtIndexCertificate_structuralPayloadBound_le_public
        valuation indexTerm stateCount hindexVariables hindex)
  have hstartResource : startProof.payloadLength ≤ startResource :=
    (compile_payloadLength_le_structuralPayloadBound startCertificate).trans
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        valuation tableTerm widthTerm indexTerm startTerm
        htable hwidth hindexVariables hstartTerm hstartAtTerms)
  have hfinishResource : finishProof.payloadLength ≤ finishResource :=
    (compile_payloadLength_le_structuralPayloadBound finishCertificate).trans
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate_structuralPayloadBound_le_openIndexPolynomial
        valuation tableTerm widthTerm nextIndexTerm finishTerm
        htable hwidth hnextIndexVariables hfinishTerm hfinishAtTerms)
  have hcoreRaw := compileClosedHybridAtValuation_payloadLength_le_structural
    (target := valuation) coreCertificate
    (compactFormulaTransformStateCoreClosedFormula_freeVariables
      tokenTable width tokenCount coordinates sizeWitness)
  have hcoreResource : coreProof.payloadLength ≤ coreResource :=
    hcoreRaw.trans
      (compactFormulaTransformStateCoreExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
        tokenTable width tokenCount coordinates sizeWitness hcore)
  let finishCoreProof := compileDirectConjunction finishProof coreProof
  have hfinishCore := compileDirectConjunction_payloadLength_le
    finishProof coreProof finishResource coreResource
    hfinishResource hcoreResource
  let startTailProof := compileDirectConjunction startProof finishCoreProof
  have hstartTail := compileDirectConjunction_payloadLength_le
    startProof finishCoreProof startResource
    (transparentHybridConjunctionPayloadEnvelope valuation
      (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm
        nextIndexTerm finishTerm)
      (compactFormulaTransformStateCoreClosedFormula
        tokenTable width tokenCount coordinates sizeWitness)
      finishResource coreResource)
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
      startResource
      (transparentHybridConjunctionPayloadEnvelope valuation
        (compactFixedWidthEntryAtValuationFormula tableTerm widthTerm
          nextIndexTerm finishTerm)
        (compactFormulaTransformStateCoreClosedFormula
          tokenTable width tokenCount coordinates sizeWitness)
        finishResource coreResource))
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
    compactFormulaTransformStateAtRowsAtValuationIndexDirectPayloadEnvelope,
    tableTerm, widthTerm, startTerm, finishTerm, nextIndexTerm,
    indexCertificate, startCertificate, finishCertificate,
    coreCertificate, indexProof, startProof, finishProof, coreProof,
    indexResource, startResource, finishResource, coreResource,
    finishCoreProof, startTailProof, explicitProof]
    using hexplicit

#print axioms
  valuationLtAtIndexCertificate_structuralPayloadBound_le_public
#print axioms
  compactFormulaTransformStateAtRowsAtValuationIndexExplicitDirectOfGraph

end FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds
