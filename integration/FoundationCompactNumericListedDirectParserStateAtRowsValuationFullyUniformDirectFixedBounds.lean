import integration.FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds

/-!
# Fully uniform parser-state row bounds at an arbitrary valuation

The existing fixed compiler specializes the valuation to zero.  Finite
universal branches instead evaluate the open row index at an extended
valuation.  This module exposes the same checked atomic, table-entry, and state
core construction with that valuation supplied explicitly.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace FoundationCompactNumericListedDirectParserStateAtRowsValuationFullyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds

private theorem arithmeticAddTerm_eq_func
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem arithmeticAddTerm_freeVariables
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  rw [arithmeticAddTerm_eq_func]
  ext candidate
  simp [LO.FirstOrder.Semiterm.freeVariables_func]

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

noncomputable def compactParserStateAtRowsIndexValuationFullyUniformDirectFixedBound
    (valuation : Nat -> Nat)
    (indexTerm : ValuationTerm) (stateCount numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindex : termValue valuation indexTerm < stateCount)
    (hstateCount : stateCount <= numericBound)
    (hzero : valuation 0 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound valuation
      “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
      (compilePositiveRelationFixedPayloadPolynomial numericBound
        (compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound)) := by
  let args : Fin 2 -> ValuationTerm :=
    ![indexTerm, shortBinaryNumeralTerm stateCount]
  let direct :=
    CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic valuation
      Language.ORing.Rel.lt args (by
        change termValue valuation indexTerm <
          termValue valuation (shortBinaryNumeralTerm stateCount)
        simpa only [termValue_shortBinaryNumeralTerm] using hindex)
  let certificate :=
    CheckedHybridValuationBoundedFormulaCertificate.cast
      (LO.FirstOrder.Semiformula.Operator.lt_def _ _).symm direct
  let proof := certificate.compile
  let termCodeBound :=
    compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hindexTermCode :
      (binaryTermCode indexTerm).length <= termCodeBound := by
    dsimp only [termCodeBound,
      compactParserStateAtRowsUniformTermCodeBound]
    omega
  have hstateCountCode :
      (binaryTermCode
        (shortBinaryNumeralTerm stateCount : ValuationTerm)).length <=
        termCodeBound := by
    have hcode := binaryNumeralTerm_code_length_le_envelope stateCount
      bitBound hstateCountSize
    dsimp only [termCodeBound,
      compactParserStateAtRowsUniformTermCodeBound]
    exact hcode.trans (by omega)
  have hrightVariables :
      (shortBinaryNumeralTerm stateCount : ValuationTerm).freeVariables ⊆
        {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic :
      hybridFormulaStructuralPayloadBound certificate <=
        compilePositiveRelationPayloadPolynomial valuation
          Language.ORing.Rel.lt args := by
    have hraw := compilePositiveRelationPayloadResource_le_publicPolynomial
      valuation Language.ORing.Rel.lt args hindexVariables hrightVariables
    simpa only [certificate, direct, args,
      hybridFormulaStructuralPayloadBound] using hraw
  have hfixed :
      compilePositiveRelationPayloadPolynomial valuation
          Language.ORing.Rel.lt args <=
        compilePositiveRelationFixedPayloadPolynomial numericBound
          termCodeBound := by
    exact compilePositiveRelationPayloadPolynomial_le_fixed valuation
      Language.ORing.Rel.lt args numericBound termCodeBound hindexVariables
      hrightVariables hzero hindexTermCode hstateCountCode
  refine ⟨proof, ?_⟩
  exact (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
    certificate).trans (hpublic.trans hfixed)

noncomputable def compactParserStateAtRowsEntryValuationFullyUniformDirectFixedBound
    (valuation : Nat -> Nat)
    (table width value : Nat) (indexTerm : ValuationTerm)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hentry : CompactFixedWidthEntry table width
      (termValue valuation indexTerm) value)
    (hwidthValue : width <= numericBound)
    (hindexValue : termValue valuation indexTerm <= numericBound)
    (hzero : valuation 0 <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width) indexTerm
        (shortBinaryNumeralTerm value))
      (compactParserStateAtRowsUniformEntryResource indexTerm numericBound
        bitBound) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  have hentryTerms : CompactFixedWidthEntry
      (termValue valuation tableTerm)
      (termValue valuation widthTerm)
      (termValue valuation indexTerm)
      (termValue valuation valueTerm) := by
    simpa only [tableTerm, widthTerm, valueTerm,
      termValue_shortBinaryNumeralTerm] using hentry
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm indexTerm valueTerm hentryTerms
  let proof := certificate.compile
  have hcertificate :
      hybridFormulaStructuralPayloadBound certificate <=
        compactParserStateAtRowsUniformEntryResource indexTerm numericBound
          bitBound := by
    have huniform :=
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation table width value indexTerm numericBound bitBound hwidthValue
        hindexValue hzero htableSize hwidthSize hindexSize hvalueSize
        hindexVariables hentry
    simpa only [certificate, tableTerm, widthTerm, valueTerm,
      compactParserStateAtRowsUniformEntryResource, hentryTerms] using
      huniform
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_hybridFormulaStructuralPayloadBound
      certificate).trans hcertificate

noncomputable def
    compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation indexTerm)
      coordinates sizeWitness)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcoordinatesValue :
      CompactUnifiedParserStateCoordinateValueBound coordinates numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcoordinatesSize :
      CompactUnifiedParserStateCoordinateSizeBound coordinates bitBound)
    (hzero : valuation 0 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount indexTerm coordinates sizeWitness)
      (compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        indexTerm numericBound bitBound) := by
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
  let explicitFormula :=
    indexFormula ⋏ (startFormula ⋏ (finishFormula ⋏ coreFormula))
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsUniformTermCodeBound indexTerm bitBound)
  let startResource := compactParserStateAtRowsUniformStartEntryResource
    indexTerm numericBound bitBound
  let finishResource := compactParserStateAtRowsUniformFinishEntryResource
    indexTerm numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactParserStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      indexTerm numericBound bitBound
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty]
    simpa using hindexVariables
  have hindexValue : termValue valuation indexTerm <= numericBound :=
    (Nat.le_of_lt hindex).trans hstateCount
  have hnextIndexValue :
      termValue valuation nextIndexTerm <= numericBound := by
    have hstep : termValue valuation indexTerm + 1 <= stateCount := by omega
    simpa only [nextIndexTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hstep.trans hstateCount
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize :
      Nat.size (termValue valuation indexTerm) <= bitBound :=
    (Nat.size_le_size hindexValue).trans hnumericSize
  have hnextIndexSize :
      Nat.size (termValue valuation nextIndexTerm) <= bitBound :=
    (Nat.size_le_size hnextIndexValue).trans hnumericSize
  have hstartSize : Nat.size coordinates.start <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (0 : Fin 8)
  have hfinishSize : Nat.size coordinates.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (1 : Fin 8)
  have htokensCount : coordinates.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesValue (5 : Fin 8)
  have htasksCount : coordinates.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesValue (7 : Fin 8)
  have htokensBoundarySize :
      Nat.size coordinates.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (4 : Fin 8)
  have htasksBoundarySize :
      Nat.size coordinates.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcoordinatesSize (6 : Fin 8)
  let indexBound :=
    compactParserStateAtRowsIndexValuationFullyUniformDirectFixedBound valuation
      indexTerm stateCount numericBound bitBound hindexVariables hindex
      hstateCount hzero hnumericSize
  let startBound :=
    compactParserStateAtRowsEntryValuationFullyUniformDirectFixedBound valuation
      stateBoundary tokenCount coordinates.start indexTerm numericBound bitBound
      hindexVariables hstart htokenCount hindexValue hzero hstateBoundarySize
      htokenCountSize hindexSize hstartSize
  have hfinishAtTerm : CompactFixedWidthEntry stateBoundary tokenCount
      (termValue valuation nextIndexTerm) coordinates.finish := by
    simpa only [nextIndexTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hfinish
  let finishBound :=
    compactParserStateAtRowsEntryValuationFullyUniformDirectFixedBound valuation
      stateBoundary tokenCount coordinates.finish nextIndexTerm numericBound
      bitBound hnextIndexVariables hfinishAtTerm htokenCount
      hnextIndexValue hzero hstateBoundarySize htokenCountSize hnextIndexSize
      hfinishSize
  let coreClosedBound :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedBound tokenTable width
      tokenCount coordinates sizeWitness hcore numericBound bitBound hwidth
      htokenCount htokensCount htasksCount htokenTableSize
      htokensBoundarySize htasksBoundarySize hnumericSize
  have hcoreContext :
      (∅ : Finset ValuationFormula) =
        valuationContext coreFormula.freeVariables valuation := by
    dsimp only [coreFormula]
    rw [compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let coreProof := CertifiedPAContextProof.castContext hcoreContext
    coreClosedBound.proof
  let coreBound : ExplicitDirectFormulaBound valuation coreFormula
      coreResource :=
    { proof := coreProof
      payloadLength_le := by
        dsimp only [coreProof]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        exact coreClosedBound.payloadLength_le }
  have hindexFormulaVariables : indexFormula.freeVariables ⊆ {0} := by
    dsimp only [indexFormula]
    rw [LO.FirstOrder.Semiformula.Operator.lt_def]
    intro candidate hcandidate
    rw [LO.FirstOrder.Semiformula.freeVariables_rel] at hcandidate
    rcases Finset.mem_biUnion.mp hcandidate with
      ⟨coordinate, _, hcoordinate⟩
    cases coordinate using Fin.cases with
    | zero => exact hindexVariables hcoordinate
    | succ coordinate =>
        cases coordinate using Fin.cases with
        | zero =>
            change candidate ∈
              (shortBinaryNumeralTerm stateCount :
                ValuationTerm).freeVariables at hcoordinate
            rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  have hstartFormulaVariables : startFormula.freeVariables ⊆ {0} := by
    exact
      compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount) indexTerm
        (shortBinaryNumeralTerm coordinates.start)
        (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hindexVariables
        (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start)
  have hfinishFormulaVariables : finishFormula.freeVariables ⊆ {0} := by
    exact
      compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
        (shortBinaryNumeralTerm stateBoundary)
        (shortBinaryNumeralTerm tokenCount) nextIndexTerm
        (shortBinaryNumeralTerm coordinates.finish)
        (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hnextIndexVariables
        (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.finish)
  have hcoreFormulaVariables : coreFormula.freeVariables ⊆ {0} := by
    dsimp only [coreFormula]
    rw [compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty]
    simp
  let explicitBound :=
    compileDirectFourConjunctionSingletonGeneralBound valuation indexFormula
      startFormula finishFormula coreFormula indexResource startResource
      finishResource coreResource syntaxResource numericBound indexBound
      startBound finishBound coreBound hindexFormulaVariables
      hstartFormulaVariables hfinishFormulaVariables hcoreFormulaVariables
      hzero (by
        unfold syntaxResource
          compactParserStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
        dsimp only [indexResource, startResource, finishResource, coreResource]
        omega)
  have hformula :
      explicitFormula =
        compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
          tokenCount stateBoundary stateCount indexTerm coordinates
          sizeWitness := by
    exact
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula_alignment
        tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness).symm
  let proof := castValuationContextProof hformula explicitBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula
      explicitBound.proof]
  simpa only [
    compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial,
    directFourConjunctionGeneralPayloadEnvelope, syntaxResource,
    indexResource, startResource, finishResource, coreResource] using
    explicitBound.payloadLength_le

#print axioms
  compactParserStateAtRowsIndexValuationFullyUniformDirectFixedBound
#print axioms
  compactParserStateAtRowsEntryValuationFullyUniformDirectFixedBound
#print axioms
  compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound

end FoundationCompactNumericListedDirectParserStateAtRowsValuationFullyUniformDirectFixedBounds
