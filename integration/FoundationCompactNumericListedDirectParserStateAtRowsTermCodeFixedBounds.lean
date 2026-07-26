import integration.FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds

/-! # Term-code fixed direct bound for one parser-state row -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTermCodeBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds

private theorem arithmeticAddTerm_freeVariables_termCodeRow
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables = left.freeVariables ∪ right.freeVariables
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

private theorem arithmeticOneTerm_freeVariables_termCodeRow :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd_termCodeRow
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [show (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] by
    simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
      Rew.func, Matrix.fun_eq_vec_two]]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_termCodeRow (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

def compactParserStateAtRowsTermCodeFixedRelationTermBound
    (termCodeBound bitBound : Nat) : Nat :=
  termCodeBound + binaryNumeralTermCodeEnvelope bitBound + 1

def compactParserStateAtRowsTermCodeFixedEntryResource
    (termCodeBound numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexShortNumeralAtTermCodeBoundScale termCodeBound
      numericBound bitBound)

def compactParserStateAtRowsTermCodeFixedAssemblySyntaxPolynomial
    (termCodeBound numericBound bitBound : Nat) : Nat :=
  let contextResource :=
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound
      bitBound)
  let entryResource := compactParserStateAtRowsTermCodeFixedEntryResource
    termCodeBound numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  contextResource + indexResource + 2 * entryResource + coreResource +
    3 * (binaryNatCode 4).length + 1

def compactParserStateAtRowsTermCodeFixedPayloadPolynomial
    (termCodeBound numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactParserStateAtRowsTermCodeFixedAssemblySyntaxPolynomial termCodeBound
      numericBound bitBound
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound
      bitBound)
  let entryResource := compactParserStateAtRowsTermCodeFixedEntryResource
    termCodeBound numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  directFourConjunctionGeneralPayloadEnvelope syntaxResource indexResource
    entryResource entryResource coreResource

noncomputable def compactParserStateAtRowsIndexTermCodeFixedBound
    (indexTerm : ValuationTerm) (stateCount termCodeBound numericBound
      bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hindex :
      termValue compactParserStateAtRowsZeroValuation indexTerm < stateCount)
    (hstateCount : stateCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound compactParserStateAtRowsZeroValuation
      “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
      (compilePositiveRelationFixedPayloadPolynomial numericBound
        (compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound
          bitBound)) := by
  let relationTermBound :=
    compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound bitBound
  let certificate :=
    compactParserStateAtRowsValuationLtCertificate indexTerm stateCount hindex
  let proof := certificate.compile
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hindexCode' : (binaryTermCode indexTerm).length <= relationTermBound :=
    hindexCode.trans (by
      unfold relationTermBound
        compactParserStateAtRowsTermCodeFixedRelationTermBound
      omega)
  have hstateCountCode :
      (binaryTermCode
        (shortBinaryNumeralTerm stateCount : ValuationTerm)).length <=
        relationTermBound := by
    have hcode := binaryNumeralTerm_code_length_le_envelope stateCount bitBound
      hstateCountSize
    exact hcode.trans (by
      unfold relationTermBound
        compactParserStateAtRowsTermCodeFixedRelationTermBound
      omega)
  have hpolynomial :
      compactParserStateAtRowsLtStructuralPayloadPolynomial indexTerm
          stateCount <=
        compilePositiveRelationFixedPayloadPolynomial numericBound
          relationTermBound := by
    have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
      compactParserStateAtRowsZeroValuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm stateCount] numericBound
      relationTermBound hindexVariables (by
        change
          (shortBinaryNumeralTerm stateCount : ValuationTerm).freeVariables ⊆
            {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp) (by simp [compactParserStateAtRowsZeroValuation])
      hindexCode' hstateCountCode
    simpa only [compactParserStateAtRowsLtStructuralPayloadPolynomial] using
      hfixed
  refine ⟨proof, ?_⟩
  exact
    (compile_payloadLength_le_structuralPayloadBound certificate).trans
      ((compactParserStateAtRowsValuationLtCertificate_structuralPayloadBound_le_public
        indexTerm stateCount hindexVariables hindex).trans hpolynomial)

noncomputable def compactParserStateAtRowsEntryTermCodeFixedBound
    (table width value : Nat) (indexTerm : ValuationTerm)
    (termCodeBound numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hentry : CompactFixedWidthEntry table width
      (termValue compactParserStateAtRowsZeroValuation indexTerm) value)
    (hwidthValue : width <= numericBound)
    (hindexValue :
      termValue compactParserStateAtRowsZeroValuation indexTerm <= numericBound)
    (htableSize : Nat.size table <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hindexSize :
      Nat.size (termValue compactParserStateAtRowsZeroValuation indexTerm) <=
        bitBound)
    (hvalueSize : Nat.size value <= bitBound) :
    ExplicitDirectFormulaBound compactParserStateAtRowsZeroValuation
      (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm table) (shortBinaryNumeralTerm width) indexTerm
        (shortBinaryNumeralTerm value))
      (compactParserStateAtRowsTermCodeFixedEntryResource termCodeBound
        numericBound bitBound) := by
  let tableTerm := shortBinaryNumeralTerm table
  let widthTerm := shortBinaryNumeralTerm width
  let valueTerm := shortBinaryNumeralTerm value
  have hentryTerms : CompactFixedWidthEntry
      (termValue compactParserStateAtRowsZeroValuation tableTerm)
      (termValue compactParserStateAtRowsZeroValuation widthTerm)
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
      (termValue compactParserStateAtRowsZeroValuation valueTerm) := by
    simpa only [tableTerm, widthTerm, valueTerm,
      termValue_shortBinaryNumeralTerm] using hentry
  let certificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate
      compactParserStateAtRowsZeroValuation tableTerm widthTerm indexTerm
      valueTerm hentryTerms
  let proof := certificate.compile
  have hcertificate :
      hybridFormulaStructuralPayloadBound certificate <=
        compactParserStateAtRowsTermCodeFixedEntryResource termCodeBound
          numericBound bitBound := by
    have huniform :=
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_termCodeBound
        compactParserStateAtRowsZeroValuation table width value indexTerm
        termCodeBound numericBound bitBound hwidthValue hindexValue
        (by simp [compactParserStateAtRowsZeroValuation]) htableSize hwidthSize
        hindexSize hvalueSize hindexCode hindexVariables hentry
    simpa only [certificate, tableTerm, widthTerm, valueTerm, hentryTerms,
      compactParserStateAtRowsTermCodeFixedEntryResource] using huniform
  refine ⟨proof, ?_⟩
  exact (compile_payloadLength_le_structuralPayloadBound certificate).trans
    hcertificate

noncomputable def
    compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (termCodeBound numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hnextIndexCode :
      (binaryTermCode (‘!!indexTerm + 1’ : ValuationTerm)).length <=
        termCodeBound)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
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
    (hnumericSize : Nat.size numericBound <= bitBound) :
    ExplicitDirectFormulaBound compactParserStateAtRowsZeroValuation
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount indexTerm coordinates sizeWitness)
      (compactParserStateAtRowsTermCodeFixedPayloadPolynomial termCodeBound
        numericBound bitBound) := by
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
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactParserStateAtRowsTermCodeFixedRelationTermBound termCodeBound
      bitBound)
  let entryResource := compactParserStateAtRowsTermCodeFixedEntryResource
    termCodeBound numericBound bitBound
  let coreResource :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactParserStateAtRowsTermCodeFixedAssemblySyntaxPolynomial termCodeBound
      numericBound bitBound
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_termCodeRow,
      arithmeticOneTerm_freeVariables_termCodeRow]
    simpa using hindexVariables
  have hindexValue :
      termValue compactParserStateAtRowsZeroValuation indexTerm <= numericBound :=
    (Nat.le_of_lt hindex).trans hstateCount
  have hnextIndexValue :
      termValue compactParserStateAtRowsZeroValuation nextIndexTerm <=
        numericBound := by
    have hstep :
        termValue compactParserStateAtRowsZeroValuation indexTerm + 1 <=
          stateCount := by omega
    simpa only [nextIndexTerm, termValue_arithmeticAdd_termCodeRow,
      termValue_arithmeticOne_termCodeRow] using hstep.trans hstateCount
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize :
      Nat.size (termValue compactParserStateAtRowsZeroValuation indexTerm) <=
        bitBound :=
    (Nat.size_le_size hindexValue).trans hnumericSize
  have hnextIndexSize :
      Nat.size (termValue compactParserStateAtRowsZeroValuation nextIndexTerm) <=
        bitBound :=
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
  let indexBound := compactParserStateAtRowsIndexTermCodeFixedBound indexTerm
    stateCount termCodeBound numericBound bitBound hindexVariables hindexCode
    hindex hstateCount hnumericSize
  let startBound := compactParserStateAtRowsEntryTermCodeFixedBound stateBoundary
    tokenCount coordinates.start indexTerm termCodeBound numericBound bitBound
    hindexVariables hindexCode hstart htokenCount hindexValue
    hstateBoundarySize htokenCountSize hindexSize hstartSize
  have hfinishAtTerm : CompactFixedWidthEntry stateBoundary tokenCount
      (termValue compactParserStateAtRowsZeroValuation nextIndexTerm)
      coordinates.finish := by
    simpa only [nextIndexTerm, termValue_arithmeticAdd_termCodeRow,
      termValue_arithmeticOne_termCodeRow] using hfinish
  let finishBound := compactParserStateAtRowsEntryTermCodeFixedBound
    stateBoundary tokenCount coordinates.finish nextIndexTerm termCodeBound
    numericBound bitBound hnextIndexVariables hnextIndexCode hfinishAtTerm
    htokenCount hnextIndexValue hstateBoundarySize htokenCountSize
    hnextIndexSize hfinishSize
  let coreClosedBound :=
    compactUnifiedParserStateCoreFullyUniformDirectFixedBound tokenTable width
      tokenCount coordinates sizeWitness hcore numericBound bitBound hwidth
      htokenCount htokensCount htasksCount htokenTableSize
      htokensBoundarySize htasksBoundarySize hnumericSize
  have hcoreContext :
      (∅ : Finset ValuationFormula) =
        valuationContext coreFormula.freeVariables
          compactParserStateAtRowsZeroValuation := by
    dsimp only [coreFormula]
    rw [compactUnifiedParserStateCoreClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let coreProof := CertifiedPAContextProof.castContext hcoreContext
    coreClosedBound.proof
  let coreBound : ExplicitDirectFormulaBound
      compactParserStateAtRowsZeroValuation coreFormula coreResource :=
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
              (shortBinaryNumeralTerm stateCount : ValuationTerm).freeVariables
              at hcoordinate
            rw [shortBinaryNumeralTerm_freeVariables_eq_empty] at hcoordinate
            simp at hcoordinate
        | succ coordinate => exact Fin.elim0 coordinate
  have hstartFormulaVariables : startFormula.freeVariables ⊆ {0} :=
    compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
      (shortBinaryNumeralTerm stateBoundary)
      (shortBinaryNumeralTerm tokenCount) indexTerm
      (shortBinaryNumeralTerm coordinates.start)
      (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
      (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
      hindexVariables
      (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start)
  have hfinishFormulaVariables : finishFormula.freeVariables ⊆ {0} :=
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
    compileDirectFourConjunctionSingletonGeneralBound
      compactParserStateAtRowsZeroValuation indexFormula startFormula
      finishFormula coreFormula indexResource entryResource entryResource
      coreResource syntaxResource numericBound indexBound startBound finishBound
      coreBound hindexFormulaVariables hstartFormulaVariables
      hfinishFormulaVariables hcoreFormulaVariables
      (by simp [compactParserStateAtRowsZeroValuation])
      (by
        unfold syntaxResource
          compactParserStateAtRowsTermCodeFixedAssemblySyntaxPolynomial
        dsimp only [indexResource, entryResource, coreResource]
        omega)
  have hformula :
      indexFormula ⋏ (startFormula ⋏ (finishFormula ⋏ coreFormula)) =
        compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
          tokenCount stateBoundary stateCount indexTerm coordinates
          sizeWitness :=
    (compactUnifiedParserStateAtRowsAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness).symm
  let proof := castValuationContextProof hformula explicitBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula
      explicitBound.proof]
  simpa only [compactParserStateAtRowsTermCodeFixedPayloadPolynomial,
    indexResource, entryResource, coreResource, syntaxResource] using
    explicitBound.payloadLength_le

end FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds
