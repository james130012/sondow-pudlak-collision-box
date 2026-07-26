import integration.FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationLeaves

/-! # Term-code fixed parser-state row at an arbitrary valuation -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds
open FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationLeaves
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds

private theorem arithmeticAddTerm_freeVariables_termCodeValuationRow
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm).freeVariables =
      left.freeVariables ∪ right.freeVariables := by
  change
    (LO.FirstOrder.Semiterm.func Language.Add.add
      ![left, right]).freeVariables = left.freeVariables ∪ right.freeVariables
  ext candidate
  simp [LO.FirstOrder.Semiterm.freeVariables_func]

private theorem arithmeticOneTerm_freeVariables_termCodeValuationRow :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem termValue_arithmeticAdd_termCodeValuationRow
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [show (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] by
    simp [Semiterm.Operator.operator, Semiterm.Operator.Add.term_eq,
      Rew.func, Matrix.fun_eq_vec_two]]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_termCodeValuationRow
    (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

noncomputable def
    compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBoundAtValuation
    (valuation : Nat -> Nat)
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
    rw [arithmeticAddTerm_freeVariables_termCodeValuationRow,
      arithmeticOneTerm_freeVariables_termCodeValuationRow]
    simpa using hindexVariables
  have hindexValue : termValue valuation indexTerm <= numericBound :=
    (Nat.le_of_lt hindex).trans hstateCount
  have hnextIndexValue :
      termValue valuation nextIndexTerm <= numericBound := by
    have hstep : termValue valuation indexTerm + 1 <= stateCount := by omega
    simpa only [nextIndexTerm, termValue_arithmeticAdd_termCodeValuationRow,
      termValue_arithmeticOne_termCodeValuationRow] using
      hstep.trans hstateCount
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound :=
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
    compactParserStateAtRowsIndexTermCodeFixedBoundAtValuation valuation
      indexTerm stateCount termCodeBound numericBound bitBound hindexVariables
      hindexCode hindex hstateCount hzero hnumericSize
  let startBound :=
    compactParserStateAtRowsEntryTermCodeFixedBoundAtValuation valuation
      stateBoundary tokenCount coordinates.start indexTerm termCodeBound
      numericBound bitBound hindexVariables hindexCode hstart htokenCount
      hindexValue hzero hstateBoundarySize htokenCountSize hindexSize
      hstartSize
  have hfinishAtTerm : CompactFixedWidthEntry stateBoundary tokenCount
      (termValue valuation nextIndexTerm) coordinates.finish := by
    simpa only [nextIndexTerm, termValue_arithmeticAdd_termCodeValuationRow,
      termValue_arithmeticOne_termCodeValuationRow] using hfinish
  let finishBound :=
    compactParserStateAtRowsEntryTermCodeFixedBoundAtValuation valuation
      stateBoundary tokenCount coordinates.finish nextIndexTerm termCodeBound
      numericBound bitBound hnextIndexVariables hnextIndexCode hfinishAtTerm
      htokenCount hnextIndexValue hzero hstateBoundarySize htokenCountSize
      hnextIndexSize hfinishSize
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
    compileDirectFourConjunctionSingletonGeneralBound valuation indexFormula
      startFormula finishFormula coreFormula indexResource entryResource
      entryResource coreResource syntaxResource numericBound indexBound
      startBound finishBound coreBound hindexFormulaVariables
      hstartFormulaVariables hfinishFormulaVariables hcoreFormulaVariables
      hzero (by
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

#print axioms
  compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBoundAtValuation

end FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationBound
