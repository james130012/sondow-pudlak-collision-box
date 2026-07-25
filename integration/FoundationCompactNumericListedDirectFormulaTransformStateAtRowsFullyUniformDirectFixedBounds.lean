import integration.FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryBounds
import integration.FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fully uniform direct bound for one formula-transform state row

The row-index comparison, the two fixed-width entries, and the closed
seventeen-coordinate state core are all compiled by explicit checked
constructors.  Their complete proof-and-certificate payload is bounded by one
resource depending only on a common numeric bound, a common bit-width bound,
and the fixed syntax of the open row-index term.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAClosedHybridContextTransport
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexAtomicGuardBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexEntryShellFixedBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexUniformCeilingBounds
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectFormulaTransformStateAtRows
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexPublicBounds
open FoundationCompactNumericListedDirectFormulaTransformStateAtRowsAtValuationIndexFixedWidthEntryBounds
open FoundationCompactNumericListedDirectFormulaTransformStateCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateCoreFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula

private theorem arithmeticAddTerm_freeVariables_uniformRow
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

private theorem arithmeticOneTerm_freeVariables_uniformRow :
    (‘1’ : ValuationTerm).freeVariables = ∅ := by
  simp [LO.FirstOrder.Semiterm.Operator.operator,
    LO.FirstOrder.Semiterm.Operator.numeral_one,
    LO.FirstOrder.Semiterm.Operator.One.term_eq]

private theorem arithmeticAddTerm_eq_func_uniformRow
    (left right : ValuationTerm) :
    (‘!!left + !!right’ : ValuationTerm) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd_uniformRow
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func_uniformRow]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne_uniformRow (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

theorem compactFormulaTransformValuationContextFormulaCodeSum_le_singleton
    (valuation : Nat -> Nat) (formula : ValuationFormula)
    (numericBound : Nat)
    (hvariables : formula.freeVariables ⊆ {0})
    (hzero : valuation 0 <= numericBound) :
    formulaCodeSum (valuationContext formula.freeVariables valuation) <=
      valuationContextFormulaCodeSumEnvelope 1 numericBound
        (binaryTermCode (&0 : ValuationTerm)).length := by
  apply valuationContext_formulaCodeSum_le_uniform formula.freeVariables
    valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length
  · exact (Finset.card_le_card hvariables).trans (by simp)
  · intro index hindex
    have hzeroIndex := hvariables hindex
    simp only [Finset.mem_singleton] at hzeroIndex
    subst index
    exact hzero
  · intro index hindex
    have hzeroIndex := hvariables hindex
    simp only [Finset.mem_singleton] at hzeroIndex
    subst index
    exact Nat.le_refl _

theorem
    compactFormulaTransformStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (hindexVariables : indexTerm.freeVariables ⊆ {0}) :
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness).freeVariables ⊆ {0} := by
  unfold compactFormulaTransformStateAtRowsAtValuationIndexFormula
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate <;>
    simp [shortBinaryNumeralTerm_freeVariables_eq_empty, hindexVariables]

def compactFormulaTransformStateAtRowsUniformTermCodeBound
    (indexTerm : ValuationTerm) (bitBound : Nat) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  (binaryTermCode indexTerm).length +
    (binaryTermCode nextIndexTerm).length +
    binaryNumeralTermCodeEnvelope bitBound + 1

def compactFormulaTransformStateAtRowsUniformStartEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate indexTerm
        numericBound bitBound))

def compactFormulaTransformStateAtRowsUniformFinishEntryResource
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  compactFixedWidthEntryAtValuationOpenIndexFullyFixedPayloadPolynomial
    (fixedWidthOpenIndexAtomicUniformCoordinateCeiling
      (fixedWidthOpenIndexShortNumeralAtIndexTermCoordinate nextIndexTerm
        numericBound bitBound))

def compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let contextResource :=
    valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactFormulaTransformStateAtRowsUniformTermCodeBound indexTerm bitBound)
  let startResource :=
    compactFormulaTransformStateAtRowsUniformStartEntryResource indexTerm
      numericBound bitBound
  let finishResource :=
    compactFormulaTransformStateAtRowsUniformFinishEntryResource indexTerm
      numericBound bitBound
  let coreResource :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  contextResource + indexResource + startResource + finishResource +
    coreResource + 3 * (binaryNatCode 4).length + 1

def compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
    (indexTerm : ValuationTerm) (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      indexTerm numericBound bitBound
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound
    (compactFormulaTransformStateAtRowsUniformTermCodeBound indexTerm bitBound)
  let startResource :=
    compactFormulaTransformStateAtRowsUniformStartEntryResource indexTerm
      numericBound bitBound
  let finishResource :=
    compactFormulaTransformStateAtRowsUniformFinishEntryResource indexTerm
      numericBound bitBound
  let coreResource :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let finishCoreResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource finishResource coreResource
  let startTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource startResource finishCoreResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource indexResource
    startTailResource

noncomputable def
    compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) coordinates sizeWitness)
    (hzero : valuation 0 <= numericBound)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hparserTokensCount : coordinates.parserTokensCount <= numericBound)
    (hparserTasksCount : coordinates.parserTasksCount <= numericBound)
    (houtputCount : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hparserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputTableSize : Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactFormulaTransformStateAtRowsAtValuationIndexFormula
        tokenTable width tokenCount stateBoundary stateCount indexTerm
        coordinates sizeWitness)
      (compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        indexTerm numericBound bitBound) := by
  rcases hgraph with ⟨hindex, hstart, hfinish, hcore⟩
  let tableTerm := shortBinaryNumeralTerm stateBoundary
  let widthTerm := shortBinaryNumeralTerm tokenCount
  let startTerm := shortBinaryNumeralTerm coordinates.start
  let finishTerm := shortBinaryNumeralTerm coordinates.finish
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let indexFormula : ValuationFormula :=
    “!!indexTerm < !!(shortBinaryNumeralTerm stateCount)”
  let startFormula := compactFixedWidthEntryAtValuationFormula tableTerm
    widthTerm indexTerm startTerm
  let finishFormula := compactFixedWidthEntryAtValuationFormula tableTerm
    widthTerm nextIndexTerm finishTerm
  let coreFormula := compactFormulaTransformStateCoreClosedFormula tokenTable
    width tokenCount coordinates sizeWitness
  let finishCoreFormula := finishFormula ⋏ coreFormula
  let startTailFormula := startFormula ⋏ finishCoreFormula
  let explicitFormula := indexFormula ⋏ startTailFormula
  let termCodeBound :=
    compactFormulaTransformStateAtRowsUniformTermCodeBound indexTerm bitBound
  let indexResource := compilePositiveRelationFixedPayloadPolynomial
    numericBound termCodeBound
  let startResource :=
    compactFormulaTransformStateAtRowsUniformStartEntryResource indexTerm
      numericBound bitBound
  let finishResource :=
    compactFormulaTransformStateAtRowsUniformFinishEntryResource indexTerm
      numericBound bitBound
  let coreResource :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      indexTerm numericBound bitBound
  let finishCoreResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource finishResource coreResource
  let startTailResource := hybridConjunctionGeneralPayloadEnvelope
    syntaxResource startResource finishCoreResource
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables_uniformRow,
      arithmeticOneTerm_freeVariables_uniformRow]
    simpa using hindexVariables
  have hindexValue : termValue valuation indexTerm <= numericBound :=
    (Nat.le_of_lt hindex).trans hstateCount
  have hnextIndexValue :
      termValue valuation nextIndexTerm <= numericBound := by
    have hstep : termValue valuation indexTerm + 1 <= stateCount := by omega
    simpa only [nextIndexTerm, termValue_arithmeticAdd_uniformRow,
      termValue_arithmeticOne_uniformRow] using hstep.trans hstateCount
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hstateCountSize : Nat.size stateCount <= bitBound :=
    (Nat.size_le_size hstateCount).trans hnumericSize
  have hindexSize : Nat.size (termValue valuation indexTerm) <= bitBound :=
    (Nat.size_le_size hindexValue).trans hnumericSize
  have hnextIndexSize :
      Nat.size (termValue valuation nextIndexTerm) <= bitBound :=
    (Nat.size_le_size hnextIndexValue).trans hnumericSize
  have hstartSize : Nat.size coordinates.start <= bitBound :=
    hstart.1.trans (htokenCount.trans hnumericBit)
  have hfinishSize : Nat.size coordinates.finish <= bitBound :=
    hfinish.1.trans (htokenCount.trans hnumericBit)
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
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd_uniformRow,
      termValue_arithmeticOne_uniformRow] using hfinish
  let indexCertificate := valuationLtAtIndexCertificate valuation indexTerm
    stateCount hindex
  let startCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm indexTerm startTerm hstartAtTerms
  let finishCertificate :=
    compactFixedWidthEntryAtValuationExplicitHybridCertificate valuation
      tableTerm widthTerm nextIndexTerm finishTerm hfinishAtTerms
  let indexProof := indexCertificate.compile
  let startProof := startCertificate.compile
  let finishProof := finishCertificate.compile
  have hindexTermCode :
      (binaryTermCode indexTerm).length <= termCodeBound := by
    unfold termCodeBound
      compactFormulaTransformStateAtRowsUniformTermCodeBound
    dsimp only [nextIndexTerm]
    omega
  have hstateCountCode :
      (binaryTermCode
        (shortBinaryNumeralTerm stateCount : ValuationTerm)).length <=
        termCodeBound := by
    have hcode := binaryNumeralTerm_code_length_le_envelope stateCount
      bitBound hstateCountSize
    unfold termCodeBound
      compactFormulaTransformStateAtRowsUniformTermCodeBound
    dsimp only [nextIndexTerm]
    exact hcode.trans (by omega)
  have hindexPolynomial :
      valuationLtAtIndexStructuralPayloadPolynomial valuation indexTerm
          stateCount <=
        indexResource := by
    have hfixed := compilePositiveRelationPayloadPolynomial_le_fixed
      valuation Language.ORing.Rel.lt
      ![indexTerm, shortBinaryNumeralTerm stateCount] numericBound
      termCodeBound hindexVariables (by
        change
          (shortBinaryNumeralTerm stateCount :
            ValuationTerm).freeVariables ⊆ {0}
        rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
        simp) hzero hindexTermCode hstateCountCode
    simpa only [indexResource,
      valuationLtAtIndexStructuralPayloadPolynomial] using hfixed
  have hindexProof : indexProof.payloadLength <= indexResource :=
    (compile_payloadLength_le_structuralPayloadBound indexCertificate).trans
      ((valuationLtAtIndexCertificate_structuralPayloadBound_le_public
        valuation indexTerm stateCount hindexVariables hindex).trans
        hindexPolynomial)
  have hstartCertificate :
      hybridFormulaStructuralPayloadBound startCertificate <=
        startResource := by
    have huniform :=
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation stateBoundary tokenCount coordinates.start indexTerm
        numericBound bitBound htokenCount hindexValue hzero
        hstateBoundarySize htokenCountSize hindexSize hstartSize
        hindexVariables hstart
    simpa only [startCertificate, tableTerm, widthTerm, startTerm,
      startResource,
      compactFormulaTransformStateAtRowsUniformStartEntryResource,
      hstartAtTerms] using huniform
  have hfinishCertificate :
      hybridFormulaStructuralPayloadBound finishCertificate <=
        finishResource := by
    have huniform :=
      compactFixedWidthEntryAtValuationIndexTermShortNumeralsExplicitHybridCertificate_structuralPayloadBound_le_uniform
        valuation stateBoundary tokenCount coordinates.finish nextIndexTerm
        numericBound bitBound htokenCount hnextIndexValue hzero
        hstateBoundarySize htokenCountSize hnextIndexSize hfinishSize
        hnextIndexVariables (by
          simpa only [nextIndexTerm, termValue_arithmeticAdd_uniformRow,
            termValue_arithmeticOne_uniformRow] using hfinish)
    simpa only [finishCertificate, tableTerm, widthTerm, finishTerm,
      finishResource,
      compactFormulaTransformStateAtRowsUniformFinishEntryResource,
      nextIndexTerm, hfinishAtTerms] using huniform
  have hstartProof : startProof.payloadLength <= startResource :=
    (compile_payloadLength_le_structuralPayloadBound startCertificate).trans
      hstartCertificate
  have hfinishProof : finishProof.payloadLength <= finishResource :=
    (compile_payloadLength_le_structuralPayloadBound finishCertificate).trans
      hfinishCertificate
  let coreBound :=
    compactFormulaTransformStateCoreFullyUniformDirectFixedBound tokenTable
      width tokenCount coordinates sizeWitness hcore numericBound bitBound
      hwidthBound htokenCount hparserTokensCount hparserTasksCount
      houtputCount htokenTableSize hparserTokensTableSize
      hparserTasksTableSize houtputTableSize hnumericSize
  let coreClosedProof := coreBound.proof
  have hcoreContext : (∅ : Finset ValuationFormula) =
      valuationContext coreFormula.freeVariables valuation := by
    dsimp only [coreFormula]
    rw [
      compactFormulaTransformStateCoreClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let coreProof := CertifiedPAContextProof.castContext hcoreContext
    coreClosedProof
  have hcoreProof : coreProof.payloadLength <= coreResource := by
    dsimp only [coreProof]
    rw [CertifiedPAContextProof.castContext_payloadLength]
    exact coreBound.payloadLength_le
  have hindexCode : (binaryFormulaCode indexFormula).length <=
      indexResource := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        indexProof).trans hindexProof
  have hstartCode : (binaryFormulaCode startFormula).length <=
      startResource := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        startProof).trans hstartProof
  have hfinishCode : (binaryFormulaCode finishFormula).length <=
      finishResource := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        finishProof).trans hfinishProof
  have hcoreCode : (binaryFormulaCode coreFormula).length <=
      coreResource := by
    exact
      (CertifiedPAContextProof.conclusionCodeLength_le_payloadLength
        coreProof).trans hcoreProof
  have hfinishCoreCode :
      (binaryFormulaCode finishCoreFormula).length <=
        finishResource + coreResource + (binaryNatCode 4).length := by
    dsimp only [finishCoreFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hstartTailCode :
      (binaryFormulaCode startTailFormula).length <=
        startResource + finishResource + coreResource +
          2 * (binaryNatCode 4).length := by
    dsimp only [startTailFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hexplicitCode :
      (binaryFormulaCode explicitFormula).length <=
        indexResource + startResource + finishResource + coreResource +
          3 * (binaryNatCode 4).length := by
    dsimp only [explicitFormula]
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hindexVariablesFormula : indexFormula.freeVariables ⊆ {0} := by
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
            exact False.elim (by simpa using hcoordinate)
        | succ coordinate => exact Fin.elim0 coordinate
  have hstartVariables : startFormula.freeVariables ⊆ {0} := by
    exact
      compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
        tableTerm widthTerm indexTerm startTerm
        (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hindexVariables
        (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.start)
  have hfinishVariables : finishFormula.freeVariables ⊆ {0} := by
    exact
      compactFixedWidthEntryAtValuationFormula_freeVariables_subset_singleton
        tableTerm widthTerm nextIndexTerm finishTerm
        (shortBinaryNumeralTerm_freeVariables_eq_empty stateBoundary)
        (shortBinaryNumeralTerm_freeVariables_eq_empty tokenCount)
        hnextIndexVariables
        (shortBinaryNumeralTerm_freeVariables_eq_empty coordinates.finish)
  have hcoreVariables : coreFormula.freeVariables ⊆ {0} := by
    dsimp only [coreFormula]
    rw [
      compactFormulaTransformStateCoreClosedFormula_freeVariables_eq_empty]
    simp
  have hfinishCoreVariables : finishCoreFormula.freeVariables ⊆ {0} := by
    dsimp only [finishCoreFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hfinishVariables hcoreVariables
  have hstartTailVariables : startTailFormula.freeVariables ⊆ {0} := by
    dsimp only [startTailFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hstartVariables hfinishCoreVariables
  have hexplicitVariables : explicitFormula.freeVariables ⊆ {0} := by
    dsimp only [explicitFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and]
    exact Finset.union_subset hindexVariablesFormula hstartTailVariables
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource
      compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    dsimp only [termCodeBound, indexResource, startResource, finishResource,
      coreResource]
    omega
  have hcontextFinishCore :
      formulaCodeSum
          (valuationContext finishCoreFormula.freeVariables valuation) <=
        syntaxResource := by
    exact
      (compactFormulaTransformValuationContextFormulaCodeSum_le_singleton
        valuation
        finishCoreFormula numericBound hfinishCoreVariables hzero).trans (by
          unfold syntaxResource
            compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
          dsimp only [termCodeBound, indexResource, startResource,
            finishResource, coreResource]
          omega)
  have hcontextStartTail :
      formulaCodeSum
          (valuationContext startTailFormula.freeVariables valuation) <=
        syntaxResource := by
    exact
      (compactFormulaTransformValuationContextFormulaCodeSum_le_singleton
        valuation
        startTailFormula numericBound hstartTailVariables hzero).trans (by
          unfold syntaxResource
            compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
          dsimp only [termCodeBound, indexResource, startResource,
            finishResource, coreResource]
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
            compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
          dsimp only [termCodeBound, indexResource, startResource,
            finishResource, coreResource]
          omega)
  have hindexSyntax : (binaryFormulaCode indexFormula).length <=
      syntaxResource := hindexCode.trans (by
    unfold syntaxResource
      compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    dsimp only [termCodeBound, indexResource, startResource, finishResource,
      coreResource]
    omega)
  have hstartSyntax : (binaryFormulaCode startFormula).length <=
      syntaxResource := hstartCode.trans (by
    unfold syntaxResource
      compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    dsimp only [termCodeBound, indexResource, startResource, finishResource,
      coreResource]
    omega)
  have hfinishSyntax : (binaryFormulaCode finishFormula).length <=
      syntaxResource := hfinishCode.trans (by
    unfold syntaxResource
      compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    dsimp only [termCodeBound, indexResource, startResource, finishResource,
      coreResource]
    omega)
  have hcoreSyntax : (binaryFormulaCode coreFormula).length <=
      syntaxResource := hcoreCode.trans (by
    unfold syntaxResource
      compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
    dsimp only [termCodeBound, indexResource, startResource, finishResource,
      coreResource]
    omega)
  have hfinishCoreSyntax :
      (binaryFormulaCode finishCoreFormula).length <= syntaxResource :=
    hfinishCoreCode.trans (by
      unfold syntaxResource
        compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      dsimp only [termCodeBound, indexResource, startResource, finishResource,
        coreResource]
      omega)
  have hstartTailSyntax :
      (binaryFormulaCode startTailFormula).length <= syntaxResource :=
    hstartTailCode.trans (by
      unfold syntaxResource
        compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      dsimp only [termCodeBound, indexResource, startResource, finishResource,
        coreResource]
      omega)
  have hexplicitSyntax :
      (binaryFormulaCode explicitFormula).length <= syntaxResource :=
    hexplicitCode.trans (by
      unfold syntaxResource
        compactFormulaTransformStateAtRowsFullyUniformDirectAssemblySyntaxPolynomial
      dsimp only [termCodeBound, indexResource, startResource, finishResource,
        coreResource]
      omega)
  let finishCoreProof := compileDirectConjunction finishProof coreProof
  have hfinishCoreRaw := compileDirectConjunction_payloadLength_le finishProof
    coreProof finishResource coreResource hfinishProof hcoreProof
  have hfinishCoreEnvelope :
      transparentHybridConjunctionPayloadEnvelope valuation finishFormula
          coreFormula finishResource coreResource <=
        finishCoreResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation finishFormula
        coreFormula finishResource coreResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      finishFormula coreFormula finishResource coreResource syntaxResource
      hpositive hcontextFinishCore hfinishSyntax hcoreSyntax
      hfinishCoreSyntax
  have hfinishCoreProof :
      finishCoreProof.payloadLength <= finishCoreResource :=
    hfinishCoreRaw.trans hfinishCoreEnvelope
  let startTailProof := compileDirectConjunction startProof finishCoreProof
  have hstartTailRaw := compileDirectConjunction_payloadLength_le startProof
    finishCoreProof startResource finishCoreResource hstartProof
    hfinishCoreProof
  have hstartTailEnvelope :
      transparentHybridConjunctionPayloadEnvelope valuation startFormula
          finishCoreFormula startResource finishCoreResource <=
        startTailResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation startFormula
        finishCoreFormula startResource finishCoreResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      startFormula finishCoreFormula startResource finishCoreResource
      syntaxResource hpositive hcontextStartTail hstartSyntax
      hfinishCoreSyntax hstartTailSyntax
  have hstartTailProof :
      startTailProof.payloadLength <= startTailResource :=
    hstartTailRaw.trans hstartTailEnvelope
  let explicitProof := compileDirectConjunction indexProof startTailProof
  have hexplicitRaw := compileDirectConjunction_payloadLength_le indexProof
    startTailProof indexResource startTailResource hindexProof
    hstartTailProof
  have hexplicitEnvelope :
      transparentHybridConjunctionPayloadEnvelope valuation indexFormula
          startTailFormula indexResource startTailResource <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource indexResource
          startTailResource := by
    change hybridConjunctionStructuralPayloadEnvelope valuation indexFormula
        startTailFormula indexResource startTailResource <= _
    exact hybridConjunctionStructuralPayloadEnvelope_le_general valuation
      indexFormula startTailFormula indexResource startTailResource
      syntaxResource hpositive hcontextExplicit hindexSyntax hstartTailSyntax
      hexplicitSyntax
  have hexplicitProof :
      explicitProof.payloadLength <=
        hybridConjunctionGeneralPayloadEnvelope syntaxResource indexResource
          startTailResource :=
    hexplicitRaw.trans hexplicitEnvelope
  have hformula : explicitFormula =
      compactFormulaTransformStateAtRowsAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm coordinates
        sizeWitness :=
    (compactFormulaTransformStateAtRowsAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness).symm
  let proof := castValuationContextProof hformula explicitProof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitProof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula explicitProof]
  simpa only [
    compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial,
    syntaxResource, indexResource, startResource, finishResource,
    coreResource, finishCoreResource, startTailResource, termCodeBound]
    using hexplicitProof

noncomputable def
    compileCompactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixed
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) coordinates sizeWitness)
    (hzero : valuation 0 <= numericBound)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hparserTokensCount : coordinates.parserTokensCount <= numericBound)
    (hparserTasksCount : coordinates.parserTasksCount <= numericBound)
    (houtputCount : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hparserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputTableSize : Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound) :=
  (compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
    valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
    coordinates sizeWitness numericBound bitBound hindexVariables hgraph hzero
    hwidthBound htokenCount hstateCount hparserTokensCount hparserTasksCount
    houtputCount htokenTableSize hstateBoundarySize hparserTokensTableSize
    hparserTasksTableSize houtputTableSize hnumericSize hnumericBit).proof

theorem
    compileCompactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixed_payloadLength_le
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (coordinates : CompactFormulaTransformStateRowCoordinates)
    (sizeWitness : CompactFormulaTransformStateCoreSizeWitness)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactFormulaTransformStateAtRows
      tokenTable width tokenCount stateBoundary stateCount
      (termValue valuation indexTerm) coordinates sizeWitness)
    (hzero : valuation 0 <= numericBound)
    (hwidthBound : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hparserTokensCount : coordinates.parserTokensCount <= numericBound)
    (hparserTasksCount : coordinates.parserTasksCount <= numericBound)
    (houtputCount : coordinates.outputCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hparserTokensTableSize :
      Nat.size coordinates.parserTokensBoundary <= bitBound)
    (hparserTasksTableSize :
      Nat.size coordinates.parserTasksBoundary <= bitBound)
    (houtputTableSize : Nat.size coordinates.outputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hnumericBit : numericBound <= bitBound) :
    (compileCompactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixed
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      coordinates sizeWitness numericBound bitBound hindexVariables hgraph
      hzero hwidthBound htokenCount hstateCount hparserTokensCount
      hparserTasksCount houtputCount htokenTableSize hstateBoundarySize
      hparserTokensTableSize hparserTasksTableSize houtputTableSize
      hnumericSize hnumericBit).payloadLength <=
      compactFormulaTransformStateAtRowsFullyUniformDirectFixedPayloadPolynomial
        indexTerm numericBound bitBound :=
  (compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
    valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
    coordinates sizeWitness numericBound bitBound hindexVariables hgraph hzero
    hwidthBound htokenCount hstateCount hparserTokensCount hparserTasksCount
    houtputCount htokenTableSize hstateBoundarySize hparserTokensTableSize
    hparserTasksTableSize houtputTableSize hnumericSize hnumericBit).payloadLength_le

#print axioms
  compactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
#print axioms
  compileCompactFormulaTransformStateAtRowsAtValuationIndexFullyUniformDirectFixed_payloadLength_le

end FoundationCompactNumericListedDirectFormulaTransformStateAtRowsFullyUniformDirectFixedBounds
