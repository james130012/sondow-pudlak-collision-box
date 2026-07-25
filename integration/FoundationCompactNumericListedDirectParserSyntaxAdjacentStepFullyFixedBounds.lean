import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBounds

/-! # Closed fixed direct bound for one adjacent parser syntax step -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate

private abbrev adjacentZeroValuation : Nat -> Nat :=
  compactParserStateAtRowsZeroValuation

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

def compactParserSyntaxAdjacentStepCurrentResource
    (index numericBound bitBound : Nat) : Nat :=
  compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
    (shortBinaryNumeralTerm index) numericBound bitBound

def compactParserSyntaxAdjacentStepNextResource
    (index numericBound bitBound : Nat) : Nat :=
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  compactParserStateAtRowsFullyUniformDirectFixedPayloadPolynomial
    nextIndexTerm numericBound bitBound

def compactParserSyntaxAdjacentStepSyntaxResource
    (index tokenCount numericBound bitBound : Nat) : Nat :=
  let currentResource :=
    compactParserSyntaxAdjacentStepCurrentResource index numericBound bitBound
  let nextResource :=
    compactParserSyntaxAdjacentStepNextResource index numericBound bitBound
  let stepResource :=
    syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound
  valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length +
    currentResource + nextResource + stepResource +
    2 * (binaryNatCode 4).length + 1

def compactParserSyntaxAdjacentStepFullyFixedPayloadPolynomial
    (index tokenCount numericBound bitBound : Nat) : Nat :=
  directThreeConjunctionGeneralPayloadEnvelope
    (compactParserSyntaxAdjacentStepSyntaxResource index tokenCount
      numericBound bitBound)
    (compactParserSyntaxAdjacentStepCurrentResource index numericBound bitBound)
    (compactParserSyntaxAdjacentStepNextResource index numericBound bitBound)
    (syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound)

theorem compactParserSyntaxAdjacentStepRowClosedFormula_freeVariables_eq_empty
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) :
    (compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width tokenCount
      stateBoundary stateCount index row).freeVariables = ∅ := by
  unfold compactParserSyntaxAdjacentStepRowClosedFormula
  apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
  intro coordinate
  fin_cases coordinate <;>
    exact shortBinaryNumeralTerm_freeVariables_eq_empty _

noncomputable def compactParserSyntaxAdjacentStepFullyFixedBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount index : Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
      stateBoundary stateCount index row)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound row.currentCoordinates
        numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound row.nextCoordinates
        numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hstateBoundarySize : Nat.size stateBoundary <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound row.currentCoordinates
        bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound row.nextCoordinates
        bitBound)
    (hwitnessValue :
      CompactUnifiedParserSyntaxStepWitnessCoordinateValueBound row.stepWitness
        numericBound)
    (hwitnessSize :
      CompactUnifiedParserSyntaxStepWitnessCoordinateSizeBound row.stepWitness
        bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound adjacentZeroValuation
      (compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width
        tokenCount stateBoundary stateCount index row)
      (compactParserSyntaxAdjacentStepFullyFixedPayloadPolynomial index
        tokenCount numericBound bitBound) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let currentIndexTerm : ValuationTerm := shortBinaryNumeralTerm index
  let nextIndexTerm : ValuationTerm :=
    ‘!!(shortBinaryNumeralTerm index) + 1’
  let currentFormula :=
    compactUnifiedParserStateAtRowsClosedFormula tokenTable width tokenCount
      stateBoundary stateCount index row.currentCoordinates row.currentSize
  let nextFormula :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula :=
    compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
      row.currentCoordinates row.nextCoordinates row.stepWitness
  let currentResource :=
    compactParserSyntaxAdjacentStepCurrentResource index numericBound bitBound
  let nextResource :=
    compactParserSyntaxAdjacentStepNextResource index numericBound bitBound
  let stepResource :=
    syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound
  let syntaxResource :=
    compactParserSyntaxAdjacentStepSyntaxResource index tokenCount numericBound
      bitBound
  have hcurrentIndexVariables : currentIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [currentIndexTerm]
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [arithmeticAddTerm_freeVariables,
      arithmeticOneTerm_freeVariables_eq_empty,
      shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hcurrentAtTerm : CompactUnifiedParserStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue adjacentZeroValuation currentIndexTerm)
      row.currentCoordinates row.currentSize := by
    simpa only [adjacentZeroValuation, currentIndexTerm,
      termValue_shortBinaryNumeralTerm] using hcurrent
  let currentAtTermBound :=
    compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      tokenTable width tokenCount stateBoundary stateCount currentIndexTerm
      row.currentCoordinates row.currentSize numericBound bitBound
      hcurrentIndexVariables hcurrentAtTerm hwidth htokenCount hstateCount
      hcurrentValue htokenTableSize hstateBoundarySize hcurrentSize
      hnumericSize
  have hcurrentFormula :
      compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
          tokenCount stateBoundary stateCount currentIndexTerm
          row.currentCoordinates row.currentSize =
        currentFormula := by
    rfl
  let currentProof := castValuationContextProof hcurrentFormula
    currentAtTermBound.proof
  let currentBound : ExplicitDirectFormulaBound adjacentZeroValuation
      currentFormula currentResource :=
    { proof := currentProof
      payloadLength_le := by
        rw [show currentProof.payloadLength =
            currentAtTermBound.proof.payloadLength by
          exact castValuationContextProof_payloadLength_eq hcurrentFormula
            currentAtTermBound.proof]
        simpa only [currentResource,
          compactParserSyntaxAdjacentStepCurrentResource, currentIndexTerm]
          using currentAtTermBound.payloadLength_le }
  have hnextAtTerm : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount (termValue adjacentZeroValuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa [adjacentZeroValuation, nextIndexTerm,
      termValue_shortBinaryNumeralTerm, termValue_arithmeticAdd,
      termValue_arithmeticOne] using hnext
  let nextBound :=
    compactUnifiedParserStateAtRowsAtValuationIndexFullyUniformDirectFixedBound
      tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
      row.nextCoordinates row.nextSize numericBound bitBound
      hnextIndexVariables hnextAtTerm hwidth htokenCount hstateCount
      hnextValue htokenTableSize hstateBoundarySize hnextSize hnumericSize
  let stepExplicitBound :=
    compactUnifiedParserSyntaxStepFullyFixedBoundOfGraph tokenTable width
      tokenCount row.currentCoordinates row.nextCoordinates row.stepWitness
      numericBound bitBound hstep hwidth hwidthBit htokenCount hcurrentValue
      hnextValue htokenTableSize hcurrentSize hnextSize hwitnessValue
      hwitnessSize hnumericSize hbitPositive
  have hstepFormula :
      compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
          row.currentCoordinates row.nextCoordinates row.stepWitness =
        stepFormula :=
    (compactUnifiedParserSyntaxStepClosedFormula_alignment tokenTable width
      tokenCount row.currentCoordinates row.nextCoordinates
      row.stepWitness).symm
  let stepProof := castValuationContextProof hstepFormula
    stepExplicitBound.proof
  have hstepClosed : stepFormula.freeVariables = ∅ := by
    dsimp only [stepFormula]
    exact compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount row.currentCoordinates row.nextCoordinates
        row.stepWitness
  let stepProofAtAdjacent :
      CertifiedPAContextProof
        (valuationContext stepFormula.freeVariables adjacentZeroValuation)
        stepFormula :=
    CertifiedPAContextProof.castContext (by
      rw [hstepClosed]
      simp [valuationContext]) stepProof
  let stepBound : ExplicitDirectFormulaBound adjacentZeroValuation stepFormula
      stepResource :=
    { proof := stepProofAtAdjacent
      payloadLength_le := by
        rw [show stepProofAtAdjacent.payloadLength =
            stepProof.payloadLength by
          exact CertifiedPAContextProof.castContext_payloadLength _ _]
        rw [show stepProof.payloadLength =
            stepExplicitBound.proof.payloadLength by
          exact castValuationContextProof_payloadLength_eq hstepFormula
            stepExplicitBound.proof]
        exact stepExplicitBound.payloadLength_le }
  have hcurrentVariables : currentFormula.freeVariables ⊆ {0} := by
    rw [← hcurrentFormula]
    exact
      compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
        tokenTable width tokenCount stateBoundary stateCount currentIndexTerm
        row.currentCoordinates row.currentSize hcurrentIndexVariables
  have hnextVariables : nextFormula.freeVariables ⊆ {0} :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
      tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
      row.nextCoordinates row.nextSize hnextIndexVariables
  have hstepVariables : stepFormula.freeVariables ⊆ {0} := by
    dsimp only [stepFormula]
    rw [compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty]
    simp
  let explicitBound :=
    compileDirectThreeConjunctionSingletonGeneralBound adjacentZeroValuation
      currentFormula nextFormula stepFormula currentResource nextResource
      stepResource syntaxResource numericBound currentBound nextBound stepBound
      hcurrentVariables hnextVariables hstepVariables
      (by
        change 0 <= numericBound
        exact Nat.zero_le _)
      (by
        unfold syntaxResource
          compactParserSyntaxAdjacentStepSyntaxResource
        dsimp only [currentResource, nextResource, stepResource]
        omega)
  have hformula :
      currentFormula ⋏ (nextFormula ⋏ stepFormula) =
        compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width
          tokenCount stateBoundary stateCount index row := by
    exact
      (compactParserSyntaxAdjacentStepRowClosedFormula_alignment tokenTable
        width tokenCount stateBoundary stateCount index row).symm
  let proof := castValuationContextProof hformula explicitBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula
      explicitBound.proof]
  simpa only [
    compactParserSyntaxAdjacentStepFullyFixedPayloadPolynomial,
    syntaxResource, currentResource, nextResource, stepResource] using
    explicitBound.payloadLength_le

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFullyFixedBounds
