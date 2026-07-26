import integration.FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationBound
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexCompiler

/-! # Term-code fixed adjacent parser-syntax step -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds
open FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedValuationBound
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormula
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBase
open FoundationCompactNumericListedDirectParserSyntaxStepAllBranchesClosedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexAlignment

def compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedSyntaxResource
    (termCodeBound tokenCount numericBound bitBound : Nat) : Nat :=
  let stateResource :=
    compactParserStateAtRowsTermCodeFixedPayloadPolynomial termCodeBound
      numericBound bitBound
  let stepResource :=
    syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound
  valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length +
    2 * stateResource + stepResource + 2 * (binaryNatCode 4).length + 1

def compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedPayloadPolynomial
    (termCodeBound tokenCount numericBound bitBound : Nat) : Nat :=
  let stateResource :=
    compactParserStateAtRowsTermCodeFixedPayloadPolynomial termCodeBound
      numericBound bitBound
  let stepResource :=
    syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound
  directThreeConjunctionGeneralPayloadEnvelope
    (compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedSyntaxResource
      termCodeBound tokenCount numericBound bitBound)
    stateResource stateResource stepResource

noncomputable def
    compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedBoundOfGraph
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow)
    (termCodeBound numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hindexCode : (binaryTermCode indexTerm).length <= termCodeBound)
    (hnextIndexCode :
      (binaryTermCode (‘!!indexTerm + 1’ : ValuationTerm)).length <=
        termCodeBound)
    (hnextNextIndexCode :
      (binaryTermCode
        (‘!!(‘!!indexTerm + 1’ : ValuationTerm) + 1’ :
          ValuationTerm)).length <= termCodeBound)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation indexTerm) row)
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
    (hzero : valuation 0 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactParserSyntaxAdjacentStepRowAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount indexTerm row)
      (compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedPayloadPolynomial
        termCodeBound tokenCount numericBound bitBound) := by
  rcases hgraph with ⟨hcurrent, hnext, hstep⟩
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let currentFormula :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
      row.currentSize
  let nextFormula :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
      row.nextSize
  let stepFormula :=
    compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
      row.currentCoordinates row.nextCoordinates row.stepWitness
  let stateResource :=
    compactParserStateAtRowsTermCodeFixedPayloadPolynomial termCodeBound
      numericBound bitBound
  let stepResource :=
    syntaxStepAllBranchesClosedFixedResource tokenCount numericBound bitBound
  let syntaxResource :=
    compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedSyntaxResource
      termCodeBound tokenCount numericBound bitBound
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [parserSyntaxAdjacentIndexAdd_freeVariables,
      parserSyntaxAdjacentIndexOne_freeVariables]
    simpa using hindexVariables
  let currentBound :=
    compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBoundAtValuation
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize termCodeBound numericBound bitBound
      hindexVariables hindexCode hnextIndexCode hcurrent hwidth htokenCount
      hstateCount hcurrentValue htokenTableSize hstateBoundarySize hcurrentSize
      hzero hnumericSize
  have hnextAtTerm : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation nextIndexTerm)
      row.nextCoordinates row.nextSize := by
    simpa only [nextIndexTerm, parserSyntaxAdjacentIndexAdd_termValue,
      parserSyntaxAdjacentIndexOne_termValue] using hnext
  let nextBound :=
    compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBoundAtValuation
      valuation tokenTable width tokenCount stateBoundary stateCount
      nextIndexTerm row.nextCoordinates row.nextSize termCodeBound numericBound
      bitBound hnextIndexVariables hnextIndexCode hnextNextIndexCode hnextAtTerm
      hwidth htokenCount hstateCount hnextValue htokenTableSize
      hstateBoundarySize hnextSize hzero hnumericSize
  let stepClosedBound :=
    compactUnifiedParserSyntaxStepFullyFixedBoundOfGraph tokenTable width
      tokenCount row.currentCoordinates row.nextCoordinates row.stepWitness
      numericBound bitBound hstep hwidth hwidthBit htokenCount hcurrentValue
      hnextValue htokenTableSize hcurrentSize hnextSize hwitnessValue
      hwitnessSize hnumericSize hbitPositive
  let explicitStepFormula :=
    compactUnifiedParserSyntaxStepExplicitFormula tokenTable width tokenCount
      row.currentCoordinates row.nextCoordinates row.stepWitness
  have hstepExplicitContext :
      valuationContext explicitStepFormula.freeVariables
          compactUnifiedParserSyntaxStepZeroValuation = ∅ := by
    dsimp only [explicitStepFormula]
    rw [compactUnifiedParserSyntaxStepExplicitFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let stepExplicitProofEmpty :=
    CertifiedPAContextProof.castContext hstepExplicitContext
      stepClosedBound.proof
  have hstepFormula : explicitStepFormula = stepFormula := by
    dsimp only [explicitStepFormula, stepFormula]
    exact
      (compactUnifiedParserSyntaxStepClosedFormula_alignment tokenTable width
        tokenCount row.currentCoordinates row.nextCoordinates
          row.stepWitness).symm
  let stepClosedProofEmpty :=
    CertifiedPAContextProof.cast hstepFormula stepExplicitProofEmpty
  have hstepContext :
      (∅ : Finset ValuationFormula) =
        valuationContext stepFormula.freeVariables valuation := by
    dsimp only [stepFormula]
    rw [compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty]
    simp [valuationContext]
  let stepProof :=
    CertifiedPAContextProof.castContext hstepContext stepClosedProofEmpty
  let stepBound : ExplicitDirectFormulaBound valuation stepFormula
      stepResource :=
    { proof := stepProof
      payloadLength_le := by
        dsimp only [stepProof, stepClosedProofEmpty, stepExplicitProofEmpty]
        rw [CertifiedPAContextProof.castContext_payloadLength,
          CertifiedPAContextProof.cast_payloadLength,
          CertifiedPAContextProof.castContext_payloadLength]
        exact stepClosedBound.payloadLength_le }
  have hcurrentVariables : currentFormula.freeVariables ⊆ {0} :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize hindexVariables
  have hnextVariables : nextFormula.freeVariables ⊆ {0} :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
      tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
      row.nextCoordinates row.nextSize hnextIndexVariables
  have hstepVariables : stepFormula.freeVariables ⊆ {0} := by
    dsimp only [stepFormula]
    rw [compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty]
    simp
  let explicitBound :=
    compileDirectThreeConjunctionSingletonGeneralBound valuation currentFormula
      nextFormula stepFormula stateResource stateResource stepResource
      syntaxResource numericBound currentBound nextBound stepBound
      hcurrentVariables hnextVariables hstepVariables hzero (by
        unfold syntaxResource
          compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedSyntaxResource
        dsimp only [stateResource, stepResource]
        omega)
  have hformula :
      currentFormula ⋏ (nextFormula ⋏ stepFormula) =
        compactParserSyntaxAdjacentStepRowAtValuationIndexFormula tokenTable
          width tokenCount stateBoundary stateCount indexTerm row :=
    (compactParserSyntaxAdjacentStepRowAtValuationIndexFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount indexTerm row).symm
  let proof := castValuationContextProof hformula explicitBound.proof
  refine ⟨proof, ?_⟩
  rw [show proof.payloadLength = explicitBound.proof.payloadLength by
    exact castValuationContextProof_payloadLength_eq hformula
      explicitBound.proof]
  simpa only [
    compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedPayloadPolynomial,
    syntaxResource, stateResource, stepResource] using
    explicitBound.payloadLength_le

#print axioms
  compactParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexTermCodeFixedBounds
