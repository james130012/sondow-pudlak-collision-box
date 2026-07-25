import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexCompiler
import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds

/-! # Fixed adjacent-row terminal at an arbitrary valuation index -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerFixedArities
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxStepFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexAlignment
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepAtValuationIndexCompiler
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

def compactParserSyntaxAdjacentRowTerminalAtValuationIndexFormula
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  compactParserSyntaxAdjacentStepRowAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row ⋏
    (compactParserSyntaxAdjacentRowCurrentStatusFormula tokenTable width
        tokenCount valueBound row ⋏
      compactParserSyntaxAdjacentRowNextStatusFormula tokenTable width
        tokenCount valueBound row)

def compactParserSyntaxAdjacentRowTerminalAtValuationIndexSyntaxResource
    (indexTerm : ValuationTerm)
    (tokenCount numericBound bitBound : Nat) : Nat :=
  let adjacentResource :=
    compactParserSyntaxAdjacentStepAtValuationIndexFullyFixedPayloadPolynomial
      indexTerm tokenCount numericBound bitBound
  let statusResource :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length +
    adjacentResource + statusResource + statusResource +
    2 * (binaryNatCode 4).length + 1

def compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedPayloadPolynomial
    (indexTerm : ValuationTerm)
    (tokenCount numericBound bitBound : Nat) : Nat :=
  directThreeConjunctionGeneralPayloadEnvelope
    (compactParserSyntaxAdjacentRowTerminalAtValuationIndexSyntaxResource
      indexTerm tokenCount numericBound bitBound)
    (compactParserSyntaxAdjacentStepAtValuationIndexFullyFixedPayloadPolynomial
      indexTerm tokenCount numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)

noncomputable def
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBound
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount valueBound : Nat)
    (indexTerm : ValuationTerm)
    (row : CompactParserSyntaxAdjacentStepRow)
    (numericBound bitBound : Nat)
    (hindexVariables : indexTerm.freeVariables ⊆ {0})
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
      stateBoundary stateCount (termValue valuation indexTerm) row)
    (hcurrentStatus : CompactBinaryNatStatusValidBounded tokenTable width
      tokenCount row.currentCoordinates.tasksFinish
      row.currentCoordinates.finish valueBound)
    (hnextStatus : CompactBinaryNatStatusValidBounded tokenTable width
      tokenCount row.nextCoordinates.tasksFinish row.nextCoordinates.finish
      valueBound)
    (hvalueBound : valueBound <= numericBound)
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
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (hareaBit : (tokenCount + 1) * tokenCount <= bitBound)
    (hzero : valuation 0 <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound valuation
      (compactParserSyntaxAdjacentRowTerminalAtValuationIndexFormula tokenTable
        width tokenCount stateBoundary stateCount valueBound indexTerm row)
      (compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedPayloadPolynomial
        indexTerm tokenCount numericBound bitBound) := by
  let adjacentFormula :=
    compactParserSyntaxAdjacentStepRowAtValuationIndexFormula tokenTable width
      tokenCount stateBoundary stateCount indexTerm row
  let currentStatusFormula :=
    compactParserSyntaxAdjacentRowCurrentStatusFormula tokenTable width
      tokenCount valueBound row
  let nextStatusFormula :=
    compactParserSyntaxAdjacentRowNextStatusFormula tokenTable width tokenCount
      valueBound row
  let adjacentResource :=
    compactParserSyntaxAdjacentStepAtValuationIndexFullyFixedPayloadPolynomial
      indexTerm tokenCount numericBound bitBound
  let statusResource :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexSyntaxResource
      indexTerm tokenCount numericBound bitBound
  let adjacentBound :=
    compactParserSyntaxAdjacentStepAtValuationIndexFullyFixedBoundOfGraph
      valuation tokenTable width tokenCount stateBoundary stateCount indexTerm
      row numericBound bitBound hindexVariables hgraph hwidth hwidthBit
      htokenCount hstateCount hcurrentValue hnextValue htokenTableSize
      hstateBoundarySize hcurrentSize hnextSize hwitnessValue hwitnessSize hzero
      hnumericSize hbitPositive
  have hcurrentStart :
      row.currentCoordinates.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (3 : Fin 8)
  have hcurrentFinish :
      row.currentCoordinates.finish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (1 : Fin 8)
  have hnextStart :
      row.nextCoordinates.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (3 : Fin 8)
  have hnextFinish :
      row.nextCoordinates.finish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hnextValue (1 : Fin 8)
  let currentStatusProof :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph
      valuation tokenTable width tokenCount
      row.currentCoordinates.tasksFinish row.currentCoordinates.finish
      valueBound numericBound bitBound hcurrentStatus hvalueBound hwidth
      htokenCount hcurrentStart hcurrentFinish hareaNumeric hareaBit
      htokenTableSize hnumericSize hbitPositive
  let nextStatusProof :=
    compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph
      valuation tokenTable width tokenCount row.nextCoordinates.tasksFinish
      row.nextCoordinates.finish valueBound numericBound bitBound hnextStatus
      hvalueBound hwidth htokenCount hnextStart hnextFinish hareaNumeric
      hareaBit htokenTableSize hnumericSize hbitPositive
  let currentStatusBound : ExplicitDirectFormulaBound valuation
      currentStatusFormula statusResource :=
    { proof := currentStatusProof
      payloadLength_le :=
        compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph_payloadLength_le
          valuation tokenTable width tokenCount
          row.currentCoordinates.tasksFinish row.currentCoordinates.finish
          valueBound numericBound bitBound hcurrentStatus hvalueBound hwidth
          htokenCount hcurrentStart hcurrentFinish hareaNumeric hareaBit
          htokenTableSize hnumericSize hbitPositive }
  let nextStatusBound : ExplicitDirectFormulaBound valuation nextStatusFormula
      statusResource :=
    { proof := nextStatusProof
      payloadLength_le :=
        compileCompactBinaryNatStatusValidBoundedUniformDirectFixedAtValuationOfGraph_payloadLength_le
          valuation tokenTable width tokenCount
          row.nextCoordinates.tasksFinish row.nextCoordinates.finish valueBound
          numericBound bitBound hnextStatus hvalueBound hwidth htokenCount
          hnextStart hnextFinish hareaNumeric hareaBit htokenTableSize
          hnumericSize hbitPositive }
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  have hnextIndexVariables : nextIndexTerm.freeVariables ⊆ {0} := by
    dsimp only [nextIndexTerm]
    rw [parserSyntaxAdjacentIndexAdd_freeVariables,
      parserSyntaxAdjacentIndexOne_freeVariables]
    simpa using hindexVariables
  have hcurrentVariables :
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount indexTerm row.currentCoordinates
          row.currentSize).freeVariables ⊆ {0} :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
      tokenTable width tokenCount stateBoundary stateCount indexTerm
      row.currentCoordinates row.currentSize hindexVariables
  have hnextVariables :
      (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable width
        tokenCount stateBoundary stateCount nextIndexTerm row.nextCoordinates
          row.nextSize).freeVariables ⊆ {0} :=
    compactUnifiedParserStateAtRowsAtValuationIndexFormula_freeVariables_subset_singleton
      tokenTable width tokenCount stateBoundary stateCount nextIndexTerm
      row.nextCoordinates row.nextSize hnextIndexVariables
  have hstepVariables :
      (compactUnifiedParserSyntaxStepClosedFormula tokenTable width tokenCount
        row.currentCoordinates row.nextCoordinates
          row.stepWitness).freeVariables ⊆ {0} := by
    rw [compactUnifiedParserSyntaxStepClosedFormula_freeVariables_eq_empty]
    simp
  have hadjacentVariables : adjacentFormula.freeVariables ⊆ {0} := by
    dsimp only [adjacentFormula]
    rw [compactParserSyntaxAdjacentStepRowAtValuationIndexFormula_alignment]
    unfold compactParserSyntaxAdjacentStepRowAtValuationIndexExplicitFormula
    simpa using Finset.union_subset hcurrentVariables
      (Finset.union_subset hnextVariables hstepVariables)
  have hcurrentStatusVariables : currentStatusFormula.freeVariables ⊆ {0} := by
    dsimp only [currentStatusFormula,
      compactParserSyntaxAdjacentRowCurrentStatusFormula]
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp
  have hnextStatusVariables : nextStatusFormula.freeVariables ⊆ {0} := by
    dsimp only [nextStatusFormula,
      compactParserSyntaxAdjacentRowNextStatusFormula]
    rw [compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty]
    simp
  let bound :=
    compileDirectThreeConjunctionSingletonGeneralBound valuation adjacentFormula
      currentStatusFormula nextStatusFormula adjacentResource statusResource
      statusResource syntaxResource numericBound adjacentBound
      currentStatusBound nextStatusBound hadjacentVariables
      hcurrentStatusVariables hnextStatusVariables hzero (by
        unfold syntaxResource
          compactParserSyntaxAdjacentRowTerminalAtValuationIndexSyntaxResource
        dsimp only [adjacentResource, statusResource]
        omega)
  simpa only [compactParserSyntaxAdjacentRowTerminalAtValuationIndexFormula,
    adjacentFormula, currentStatusFormula, nextStatusFormula,
    compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedPayloadPolynomial,
    syntaxResource, adjacentResource, statusResource] using bound

#print axioms
  compactParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalAtValuationIndexFullyFixedBounds
