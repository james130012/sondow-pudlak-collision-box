import integration.FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFullyFixedBounds
import integration.FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

/-! # Fixed terminal body below the 27 adjacent-row witnesses -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

namespace FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationTermCompilerPublicBounds
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsFullyUniformDirectFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxStepCoordinateFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFormula
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentStepFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusValidBoundedUniformDirectFixedBounds

private abbrev terminalZeroValuation : Nat -> Nat :=
  compactParserStateAtRowsZeroValuation

def compactParserSyntaxAdjacentRowCurrentStatusFormula
    (tokenTable width tokenCount valueBound : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  compactBinaryNatStatusValidBoundedClosedFormula tokenTable width tokenCount
    row.currentCoordinates.tasksFinish row.currentCoordinates.finish valueBound

def compactParserSyntaxAdjacentRowNextStatusFormula
    (tokenTable width tokenCount valueBound : Nat)
    (row : CompactParserSyntaxAdjacentStepRow) : ValuationFormula :=
  compactBinaryNatStatusValidBoundedClosedFormula tokenTable width tokenCount
    row.nextCoordinates.tasksFinish row.nextCoordinates.finish valueBound

def compactParserSyntaxAdjacentRowTerminalSyntaxResource
    (index tokenCount numericBound bitBound : Nat) : Nat :=
  let adjacentResource :=
    compactParserSyntaxAdjacentStepFullyFixedPayloadPolynomial index tokenCount
      numericBound bitBound
  let statusResource :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  valuationContextFormulaCodeSumEnvelope 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length +
    adjacentResource + statusResource + statusResource +
    2 * (binaryNatCode 4).length + 1

def compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial
    (index tokenCount numericBound bitBound : Nat) : Nat :=
  directThreeConjunctionGeneralPayloadEnvelope
    (compactParserSyntaxAdjacentRowTerminalSyntaxResource index tokenCount
      numericBound bitBound)
    (compactParserSyntaxAdjacentStepFullyFixedPayloadPolynomial index tokenCount
      numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)
    (compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound)

noncomputable def compactParserSyntaxAdjacentRowTerminalFullyFixedBound
    (tokenTable width tokenCount stateBoundary stateCount index valueBound :
      Nat)
    (row : CompactParserSyntaxAdjacentStepRow)
    (numericBound bitBound : Nat)
    (hgraph : CompactParserSyntaxAdjacentStepRowGraph tokenTable width tokenCount
      stateBoundary stateCount index row)
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
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ExplicitDirectFormulaBound terminalZeroValuation
      (compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width
          tokenCount stateBoundary stateCount index row ⋏
        (compactParserSyntaxAdjacentRowCurrentStatusFormula tokenTable width
            tokenCount valueBound row ⋏
          compactParserSyntaxAdjacentRowNextStatusFormula tokenTable width
            tokenCount valueBound row))
      (compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial index
        tokenCount numericBound bitBound) := by
  let adjacentFormula :=
    compactParserSyntaxAdjacentStepRowClosedFormula tokenTable width tokenCount
      stateBoundary stateCount index row
  let currentStatusFormula :=
    compactParserSyntaxAdjacentRowCurrentStatusFormula tokenTable width
      tokenCount valueBound row
  let nextStatusFormula :=
    compactParserSyntaxAdjacentRowNextStatusFormula tokenTable width tokenCount
      valueBound row
  let adjacentResource :=
    compactParserSyntaxAdjacentStepFullyFixedPayloadPolynomial index tokenCount
      numericBound bitBound
  let statusResource :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedPayloadPolynomial
      numericBound bitBound
  let syntaxResource :=
    compactParserSyntaxAdjacentRowTerminalSyntaxResource index tokenCount
      numericBound bitBound
  let adjacentBound :=
    compactParserSyntaxAdjacentStepFullyFixedBoundOfGraph tokenTable width
      tokenCount stateBoundary stateCount index row numericBound bitBound
      hgraph hwidth hwidthBit htokenCount hstateCount hcurrentValue hnextValue
      htokenTableSize hstateBoundarySize hcurrentSize hnextSize hwitnessValue
      hwitnessSize hnumericSize hbitPositive
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
  let currentStatusRaw :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfGraph tokenTable
      width tokenCount row.currentCoordinates.tasksFinish
      row.currentCoordinates.finish valueBound numericBound bitBound
      hcurrentStatus hvalueBound hwidth htokenCount hcurrentStart
      hcurrentFinish hareaNumeric hareaBit htokenTableSize hnumericSize
      hbitPositive
  let nextStatusRaw :=
    compactBinaryNatStatusValidBoundedUniformDirectFixedBoundOfGraph tokenTable
      width tokenCount row.nextCoordinates.tasksFinish
      row.nextCoordinates.finish valueBound numericBound bitBound hnextStatus
      hvalueBound hwidth htokenCount hnextStart hnextFinish hareaNumeric
      hareaBit htokenTableSize hnumericSize hbitPositive
  have hcurrentStatusClosed : currentStatusFormula.freeVariables = ∅ := by
    dsimp only [currentStatusFormula,
      compactParserSyntaxAdjacentRowCurrentStatusFormula]
    exact compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount row.currentCoordinates.tasksFinish
        row.currentCoordinates.finish valueBound
  have hnextStatusClosed : nextStatusFormula.freeVariables = ∅ := by
    dsimp only [nextStatusFormula,
      compactParserSyntaxAdjacentRowNextStatusFormula]
    exact compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty
      tokenTable width tokenCount row.nextCoordinates.tasksFinish
        row.nextCoordinates.finish valueBound
  let currentStatusProof : CertifiedPAContextProof
      (valuationContext currentStatusFormula.freeVariables
        terminalZeroValuation) currentStatusFormula :=
    CertifiedPAContextProof.castContext (by
      rw [
        compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty,
        hcurrentStatusClosed]
      simp [valuationContext]) currentStatusRaw.proof
  let nextStatusProof : CertifiedPAContextProof
      (valuationContext nextStatusFormula.freeVariables
        terminalZeroValuation) nextStatusFormula :=
    CertifiedPAContextProof.castContext (by
      rw [
        compactBinaryNatStatusValidBoundedClosedFormula_freeVariables_eq_empty,
        hnextStatusClosed]
      simp [valuationContext]) nextStatusRaw.proof
  let currentStatusBound : ExplicitDirectFormulaBound terminalZeroValuation
      currentStatusFormula statusResource :=
    { proof := currentStatusProof
      payloadLength_le := by
        dsimp only [currentStatusProof]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        exact currentStatusRaw.payloadLength_le }
  let nextStatusBound : ExplicitDirectFormulaBound terminalZeroValuation
      nextStatusFormula statusResource :=
    { proof := nextStatusProof
      payloadLength_le := by
        dsimp only [nextStatusProof]
        rw [CertifiedPAContextProof.castContext_payloadLength]
        exact nextStatusRaw.payloadLength_le }
  have hadjacentVariables : adjacentFormula.freeVariables ⊆ {0} := by
    dsimp only [adjacentFormula]
    rw [
      compactParserSyntaxAdjacentStepRowClosedFormula_freeVariables_eq_empty]
    simp
  have hcurrentStatusVariables : currentStatusFormula.freeVariables ⊆ {0} := by
    rw [hcurrentStatusClosed]
    simp
  have hnextStatusVariables : nextStatusFormula.freeVariables ⊆ {0} := by
    rw [hnextStatusClosed]
    simp
  let bound :=
    compileDirectThreeConjunctionSingletonGeneralBound terminalZeroValuation
      adjacentFormula currentStatusFormula nextStatusFormula adjacentResource
      statusResource statusResource syntaxResource numericBound adjacentBound
      currentStatusBound nextStatusBound hadjacentVariables
      hcurrentStatusVariables hnextStatusVariables
      (by
        change 0 <= numericBound
        exact Nat.zero_le _)
      (by
        unfold syntaxResource
          compactParserSyntaxAdjacentRowTerminalSyntaxResource
        dsimp only [adjacentResource, statusResource]
        omega)
  simpa only [adjacentFormula, currentStatusFormula, nextStatusFormula,
    compactParserSyntaxAdjacentRowTerminalFullyFixedPayloadPolynomial,
    syntaxResource, adjacentResource, statusResource] using bound

end FoundationCompactNumericListedDirectParserSyntaxAdjacentRowTerminalFullyFixedBounds
