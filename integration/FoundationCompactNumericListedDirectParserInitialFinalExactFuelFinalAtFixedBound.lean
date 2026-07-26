import integration.FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
import integration.FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds

/-! # Fixed exact-fuel final-row parser bound -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 350000

namespace FoundationCompactNumericListedDirectParserInitialFinalExactFuelFinalAtFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows
open FoundationCompactNumericListedDirectParserStateAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserStateAtRowsTermCodeFixedBounds
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFuelFixedBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsFixedLeafBounds
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle

def compactParserInitialFinalExactFuelFinalAtTermCodeBound
    (numericBound : Nat) : Nat :=
  compactParserSyntaxExactStateCountTermFixedCodePolynomial numericBound

def compactParserInitialFinalExactFuelFinalAtFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  compactParserStateAtRowsTermCodeFixedPayloadPolynomial
    (compactParserInitialFinalExactFuelFinalAtTermCodeBound numericBound)
      numericBound bitBound

noncomputable def parserInitialFinalExactFuelFinalAtFixedClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputCount
      numericBound bitBound : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sizeWitness : CompactUnifiedParserStateCoreSizeWitness)
    (hgraph : CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount (compactParserSyntaxExactFuel inputCount)
        coordinates sizeWitness)
    (hinputCount : inputCount <= numericBound)
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
    ParserInitialFinalClosedDirectBound
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount coordinates sizeWitness)
      (compactParserInitialFinalExactFuelFinalAtFixedPayloadPolynomial
        numericBound bitBound) := by
  let indexTerm := compactParserSyntaxExactFuelTerm inputCount
  let nextIndexTerm : ValuationTerm := ‘!!indexTerm + 1’
  let termCodeBound :=
    compactParserInitialFinalExactFuelFinalAtTermCodeBound numericBound
  have hindexVariables : indexTerm.freeVariables ⊆ {0} := by
    rw [show indexTerm.freeVariables = ∅ by
      exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount]
    simp
  have hindexCode : (binaryTermCode indexTerm).length <= termCodeBound := by
    have hcode := compactParserSyntaxExactFuelTerm_code_length_le_fixed
      inputCount numericBound hinputCount
    exact hcode.trans (by
      unfold termCodeBound
        compactParserInitialFinalExactFuelFinalAtTermCodeBound
        compactParserSyntaxExactStateCountTermFixedCodePolynomial
      omega)
  have hnextIndexCode : (binaryTermCode nextIndexTerm).length <=
      termCodeBound := by
    have hcode := compactParserSyntaxExactStateCountTerm_code_length_le_fixed
      inputCount numericBound hinputCount
    simpa only [nextIndexTerm, indexTerm,
      compactParserSyntaxExactStateCountTerm, termCodeBound,
      compactParserInitialFinalExactFuelFinalAtTermCodeBound] using hcode
  have hgraphAtTerm : CompactUnifiedParserStateAtRows tokenTable width
      tokenCount stateBoundary stateCount
      (termValue compactParserStateAtRowsZeroValuation indexTerm)
        coordinates sizeWitness := by
    change CompactUnifiedParserStateAtRows tokenTable width tokenCount
      stateBoundary stateCount
      (termValue (fun _ => 0)
        (compactParserSyntaxExactFuelTerm inputCount))
      coordinates sizeWitness
    rw [compactParserSyntaxExactFuelTerm_value]
    exact hgraph
  let bound :=
    compactUnifiedParserStateAtRowsAtValuationIndexTermCodeFixedBound
      tokenTable width tokenCount stateBoundary stateCount indexTerm coordinates
      sizeWitness termCodeBound numericBound bitBound hindexVariables hindexCode
      hnextIndexCode hgraphAtTerm hwidth htokenCount hstateCount
      hcoordinatesValue htokenTableSize hstateBoundarySize hcoordinatesSize
      hnumericSize
  have hclosed :
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount coordinates
          sizeWitness).freeVariables = ∅ := by
    unfold compactParserInitialFinalExactFuelFinalAtFormula
      compactUnifiedParserStateAtRowsAtValuationIndexFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms_atArity
    intro coordinate
    fin_cases coordinate <;>
      first
      | exact compactParserSyntaxExactFuelTerm_freeVariables_eq_empty inputCount
      | exact shortBinaryNumeralTerm_freeVariables_eq_empty _
  let proof : CertifiedPAContextProof ∅
      (compactParserInitialFinalExactFuelFinalAtFormula tokenTable width
        tokenCount stateBoundary stateCount inputCount coordinates
          sizeWitness) :=
    CertifiedPAContextProof.castContext (by
      have hboundClosed :
          (compactUnifiedParserStateAtRowsAtValuationIndexFormula tokenTable
            width tokenCount stateBoundary stateCount indexTerm coordinates
              sizeWitness).freeVariables = ∅ := by
        simpa only [indexTerm,
          compactParserInitialFinalExactFuelFinalAtFormula] using hclosed
      rw [hboundClosed]
      simp [valuationContext]) bound.proof
  refine ⟨proof, ?_⟩
  change (CertifiedPAContextProof.castContext _ bound.proof).payloadLength <= _
  rw [CertifiedPAContextProof.castContext_payloadLength]
  simpa only [compactParserInitialFinalExactFuelFinalAtFixedPayloadPolynomial,
    termCodeBound] using bound.payloadLength_le

#print axioms
  parserInitialFinalExactFuelFinalAtFixedClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserInitialFinalExactFuelFinalAtFixedBound
