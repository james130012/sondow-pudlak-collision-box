import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalFreeVariables
import integration.FoundationCompactPAValuationTermCompilerUniformBounds

/-!
# Public context bounds for adjacent-row raw terminals

All three raw terminals use only variables already occurring in the public row
index term.  Hence one valuation-context code sum controls every nested witness
compiler, independently of all concrete graph witnesses.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds

open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactPAValuationTermCompilerUniformBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalFreeVariables

def compactFormulaTransformAdjacentPublicContextCodeBound
    (valuation : Nat -> Nat) (rowIndexTerm : ValuationTerm) : Nat :=
  formulaCodeSum
    (valuationContext rowIndexTerm.freeVariables valuation)

theorem compactFormulaTransformAdjacentPublicContextCodeBound_variable0_le
    (rowIndex rowCount : Nat) (hrowIndex : rowIndex < rowCount) :
    compactFormulaTransformAdjacentPublicContextCodeBound
        (extendValuation rowIndex (fun _ => 0)) (&0 : ValuationTerm) <=
      valuationTermContextFormulaCodeEnvelope
        rowCount (&0 : ValuationTerm) := by
  unfold compactFormulaTransformAdjacentPublicContextCodeBound
  apply valuationTermContext_formulaCodeSum_le_envelope
  intro index hindex
  simp only [LO.FirstOrder.Semiterm.freeVariables_fvar,
    Finset.mem_singleton] at hindex
  subst index
  simp only [extendValuation_zero]
  omega

theorem compactFormulaTransformAdjacentCurrentRawTerminal_context_le_public
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    formulaCodeSum
        (valuationContext
          (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
            mode witnessStart witnessFinish witnessCount valueBound).freeVariables
          valuation) <=
      compactFormulaTransformAdjacentPublicContextCodeBound
        valuation rowIndexTerm := by
  unfold compactFormulaTransformAdjacentPublicContextCodeBound
  exact formulaCodeSum_mono
    (valuationContext_mono valuation
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal_freeVariables_subset
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound))

theorem compactFormulaTransformAdjacentNextRawTerminal_context_le_public
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    formulaCodeSum
        (valuationContext
          (compactFormulaTransformAdjacentNextBoundedRawTerminal
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
            mode witnessStart witnessFinish witnessCount valueBound
            currentCoordinates currentSize).freeVariables valuation) <=
      compactFormulaTransformAdjacentPublicContextCodeBound
        valuation rowIndexTerm := by
  unfold compactFormulaTransformAdjacentPublicContextCodeBound
  exact formulaCodeSum_mono
    (valuationContext_mono valuation
      (compactFormulaTransformAdjacentNextBoundedRawTerminal_freeVariables_subset
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize))

theorem compactFormulaTransformAdjacentStepRawTerminal_context_le_public
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    formulaCodeSum
        (valuationContext
          (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
            tokenTable width tokenCount stateBoundary stateCount rowIndexTerm
            mode witnessStart witnessFinish witnessCount valueBound
            currentCoordinates currentSize nextCoordinates
            nextSize).freeVariables valuation) <=
      compactFormulaTransformAdjacentPublicContextCodeBound
        valuation rowIndexTerm := by
  unfold compactFormulaTransformAdjacentPublicContextCodeBound
  exact formulaCodeSum_mono
    (valuationContext_mono valuation
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_freeVariables_subset
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound currentCoordinates
        currentSize nextCoordinates nextSize))

#print axioms
  compactFormulaTransformAdjacentCurrentRawTerminal_context_le_public
#print axioms
  compactFormulaTransformAdjacentPublicContextCodeBound_variable0_le
#print axioms
  compactFormulaTransformAdjacentNextRawTerminal_context_le_public
#print axioms
  compactFormulaTransformAdjacentStepRawTerminal_context_le_public

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicContextBounds
