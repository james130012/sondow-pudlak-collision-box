import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactPAEmbeddedPredicateFreeVariables

/-!
# Free-variable bounds for adjacent-row raw terminals

Every raw terminal may mention only the variables already present in the public
row-index term.  Local witness coordinates are bound variables and all other
parameters are closed binary numerals.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalFreeVariables

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate

theorem compactFormulaTransformAdjacentCurrentBoundedRawTerminal_freeVariables_subset
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    (compactFormulaTransformAdjacentCurrentBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound).freeVariables ⊆
        rowIndexTerm.freeVariables := by
  unfold compactFormulaTransformAdjacentCurrentBoundedRawTerminal
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate <;>
    simp [sourceSubstitutionLift_freeVariables_eq,
      shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem compactFormulaTransformAdjacentNextBoundedRawTerminal_freeVariables_subset
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness) :
    (compactFormulaTransformAdjacentNextBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize).freeVariables ⊆ rowIndexTerm.freeVariables := by
  unfold compactFormulaTransformAdjacentNextBoundedRawTerminal
  apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
  intro coordinate
  fin_cases coordinate <;>
    simp [sourceSubstitutionLift_freeVariables_eq,
      shortBinaryNumeralTerm_freeVariables_eq_empty]

theorem
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_freeVariables_subset
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness) :
    (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound currentCoordinates
      currentSize nextCoordinates nextSize).freeVariables ⊆
        rowIndexTerm.freeVariables := by
  unfold compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal
  simp only [LO.FirstOrder.Semiformula.freeVariables_and]
  apply Finset.union_subset
  · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
    intro coordinate
    fin_cases coordinate <;>
      simp [sourceSubstitutionLift_freeVariables_eq,
        shortBinaryNumeralTerm_freeVariables_eq_empty]
  · apply Finset.union_subset
    · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionLift_freeVariables_eq,
          shortBinaryNumeralTerm_freeVariables_eq_empty]
    · apply embeddedSubstitution_freeVariables_subset_of_term_subset_atArity
      intro coordinate
      fin_cases coordinate <;>
        simp [sourceSubstitutionLift_freeVariables_eq,
          shortBinaryNumeralTerm_freeVariables_eq_empty]

#print axioms
  compactFormulaTransformAdjacentCurrentBoundedRawTerminal_freeVariables_subset
#print axioms
  compactFormulaTransformAdjacentNextBoundedRawTerminal_freeVariables_subset
#print axioms
  compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_freeVariables_subset

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalFreeVariables
