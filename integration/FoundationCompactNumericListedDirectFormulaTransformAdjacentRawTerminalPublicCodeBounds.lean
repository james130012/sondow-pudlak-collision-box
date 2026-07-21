import integration.FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBoundedEndpointCodeBounds

/-!
# Public code bounds for adjacent-row raw terminals

The current, next, and step source vectors share eleven public parameters.
The remaining fourteen or twenty-eight entries are bounded witnesses, so one
public term-code coordinate controls all three fixed raw-terminal templates.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerUniformBounds
open FoundationCompactNumericListedDirectBoundedEndpointCodeBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformAdjacentStepWitnessBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentNextBoundedAtValuationIndexExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformAdjacentCurrentBoundedAtValuationIndexExplicitHybridCertificate

def compactFormulaTransformAdjacentPublicSourceTermCodeBound
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  sourceTermCodeSum
      (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
        stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
        valueBound) +
    boundedWitnessNumeralTermCodeEnvelope valueBound

theorem adjacentCurrentSourceTerms_code_length_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    forall index,
      (binaryTermCode
        (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound index)).length <=
        compactFormulaTransformAdjacentPublicSourceTermCodeBound tokenTable
          width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound := by
  intro index
  exact (sourceTermCode_length_le_sum
    (adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
      stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
      valueBound) index).trans (Nat.le_add_right _ _)

private theorem adjacentNextSourceTerms_public_or_currentWitness
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (index : Fin 25) :
    (∃ publicIndex : Fin 11,
      adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize index =
        adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound publicIndex) ∨
    (∃ witnessIndex : Fin 14,
      adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize index =
        shortBinaryNumeralTerm
          (adjacentCurrentBoundedWitnessValues
            ⟨currentCoordinates, currentSize⟩ witnessIndex)) := by
  fin_cases index
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inl ⟨4, rfl⟩
  · exact Or.inl ⟨5, rfl⟩
  · exact Or.inl ⟨6, rfl⟩
  · exact Or.inl ⟨7, rfl⟩
  · exact Or.inl ⟨8, rfl⟩
  · exact Or.inl ⟨9, rfl⟩
  · exact Or.inl ⟨10, rfl⟩
  · exact Or.inr ⟨13, rfl⟩
  · exact Or.inr ⟨12, rfl⟩
  · exact Or.inr ⟨11, rfl⟩
  · exact Or.inr ⟨10, rfl⟩
  · exact Or.inr ⟨9, rfl⟩
  · exact Or.inr ⟨8, rfl⟩
  · exact Or.inr ⟨7, rfl⟩
  · exact Or.inr ⟨6, rfl⟩
  · exact Or.inr ⟨5, rfl⟩
  · exact Or.inr ⟨4, rfl⟩
  · exact Or.inr ⟨3, rfl⟩
  · exact Or.inr ⟨2, rfl⟩
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨0, rfl⟩

theorem adjacentNextSourceTerms_code_length_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound) :
    forall index,
      (binaryTermCode
        (adjacentNextSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound currentCoordinates currentSize index)).length <=
        compactFormulaTransformAdjacentPublicSourceTermCodeBound tokenTable
          width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound := by
  intro index
  rcases adjacentNextSourceTerms_public_or_currentWitness tokenTable width
    tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
    witnessFinish witnessCount valueBound currentCoordinates currentSize index
    with ⟨publicIndex, hpublic⟩ | ⟨witnessIndex, hwitness⟩
  · rw [hpublic]
    exact adjacentCurrentSourceTerms_code_length_le_public tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound publicIndex
  · rw [hwitness]
    exact (shortBinaryNumeralTerm_code_length_le_bound _ valueBound
      (hcurrent witnessIndex)).trans (Nat.le_add_left _ _)

private theorem boundedSourceTerms_public_or_stateWitness
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (index : Fin 39) :
    (∃ publicIndex : Fin 11,
      boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize index =
        adjacentCurrentSourceTerms tokenTable width tokenCount stateBoundary
          stateCount rowIndexTerm mode witnessStart witnessFinish witnessCount
          valueBound publicIndex) ∨
    (∃ witnessIndex : Fin 14,
      boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize index =
        shortBinaryNumeralTerm
          (adjacentCurrentBoundedWitnessValues
            ⟨currentCoordinates, currentSize⟩ witnessIndex)) ∨
    (∃ witnessIndex : Fin 14,
      boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize index =
        shortBinaryNumeralTerm
          (adjacentNextBoundedWitnessValues
            ⟨nextCoordinates, nextSize⟩ witnessIndex)) := by
  fin_cases index
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inl ⟨3, rfl⟩
  · exact Or.inl ⟨4, rfl⟩
  · exact Or.inl ⟨5, rfl⟩
  · exact Or.inl ⟨6, rfl⟩
  · exact Or.inl ⟨7, rfl⟩
  · exact Or.inl ⟨8, rfl⟩
  · exact Or.inl ⟨9, rfl⟩
  · exact Or.inl ⟨10, rfl⟩
  · exact Or.inr (Or.inl ⟨13, rfl⟩)
  · exact Or.inr (Or.inl ⟨12, rfl⟩)
  · exact Or.inr (Or.inl ⟨11, rfl⟩)
  · exact Or.inr (Or.inl ⟨10, rfl⟩)
  · exact Or.inr (Or.inl ⟨9, rfl⟩)
  · exact Or.inr (Or.inl ⟨8, rfl⟩)
  · exact Or.inr (Or.inl ⟨7, rfl⟩)
  · exact Or.inr (Or.inl ⟨6, rfl⟩)
  · exact Or.inr (Or.inl ⟨5, rfl⟩)
  · exact Or.inr (Or.inl ⟨4, rfl⟩)
  · exact Or.inr (Or.inl ⟨3, rfl⟩)
  · exact Or.inr (Or.inl ⟨2, rfl⟩)
  · exact Or.inr (Or.inl ⟨1, rfl⟩)
  · exact Or.inr (Or.inl ⟨0, rfl⟩)
  · exact Or.inr (Or.inr ⟨13, rfl⟩)
  · exact Or.inr (Or.inr ⟨12, rfl⟩)
  · exact Or.inr (Or.inr ⟨11, rfl⟩)
  · exact Or.inr (Or.inr ⟨10, rfl⟩)
  · exact Or.inr (Or.inr ⟨9, rfl⟩)
  · exact Or.inr (Or.inr ⟨8, rfl⟩)
  · exact Or.inr (Or.inr ⟨7, rfl⟩)
  · exact Or.inr (Or.inr ⟨6, rfl⟩)
  · exact Or.inr (Or.inr ⟨5, rfl⟩)
  · exact Or.inr (Or.inr ⟨4, rfl⟩)
  · exact Or.inr (Or.inr ⟨3, rfl⟩)
  · exact Or.inr (Or.inr ⟨2, rfl⟩)
  · exact Or.inr (Or.inr ⟨1, rfl⟩)
  · exact Or.inr (Or.inr ⟨0, rfl⟩)

theorem boundedSourceTerms_code_length_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨nextCoordinates, nextSize⟩ index <= valueBound) :
    forall index,
      (binaryTermCode
        (boundedSourceTerms tokenTable width tokenCount stateBoundary stateCount
          rowIndexTerm mode witnessStart witnessFinish witnessCount valueBound
          currentCoordinates currentSize nextCoordinates nextSize index)).length
        <= compactFormulaTransformAdjacentPublicSourceTermCodeBound tokenTable
          width tokenCount stateBoundary stateCount rowIndexTerm mode
          witnessStart witnessFinish witnessCount valueBound := by
  intro index
  rcases boundedSourceTerms_public_or_stateWitness tokenTable width tokenCount
    stateBoundary stateCount rowIndexTerm mode witnessStart witnessFinish
    witnessCount valueBound currentCoordinates currentSize nextCoordinates
    nextSize index with ⟨publicIndex, hpublic⟩ |
      ⟨witnessIndex, hcurrentWitness⟩ | ⟨witnessIndex, hnextWitness⟩
  · rw [hpublic]
    exact adjacentCurrentSourceTerms_code_length_le_public tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound publicIndex
  · rw [hcurrentWitness]
    exact (shortBinaryNumeralTerm_code_length_le_bound _ valueBound
      (hcurrent witnessIndex)).trans (Nat.le_add_left _ _)
  · rw [hnextWitness]
    exact (shortBinaryNumeralTerm_code_length_le_bound _ valueBound
      (hnext witnessIndex)).trans (Nat.le_add_left _ _)

def compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  compactFormulaTransformAdjacentCurrentBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
    (compactFormulaTransformAdjacentPublicSourceTermCodeBound tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)

def compactFormulaTransformAdjacentNextRawTerminalPublicCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  compactFormulaTransformAdjacentNextBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
    (compactFormulaTransformAdjacentPublicSourceTermCodeBound tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)

def compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) : Nat :=
  compactFormulaTransformAdjacentStepWitnessBoundedRawTerminalPolynomialSourceCodeEnvelopeOfTermBound
    (compactFormulaTransformAdjacentPublicSourceTermCodeBound tokenTable width
      tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
      witnessFinish witnessCount valueBound)

theorem compactFormulaTransformAdjacentCurrentRawTerminal_code_length_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentCurrentBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound)).length <=
      compactFormulaTransformAdjacentCurrentRawTerminalPublicCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound := by
  exact
    compactFormulaTransformAdjacentCurrentBoundedRawTerminal_code_length_le_polynomial_source_of_termBound
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound _
      (adjacentCurrentSourceTerms_code_length_le_public tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound)

theorem compactFormulaTransformAdjacentNextRawTerminal_code_length_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentNextBoundedRawTerminal tokenTable width
        tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates
        currentSize)).length <=
      compactFormulaTransformAdjacentNextRawTerminalPublicCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound := by
  exact
    compactFormulaTransformAdjacentNextBoundedRawTerminal_code_length_le_polynomial_source_of_termBound
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound _ currentCoordinates
      currentSize
      (adjacentNextSourceTerms_code_length_le_public tokenTable width tokenCount
        stateBoundary stateCount rowIndexTerm mode witnessStart witnessFinish
        witnessCount valueBound currentCoordinates currentSize hcurrent)

theorem compactFormulaTransformAdjacentStepRawTerminal_code_length_le_public
    (tokenTable width tokenCount stateBoundary stateCount : Nat)
    (rowIndexTerm : ValuationTerm)
    (mode witnessStart witnessFinish witnessCount valueBound : Nat)
    (currentCoordinates : CompactFormulaTransformStateRowCoordinates)
    (currentSize : CompactFormulaTransformStateCoreSizeWitness)
    (nextCoordinates : CompactFormulaTransformStateRowCoordinates)
    (nextSize : CompactFormulaTransformStateCoreSizeWitness)
    (hcurrent : forall index,
      adjacentCurrentBoundedWitnessValues
        ⟨currentCoordinates, currentSize⟩ index <= valueBound)
    (hnext : forall index,
      adjacentNextBoundedWitnessValues
        ⟨nextCoordinates, nextSize⟩ index <= valueBound) :
    (binaryFormulaCode
      (compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal tokenTable
        width tokenCount stateBoundary stateCount rowIndexTerm mode witnessStart
        witnessFinish witnessCount valueBound currentCoordinates currentSize
        nextCoordinates nextSize)).length <=
      compactFormulaTransformAdjacentStepRawTerminalPublicCodeEnvelope
        tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
        witnessStart witnessFinish witnessCount valueBound := by
  exact
    compactFormulaTransformAdjacentStepWitnessBoundedRawTerminal_code_length_le_polynomial_source_of_termBound
      tokenTable width tokenCount stateBoundary stateCount rowIndexTerm mode
      witnessStart witnessFinish witnessCount valueBound _ currentCoordinates
      currentSize nextCoordinates nextSize
      (boundedSourceTerms_code_length_le_public tokenTable width tokenCount
        stateBoundary stateCount rowIndexTerm mode witnessStart witnessFinish
        witnessCount valueBound currentCoordinates currentSize nextCoordinates
        nextSize hcurrent hnext)

#print axioms adjacentCurrentSourceTerms_code_length_le_public
#print axioms adjacentNextSourceTerms_code_length_le_public
#print axioms boundedSourceTerms_code_length_le_public
#print axioms
  compactFormulaTransformAdjacentCurrentRawTerminal_code_length_le_public
#print axioms
  compactFormulaTransformAdjacentNextRawTerminal_code_length_le_public
#print axioms
  compactFormulaTransformAdjacentStepRawTerminal_code_length_le_public

end FoundationCompactNumericListedDirectFormulaTransformAdjacentRawTerminalPublicCodeBounds
