import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsSubstitutionAlignment
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowEntryExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskListRowCoreRevalueExplicitHybridCertificate

/-!
# Explicit terminal certificate for one verifier task-list row

The two checked table endpoints and the checked task core are conjoined and
then transported across the exact fourteen-witness substitution identity.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-- The fourteen row witnesses in binder order. -/
def taskListRowWitnessValues
    (start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    Fin 14 -> Nat :=
  ![gammaBoundarySize, suffixCount, witnessCount, witnessFinish,
    secondCount, secondFinish, firstCount, firstFinish, gammaBoundary,
    gammaCount, gammaFinish, tag, finish, start]

/-- Explicit terminal certificate from the two row endpoints and task core. -/
opaque taskListRowTerminalExplicitHybridCertificate
    (tokenTable width tokenCount taskBoundary rowIndex
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat)
    (hstartEntry : CompactFixedWidthEntry
      taskBoundary tokenCount rowIndex start)
    (hfinishEntry : CompactFixedWidthEntry
      taskBoundary tokenCount (rowIndex + 1) finish)
    (hcore : CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      (compactNumericVerifierTaskRowCoordinatesOf
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount)
      { gammaBoundarySize := gammaBoundarySize }) :
    HybridCertificate (taskListRowsBranchValuation rowIndex)
      ((compactNumericVerifierTaskListRowsBranchTerminal
          tokenTable width tokenCount taskBoundary (&0 : ValuationTerm)) ⇜
        fun coordinate => shortBinaryNumeralTerm
          (taskListRowWitnessValues
            start finish tag gammaFinish gammaCount gammaBoundary
            firstFinish firstCount secondFinish secondCount
            witnessFinish witnessCount suffixCount gammaBoundarySize
            coordinate)) := by
  let valuation := taskListRowsBranchValuation rowIndex
  let values := taskListRowWitnessValues
    start finish tag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount gammaBoundarySize
  let coordinates := compactNumericVerifierTaskRowCoordinatesOf
    start finish tag gammaFinish gammaCount gammaBoundary
    firstFinish firstCount secondFinish secondCount
    witnessFinish witnessCount suffixCount
  let sizeWitness : CompactNumericVerifierTaskSizeWitness :=
    { gammaBoundarySize := gammaBoundarySize }
  let terminalParts : HybridCertificate valuation
      (compactNumericVerifierTaskListRowsTerminalPartsFormula
        tokenTable width tokenCount taskBoundary
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount gammaBoundarySize) := by
    unfold compactNumericVerifierTaskListRowsTerminalPartsFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (taskListRowStartEntryExplicitHybridCertificate
        taskBoundary tokenCount rowIndex start hstartEntry)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (taskListRowFinishEntryExplicitHybridCertificate
          taskBoundary tokenCount rowIndex finish hfinishEntry)
        (taskListRowCoreAtBranchExplicitHybridCertificate
          valuation tokenTable width tokenCount coordinates sizeWitness hcore))
  have hvalueTerms :
      (fun coordinate : Fin 14 =>
        shortBinaryNumeralTerm (values coordinate)) =
      ![shortBinaryNumeralTerm gammaBoundarySize,
        shortBinaryNumeralTerm suffixCount,
        shortBinaryNumeralTerm witnessCount,
        shortBinaryNumeralTerm witnessFinish,
        shortBinaryNumeralTerm secondCount,
        shortBinaryNumeralTerm secondFinish,
        shortBinaryNumeralTerm firstCount,
        shortBinaryNumeralTerm firstFinish,
        shortBinaryNumeralTerm gammaBoundary,
        shortBinaryNumeralTerm gammaCount,
        shortBinaryNumeralTerm gammaFinish,
        shortBinaryNumeralTerm tag,
        shortBinaryNumeralTerm finish,
        shortBinaryNumeralTerm start] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  exact .cast (by
    rw [hvalueTerms]
    exact
      (compactNumericVerifierTaskListRowsBranchTerminal_substitution_alignment
        tokenTable width tokenCount taskBoundary
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount witnessFinish
        witnessCount suffixCount gammaBoundarySize).symm) terminalParts

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
