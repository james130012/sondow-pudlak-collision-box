import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsSourceAlignment

/-!
# Witness-vector extraction for one verifier task-list row

The nested existential row proposition is normalized to one fourteen-entry
vector plus a proposition recording every bound, endpoint, and task-core fact.
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
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula

/-- Exact checked facts carried by a fourteen-entry task-row witness vector.
The vector order is the binder order: gamma-boundary size at coordinate zero
and the row start at coordinate thirteen. -/
def CompactNumericVerifierTaskRowWitnessFacts
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
    (values : Fin 14 -> Nat) : Prop :=
  values 13 ≤ valueBound ∧
  values 12 ≤ valueBound ∧
  values 11 ≤ valueBound ∧
  values 10 ≤ valueBound ∧
  values 9 ≤ valueBound ∧
  values 8 ≤ valueBound ∧
  values 7 ≤ valueBound ∧
  values 6 ≤ valueBound ∧
  values 5 ≤ valueBound ∧
  values 4 ≤ valueBound ∧
  values 3 ≤ valueBound ∧
  values 2 ≤ valueBound ∧
  values 1 ≤ valueBound ∧
  values 0 ≤ valueBound ∧
  CompactFixedWidthEntry taskBoundary tokenCount rowIndex (values 13) ∧
  CompactFixedWidthEntry taskBoundary tokenCount (rowIndex + 1) (values 12) ∧
  CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
    (compactNumericVerifierTaskRowCoordinatesOf
      (values 13) (values 12) (values 11) (values 10) (values 9)
      (values 8) (values 7) (values 6) (values 5) (values 4)
      (values 3) (values 2) (values 1))
    { gammaBoundarySize := values 0 }

/-- The original nested row proposition supplies one exact witness vector. -/
theorem existsTaskListRowWitnessValues
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex) :
    ∃ values : Fin 14 -> Nat,
      CompactNumericVerifierTaskRowWitnessFacts
        tokenTable width tokenCount taskBoundary valueBound rowIndex values := by
  unfold CompactNumericVerifierTaskBoundedRow at hrow
  rcases hrow with
    ⟨start, hstartLe, finish, hfinishLe, tag, htagLe,
      gammaFinish, hgammaFinishLe, gammaCount, hgammaCountLe,
      gammaBoundary, hgammaBoundaryLe, firstFinish, hfirstFinishLe,
      firstCount, hfirstCountLe, secondFinish, hsecondFinishLe,
      secondCount, hsecondCountLe, witnessFinish, hwitnessFinishLe,
      witnessCount, hwitnessCountLe, suffixCount, hsuffixCountLe,
      gammaBoundarySize, hgammaBoundarySizeLe,
      hstartEntry, hfinishEntry, hcore⟩
  refine ⟨![gammaBoundarySize, suffixCount, witnessCount, witnessFinish,
    secondCount, secondFinish, firstCount, firstFinish, gammaBoundary,
    gammaCount, gammaFinish, tag, finish, start], ?_⟩
  change
    start ≤ valueBound ∧ finish ≤ valueBound ∧ tag ≤ valueBound ∧
    gammaFinish ≤ valueBound ∧ gammaCount ≤ valueBound ∧
    gammaBoundary ≤ valueBound ∧ firstFinish ≤ valueBound ∧
    firstCount ≤ valueBound ∧ secondFinish ≤ valueBound ∧
    secondCount ≤ valueBound ∧ witnessFinish ≤ valueBound ∧
    witnessCount ≤ valueBound ∧ suffixCount ≤ valueBound ∧
    gammaBoundarySize ≤ valueBound ∧
    CompactFixedWidthEntry taskBoundary tokenCount rowIndex start ∧
    CompactFixedWidthEntry taskBoundary tokenCount (rowIndex + 1) finish ∧
    CompactNumericVerifierTaskCoreGraph tokenTable width tokenCount
      (compactNumericVerifierTaskRowCoordinatesOf
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount)
      { gammaBoundarySize := gammaBoundarySize }
  exact ⟨hstartLe, hfinishLe, htagLe, hgammaFinishLe, hgammaCountLe,
    hgammaBoundaryLe, hfirstFinishLe, hfirstCountLe, hsecondFinishLe,
    hsecondCountLe, hwitnessFinishLe, hwitnessCountLe, hsuffixCountLe,
    hgammaBoundarySizeLe, hstartEntry, hfinishEntry, hcore⟩

/-- A single chosen witness vector for the checked row. -/
noncomputable def taskListRowWitnessValuesOfBoundedRow
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex) :
    Fin 14 -> Nat :=
  Classical.choose (existsTaskListRowWitnessValues
    tokenTable width tokenCount taskBoundary valueBound rowIndex hrow)

/-- The chosen vector retains the complete checked row specification. -/
theorem taskListRowWitnessValuesOfBoundedRow_spec
    (tokenTable width tokenCount taskBoundary valueBound rowIndex : Nat)
    (hrow : CompactNumericVerifierTaskBoundedRow
      tokenTable width tokenCount taskBoundary valueBound rowIndex) :
    CompactNumericVerifierTaskRowWitnessFacts
      tokenTable width tokenCount taskBoundary valueBound rowIndex
        (taskListRowWitnessValuesOfBoundedRow
          tokenTable width tokenCount taskBoundary valueBound rowIndex hrow) :=
  Classical.choose_spec (existsTaskListRowWitnessValues
    tokenTable width tokenCount taskBoundary valueBound rowIndex hrow)

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
