import integration.FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
import integration.FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge

/-!
# Exact accepted final row in the verifier-step witness table

Columns 36 and 38 of the selected row are the next-state option tag and
Boolean payload.  Both cells are fixed directly to `1`.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectVerifierStepFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTable
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormulaBridge
open FoundationCompactNumericListedDirectVerifierFinalEnvironmentFormula

def CompactNumericVerifierAcceptedWitnessTableRow
    (tableWidth table rowIndex : Nat) : Prop :=
  CompactFixedWidthEntry table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + 36) 1 ∧
    CompactFixedWidthEntry table tableWidth
      (rowIndex * compactNumericVerifierStepWitnessColumnCount + 38) 1

def compactNumericVerifierAcceptedWitnessTableRowDef :
    HierarchySymbol.sigmaZero.Semisentence 3 := .mkSigma
  “tableWidth table rowIndex.
    !(compactFixedWidthEntryDef)
      table tableWidth
      (rowIndex * 429 + 36) 1 ∧
    !(compactFixedWidthEntryDef)
      table tableWidth
      (rowIndex * 429 + 38) 1”
  (by simp)

@[simp] theorem compactNumericVerifierAcceptedWitnessTableRowDef_spec
    (tableWidth table rowIndex : Nat) :
    compactNumericVerifierAcceptedWitnessTableRowDef.val.Evalb
        ![tableWidth, table, rowIndex] ↔
      CompactNumericVerifierAcceptedWitnessTableRow
        tableWidth table rowIndex := by
  simp [compactNumericVerifierAcceptedWitnessTableRowDef,
    CompactNumericVerifierAcceptedWitnessTableRow,
    compactNumericVerifierStepWitnessColumnCount]

theorem compactNumericVerifierAcceptedWitnessTableRowDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierAcceptedWitnessTableRowDef.val :=
  compactNumericVerifierAcceptedWitnessTableRowDef.sigma_prop

theorem CompactNumericVerifierAcceptedWitnessTableRow.to_environment
    {tableWidth table valueBound rowIndex : Nat}
    (hbounded : CompactNumericVerifierStepWitnessTableBoundedRow
      tableWidth table valueBound rowIndex)
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex) :
    ∃ environment : Fin 429 -> Nat,
      compactNumericVerifierStepGraphDef.val.Evalb environment ∧
        CompactNumericVerifierAcceptedEnvironment environment := by
  rcases hbounded with ⟨environment, _hbound, hentries, hformula⟩
  have htag : environment 36 = 1 :=
    (CompactFixedWidthEntry.value_eq_tableValue (hentries 36)).trans
      (CompactFixedWidthEntry.value_eq_tableValue haccepted.1).symm
  have hbool : environment 38 = 1 :=
    (CompactFixedWidthEntry.value_eq_tableValue (hentries 38)).trans
      (CompactFixedWidthEntry.value_eq_tableValue haccepted.2).symm
  exact ⟨environment, hformula, htag, hbool⟩

theorem CompactNumericVerifierAcceptedEnvironment.to_witnessTableRow
    {tableWidth table rowIndex : Nat}
    {environment : Fin 429 -> Nat}
    (hentries : ∀ coordinate,
      CompactFixedWidthEntry table tableWidth
        (rowIndex * compactNumericVerifierStepWitnessColumnCount + coordinate.val)
        (environment coordinate))
    (haccepted : CompactNumericVerifierAcceptedEnvironment environment) :
  CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex := by
  constructor
  · have hentry := hentries (36 : Fin 429)
    rw [haccepted.1] at hentry
    convert hentry using 1 <;> norm_num
  · have hentry := hentries (38 : Fin 429)
    rw [haccepted.2] at hentry
    convert hentry using 1 <;> norm_num

theorem CompactNumericVerifierAcceptedWitnessTableRow.canonical_environment
    {tableWidth table rowIndex : Nat}
    (haccepted : CompactNumericVerifierAcceptedWitnessTableRow
      tableWidth table rowIndex) :
    CompactNumericVerifierAcceptedEnvironment
      (compactNumericVerifierStepWitnessTableFormulaEnvironment
        tableWidth table rowIndex) := by
  constructor
  · change compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table rowIndex 36 = 1
    exact
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
        haccepted.1).symm
  · change compactNumericVerifierStepWitnessTableColumnValue
      tableWidth table rowIndex 38 = 1
    exact
      (CompactFixedWidthEntry.value_eq_stepWitnessTableColumnValue
        haccepted.2).symm

#print axioms compactNumericVerifierAcceptedWitnessTableRowDef_spec
#print axioms compactNumericVerifierAcceptedWitnessTableRowDef_sigmaZero
#print axioms CompactNumericVerifierAcceptedWitnessTableRow.to_environment
#print axioms CompactNumericVerifierAcceptedEnvironment.to_witnessTableRow
#print axioms
  CompactNumericVerifierAcceptedWitnessTableRow.canonical_environment

end FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula
