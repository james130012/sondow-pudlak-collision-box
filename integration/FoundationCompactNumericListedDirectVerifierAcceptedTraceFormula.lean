import integration.FoundationCompactNumericListedDirectVerifierCheckedTraceWitnessTable
import integration.FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
import integration.FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula

/-!
# Complete bounded arithmetic formula for an accepted verifier trace

One fixed-width table stores `fuel` complete 429-column step environments.
The formula checks every step, every adjacent-state join, the exact public
initial state, and an accepted next state in the last row.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierFinalWitnessTableRowFormula

def CompactNumericVerifierAcceptedTraceTable
    (tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : Prop :=
  valueBound = 2 ^ tableWidth ∧
    0 < fuel ∧
    CompactNumericVerifierStepWitnessTableBoundedGraph
      tableWidth table fuel valueBound ∧
    CompactNumericVerifierStepWitnessTableRowsAdjacent
      tableWidth table fuel valueBound ∧
    CompactNumericVerifierInitialWitnessTableRow
      tableWidth table valueBound 0
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish ∧
    ∃ lastRow < fuel,
      lastRow + 1 = fuel ∧
      CompactNumericVerifierAcceptedWitnessTableRow
        tableWidth table lastRow

def compactNumericVerifierAcceptedTraceTableDef :
    HierarchySymbol.sigmaZero.Semisentence 14 := .mkSigma
  “tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish.
    !expDef valueBound tableWidth ∧
    0 < fuel ∧
    !(compactNumericVerifierStepWitnessTableBoundedGraphDef)
      tableWidth table fuel valueBound ∧
    !(compactNumericVerifierStepWitnessTableRowsAdjacentDef)
      tableWidth table fuel valueBound ∧
    !(compactNumericVerifierInitialWitnessTableRowDef)
      tableWidth table valueBound 0
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish ∧
    ∃ lastRow < fuel,
      lastRow + 1 = fuel ∧
      !(compactNumericVerifierAcceptedWitnessTableRowDef)
        tableWidth table lastRow”
  (by simp)

@[simp] theorem compactNumericVerifierAcceptedTraceTableDef_spec
    (tableWidth table valueBound fuel
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) :
    compactNumericVerifierAcceptedTraceTableDef.val.Evalb
        ![tableWidth, table, valueBound, fuel,
          proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateStart, certificateFinish] ↔
      CompactNumericVerifierAcceptedTraceTable
        tableWidth table valueBound fuel
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish := by
  let env : Fin 14 -> Nat :=
    ![tableWidth, table, valueBound, fuel,
      proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
      certificateTable, certificateWidth, certificateTokenCount,
      certificateStart, certificateFinish]
  change compactNumericVerifierAcceptedTraceTableDef.val.Evalb env ↔ _
  have hinitialEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2,
          (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 14),
          #4, #5, #6, #7, #8, #9, #10, #11, #12, #13]) =
        ![tableWidth, table, valueBound, 0,
          proofTable, proofWidth, proofTokenCount, proofStart, proofFinish,
          certificateTable, certificateWidth, certificateTokenCount,
          certificateStart, certificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hinitial :
      (Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 14), #1, #2,
              (↑(0 : Nat) : Semiterm ℒₒᵣ Empty 14),
              #4, #5, #6, #7, #8, #9, #10, #11, #12, #13])
          Empty.elim)
          compactNumericVerifierInitialWitnessTableRowDef.val ↔
        CompactNumericVerifierInitialWitnessTableRow
          tableWidth table valueBound 0
          proofTable proofWidth proofTokenCount proofStart proofFinish
          certificateTable certificateWidth certificateTokenCount
          certificateStart certificateFinish := by
    rw [hinitialEnv]
    exact compactNumericVerifierInitialWitnessTableRowDef_spec
      tableWidth table valueBound 0
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish
  simp [compactNumericVerifierAcceptedTraceTableDef,
    CompactNumericVerifierAcceptedTraceTable, hinitial, env]

theorem compactNumericVerifierAcceptedTraceTableDef_sigmaZero :
    Hierarchy Polarity.sigma 0
      compactNumericVerifierAcceptedTraceTableDef.val :=
  compactNumericVerifierAcceptedTraceTableDef.sigma_prop

#print axioms compactNumericVerifierAcceptedTraceTableDef_spec
#print axioms compactNumericVerifierAcceptedTraceTableDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
