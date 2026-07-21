import integration.FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition
import integration.FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate

/-!
# Strict closed decomposition of the accepted trace table

This file exposes the six exact conjuncts of the accepted-trace formula while
retaining the original `fuelTerm`.  It is formula alignment only; each
component receives its own explicit checked certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition

open FoundationCompactBinaryNumeralTerm
open FoundationCompactNumericListedDirectVerifierAcceptedPayloadMatrixClosedDecomposition
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierAcceptedTraceFormula
open FoundationCompactNumericListedDirectVerifierInitialWitnessTableRowFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableAdjacencyFormula
open FoundationCompactNumericListedDirectVerifierStepWitnessTableFormula
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler

def compactNumericVerifierAcceptedTraceExponentialClosedFormula
    (tableWidth valueBound : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat) expDef.val) ⇜
    ![shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm tableWidth]

def compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
    (tableWidth table valueBound : Nat) (fuelTerm : ValuationTerm) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableBoundedGraphDef.val) ⇜
    ![shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm table,
      fuelTerm,
      shortBinaryNumeralTerm valueBound]

def compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
    (tableWidth table valueBound : Nat) (fuelTerm : ValuationTerm) :
    ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierStepWitnessTableRowsAdjacentDef.val) ⇜
    ![shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm table,
      fuelTerm,
      shortBinaryNumeralTerm valueBound]

def compactNumericVerifierInitialWitnessTableRowClosedFormula
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat) : ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierInitialWitnessTableRowDef.val) ⇜
    ![shortBinaryNumeralTerm tableWidth,
      shortBinaryNumeralTerm table,
      shortBinaryNumeralTerm valueBound,
      (‘0’ : ValuationTerm),
      shortBinaryNumeralTerm proofTable,
      shortBinaryNumeralTerm proofWidth,
      shortBinaryNumeralTerm proofTokenCount,
      shortBinaryNumeralTerm proofStart,
      shortBinaryNumeralTerm proofFinish,
      shortBinaryNumeralTerm certificateTable,
      shortBinaryNumeralTerm certificateWidth,
      shortBinaryNumeralTerm certificateTokenCount,
      shortBinaryNumeralTerm certificateStart,
      shortBinaryNumeralTerm certificateFinish]

def compactNumericVerifierAcceptedTraceTableDecomposedFormula
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (fuelTerm : ValuationTerm) : ArithmeticProposition :=
  compactNumericVerifierAcceptedTraceExponentialClosedFormula
      tableWidth valueBound ⋏
    (“0 < !!fuelTerm” ⋏
      (compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
          tableWidth table valueBound fuelTerm ⋏
        (compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
            tableWidth table valueBound fuelTerm ⋏
          (compactNumericVerifierInitialWitnessTableRowClosedFormula
              tableWidth table valueBound
              proofTable proofWidth proofTokenCount proofStart proofFinish
              certificateTable certificateWidth certificateTokenCount
              certificateStart certificateFinish ⋏
            compactNumericVerifierAcceptedTraceFinalAtValuationFormula
              tableWidth table fuelTerm))))

theorem compactNumericVerifierAcceptedTraceTableClosedFormula_eq_decomposed
    (tableWidth table valueBound
      proofTable proofWidth proofTokenCount proofStart proofFinish
      certificateTable certificateWidth certificateTokenCount
      certificateStart certificateFinish : Nat)
    (fuelTerm : ValuationTerm) :
    compactNumericVerifierAcceptedTraceTableClosedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish fuelTerm =
      compactNumericVerifierAcceptedTraceTableDecomposedFormula
        tableWidth table valueBound
        proofTable proofWidth proofTokenCount proofStart proofFinish
        certificateTable certificateWidth certificateTokenCount
        certificateStart certificateFinish fuelTerm := by
  unfold compactNumericVerifierAcceptedTraceTableClosedFormula
  unfold compactNumericVerifierAcceptedTraceTableDecomposedFormula
  unfold compactNumericVerifierAcceptedTraceExponentialClosedFormula
  unfold compactNumericVerifierStepWitnessTableBoundedGraphAtValuationFormula
  unfold compactNumericVerifierStepWitnessTableRowsAdjacentAtValuationFormula
  unfold compactNumericVerifierInitialWitnessTableRowClosedFormula
  unfold compactNumericVerifierAcceptedTraceTableDef
  simp [← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;> simp [Rew.comp_app]
    · intro index
      exact Empty.elim index
  · unfold compactNumericVerifierAcceptedTraceFinalAtValuationFormula
    unfold compactNumericVerifierAcceptedTraceFinalAtTermFormula
    simp [compactNumericVerifierAcceptedTraceFinalDef,
      LO.FirstOrder.Semiformula.bexsLT, LO.FirstOrder.bexs,
      ← TransitiveRewriting.comp_app]
    constructor
    · change
        ((Rew.subst ![shortBinaryNumeralTerm tableWidth,
          shortBinaryNumeralTerm table,
          shortBinaryNumeralTerm valueBound, fuelTerm,
          shortBinaryNumeralTerm proofTable,
          shortBinaryNumeralTerm proofWidth,
          shortBinaryNumeralTerm proofTokenCount,
          shortBinaryNumeralTerm proofStart,
          shortBinaryNumeralTerm proofFinish,
          shortBinaryNumeralTerm certificateTable,
          shortBinaryNumeralTerm certificateWidth,
          shortBinaryNumeralTerm certificateTokenCount,
          shortBinaryNumeralTerm certificateStart,
          shortBinaryNumeralTerm certificateFinish]).comp Rew.emb).q
            (#((3 : Fin 14).succ)) = Rew.bShift fuelTerm
      rw [Rew.q_bvar_succ]
      simp [Rew.comp_app]
    · apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        cases coordinate using Fin.cases with
        | zero =>
            simp only [Rew.comp_app, Rew.subst_bvar]
            change
              ((Rew.subst ![shortBinaryNumeralTerm tableWidth,
                shortBinaryNumeralTerm table,
                shortBinaryNumeralTerm valueBound, fuelTerm,
                shortBinaryNumeralTerm proofTable,
                shortBinaryNumeralTerm proofWidth,
                shortBinaryNumeralTerm proofTokenCount,
                shortBinaryNumeralTerm proofStart,
                shortBinaryNumeralTerm proofFinish,
                shortBinaryNumeralTerm certificateTable,
                shortBinaryNumeralTerm certificateWidth,
                shortBinaryNumeralTerm certificateTokenCount,
                shortBinaryNumeralTerm certificateStart,
                shortBinaryNumeralTerm certificateFinish]).comp Rew.emb).q
                  (#((0 : Fin 14).succ)) =
                (Rew.subst ![shortBinaryNumeralTerm tableWidth,
                  shortBinaryNumeralTerm table, fuelTerm]).q
                  (#((0 : Fin 3).succ))
            rw [Rew.q_bvar_succ, Rew.q_bvar_succ]
            simp [Rew.comp_app]
        | succ coordinate =>
            cases coordinate using Fin.cases with
            | zero =>
                simp only [Rew.comp_app, Rew.subst_bvar]
                change
                  ((Rew.subst ![shortBinaryNumeralTerm tableWidth,
                    shortBinaryNumeralTerm table,
                    shortBinaryNumeralTerm valueBound, fuelTerm,
                    shortBinaryNumeralTerm proofTable,
                    shortBinaryNumeralTerm proofWidth,
                    shortBinaryNumeralTerm proofTokenCount,
                    shortBinaryNumeralTerm proofStart,
                    shortBinaryNumeralTerm proofFinish,
                    shortBinaryNumeralTerm certificateTable,
                    shortBinaryNumeralTerm certificateWidth,
                    shortBinaryNumeralTerm certificateTokenCount,
                    shortBinaryNumeralTerm certificateStart,
                    shortBinaryNumeralTerm certificateFinish]).comp Rew.emb).q
                      (#((1 : Fin 14).succ)) =
                    (Rew.subst ![shortBinaryNumeralTerm tableWidth,
                      shortBinaryNumeralTerm table, fuelTerm]).q
                      (#((1 : Fin 3).succ))
                rw [Rew.q_bvar_succ, Rew.q_bvar_succ]
                simp [Rew.comp_app]
            | succ coordinate =>
                cases coordinate using Fin.cases with
                | zero =>
                    simp [Rew.comp_app, Rew.subst_bvar,
                      Rew.q_bvar_zero]
                | succ coordinate => exact Fin.elim0 coordinate
      · intro index
        exact Empty.elim index

#print axioms
  compactNumericVerifierAcceptedTraceTableClosedFormula_eq_decomposed

end FoundationCompactNumericListedDirectVerifierAcceptedTraceTableClosedDecomposition
