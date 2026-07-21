import integration.FoundationCompactNumericListedAcceptedDirectPACompiler

/-!
# Closed direct-predicate matrix instances

Every coordinate of a direct listed-PA witness is instantiated by its short
binary numeral.  This exposes the quantifier-free matrix itself as a closed
arithmetic proposition, independently of the surrounding Sigma-one witness
quantifiers.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectPredicateMatrixClosedInstance

open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedAcceptedDirectPACompiler
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler

def compactNumericListedDirectPredicateMatrixClosedInstance
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    LO.FirstOrder.ArithmeticProposition :=
  (Rewriting.emb (ξ := Nat)
      compactNumericListedDirectPredicateMatrixDef.val) ⇜
    ![shortBinaryNumeralTerm bound,
      shortBinaryNumeralTerm formulaCode,
      shortBinaryNumeralTerm witness.proofCode,
      shortBinaryNumeralTerm witness.inputTokenCount,
      shortBinaryNumeralTerm witness.inputTable,
      shortBinaryNumeralTerm witness.inputOffsetTable,
      shortBinaryNumeralTerm witness.inputWidth,
      shortBinaryNumeralTerm witness.sourceTable,
      shortBinaryNumeralTerm witness.sourceWidth,
      shortBinaryNumeralTerm witness.sourceTokenCount,
      shortBinaryNumeralTerm witness.proofStart,
      shortBinaryNumeralTerm witness.proofFinish,
      shortBinaryNumeralTerm witness.certificateStart,
      shortBinaryNumeralTerm witness.certificateFinish,
      shortBinaryNumeralTerm witness.split,
      shortBinaryNumeralTerm witness.traceWidth,
      shortBinaryNumeralTerm witness.traceTable,
      shortBinaryNumeralTerm witness.traceValueBound,
      shortBinaryNumeralTerm witness.formulaTokenCount,
      shortBinaryNumeralTerm witness.formulaTable,
      shortBinaryNumeralTerm witness.formulaOffsetTable,
      shortBinaryNumeralTerm witness.formulaWidth]

theorem compactNumericListedDirectPredicateMatrixClosedInstance_sigmaZero
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    Hierarchy Polarity.sigma 0
      (compactNumericListedDirectPredicateMatrixClosedInstance witness) := by
  exact
    (compactNumericListedDirectPredicateMatrixDef_sigmaZero.rew Rew.emb).rew
      (Rew.subst
        ![shortBinaryNumeralTerm bound,
          shortBinaryNumeralTerm formulaCode,
          shortBinaryNumeralTerm witness.proofCode,
          shortBinaryNumeralTerm witness.inputTokenCount,
          shortBinaryNumeralTerm witness.inputTable,
          shortBinaryNumeralTerm witness.inputOffsetTable,
          shortBinaryNumeralTerm witness.inputWidth,
          shortBinaryNumeralTerm witness.sourceTable,
          shortBinaryNumeralTerm witness.sourceWidth,
          shortBinaryNumeralTerm witness.sourceTokenCount,
          shortBinaryNumeralTerm witness.proofStart,
          shortBinaryNumeralTerm witness.proofFinish,
          shortBinaryNumeralTerm witness.certificateStart,
          shortBinaryNumeralTerm witness.certificateFinish,
          shortBinaryNumeralTerm witness.split,
          shortBinaryNumeralTerm witness.traceWidth,
          shortBinaryNumeralTerm witness.traceTable,
          shortBinaryNumeralTerm witness.traceValueBound,
          shortBinaryNumeralTerm witness.formulaTokenCount,
          shortBinaryNumeralTerm witness.formulaTable,
          shortBinaryNumeralTerm witness.formulaOffsetTable,
          shortBinaryNumeralTerm witness.formulaWidth])

theorem
    compactNumericListedDirectPredicateMatrixClosedInstance_freeVariables_eq_empty
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    (compactNumericListedDirectPredicateMatrixClosedInstance
      witness).freeVariables = ∅ := by
  exact embeddedClosedSubstitution_freeVariables_eq_empty
    compactNumericListedDirectPredicateMatrixDef.val
    ![shortBinaryNumeralTerm bound,
      shortBinaryNumeralTerm formulaCode,
      shortBinaryNumeralTerm witness.proofCode,
      shortBinaryNumeralTerm witness.inputTokenCount,
      shortBinaryNumeralTerm witness.inputTable,
      shortBinaryNumeralTerm witness.inputOffsetTable,
      shortBinaryNumeralTerm witness.inputWidth,
      shortBinaryNumeralTerm witness.sourceTable,
      shortBinaryNumeralTerm witness.sourceWidth,
      shortBinaryNumeralTerm witness.sourceTokenCount,
      shortBinaryNumeralTerm witness.proofStart,
      shortBinaryNumeralTerm witness.proofFinish,
      shortBinaryNumeralTerm witness.certificateStart,
      shortBinaryNumeralTerm witness.certificateFinish,
      shortBinaryNumeralTerm witness.split,
      shortBinaryNumeralTerm witness.traceWidth,
      shortBinaryNumeralTerm witness.traceTable,
      shortBinaryNumeralTerm witness.traceValueBound,
      shortBinaryNumeralTerm witness.formulaTokenCount,
      shortBinaryNumeralTerm witness.formulaTable,
      shortBinaryNumeralTerm witness.formulaOffsetTable,
      shortBinaryNumeralTerm witness.formulaWidth]
    (by
      intro coordinate
      fin_cases coordinate <;>
        exact shortBinaryNumeralTerm_freeVariables_eq_empty _)

theorem compactNumericListedDirectPredicateMatrixClosedInstance_truth
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    formulaValue (fun _ => 0)
      (compactNumericListedDirectPredicateMatrixClosedInstance witness) := by
  unfold compactNumericListedDirectPredicateMatrixClosedInstance formulaValue
  rw [LO.FirstOrder.Semiformula.eval_substs]
  have hvalues :
      (LO.FirstOrder.Semiterm.val ![] (fun _ => 0) ∘
        ![shortBinaryNumeralTerm bound,
          shortBinaryNumeralTerm formulaCode,
          shortBinaryNumeralTerm witness.proofCode,
          shortBinaryNumeralTerm witness.inputTokenCount,
          shortBinaryNumeralTerm witness.inputTable,
          shortBinaryNumeralTerm witness.inputOffsetTable,
          shortBinaryNumeralTerm witness.inputWidth,
          shortBinaryNumeralTerm witness.sourceTable,
          shortBinaryNumeralTerm witness.sourceWidth,
          shortBinaryNumeralTerm witness.sourceTokenCount,
          shortBinaryNumeralTerm witness.proofStart,
          shortBinaryNumeralTerm witness.proofFinish,
          shortBinaryNumeralTerm witness.certificateStart,
          shortBinaryNumeralTerm witness.certificateFinish,
          shortBinaryNumeralTerm witness.split,
          shortBinaryNumeralTerm witness.traceWidth,
          shortBinaryNumeralTerm witness.traceTable,
          shortBinaryNumeralTerm witness.traceValueBound,
          shortBinaryNumeralTerm witness.formulaTokenCount,
          shortBinaryNumeralTerm witness.formulaTable,
          shortBinaryNumeralTerm witness.formulaOffsetTable,
          shortBinaryNumeralTerm witness.formulaWidth]) =
        ![bound, formulaCode, witness.proofCode,
          witness.inputTokenCount, witness.inputTable,
          witness.inputOffsetTable, witness.inputWidth,
          witness.sourceTable, witness.sourceWidth, witness.sourceTokenCount,
          witness.proofStart, witness.proofFinish,
          witness.certificateStart, witness.certificateFinish, witness.split,
          witness.traceWidth, witness.traceTable, witness.traceValueBound,
          witness.formulaTokenCount, witness.formulaTable,
          witness.formulaOffsetTable, witness.formulaWidth] := by
    funext coordinate
    fin_cases coordinate <;>
      exact termValue_shortBinaryNumeralTerm (fun _ => 0) _
  rw [hvalues, LO.FirstOrder.Semiformula.eval_emb]
  exact
    (compactNumericListedDirectPredicateMatrixDef_spec
      bound formulaCode witness.proofCode
      witness.inputTokenCount witness.inputTable witness.inputOffsetTable
      witness.inputWidth witness.sourceTable witness.sourceWidth
      witness.sourceTokenCount witness.proofStart witness.proofFinish
      witness.certificateStart witness.certificateFinish witness.split
      witness.traceWidth witness.traceTable witness.traceValueBound
      witness.formulaTokenCount witness.formulaTable witness.formulaOffsetTable
      witness.formulaWidth).2 witness.matrix

#print axioms compactNumericListedDirectPredicateMatrixClosedInstance_sigmaZero
#print axioms compactNumericListedDirectPredicateMatrixClosedInstance_freeVariables_eq_empty
#print axioms compactNumericListedDirectPredicateMatrixClosedInstance_truth
