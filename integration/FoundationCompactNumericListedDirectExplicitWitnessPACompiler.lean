import integration.FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder
import integration.FoundationCompactNumericListedDirectPredicateMatrixHybridCompiler
import integration.FoundationCompactNumericListedDirectBoundedProofWitness
import integration.FoundationCompactNumericListedDirectBoundedWitnessBounds

/-!
# Explicit-witness formula alignment for the direct listed predicate

This module aligns the twenty coordinates of a bounded direct witness with the
twenty existential binders of the direct proof formula.  The payload compiler
is kept in a separate module so this expensive formula alignment can be cached.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectExplicitWitnessPACompiler

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactListedCertifiedVerifier
open FoundationCompactNumericListedPublicVerifier
open FoundationCompactNumericListedDirectProofPredicate
open FoundationCompactNumericListedAcceptedDirectPACompiler
open FoundationCompactNumericListedDirectPredicateMatrixClosedInstance
open FoundationCompactNumericListedDirectPredicateMatrixHybridCompiler
open FoundationCompactNumericListedDirectBoundedProofWitness
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder
open FoundationCompactPAExplicitWitnessHybridSigmaOneFormulaBuilder.ExplicitWitnessHybridSigmaOnePayload
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof

private def zeroValuation : Nat -> Nat := fun _ => 0

private theorem subst_bShift_tail_app
    {n : Nat}
    (values : Fin (n + 1) ->
      LO.FirstOrder.ArithmeticSemiterm Nat 0)
    (term : LO.FirstOrder.ArithmeticSemiterm Nat n) :
    Rew.subst values (Rew.bShift term) =
      Rew.subst (fun index : Fin n => values index.succ) term := by
  rw [← Rew.comp_app]
  apply Rew.ext'
  apply Rew.ext
  · intro index
    simp [Rew.comp_app]
  · intro index
    simp [Rew.comp_app]

/-- The direct witness fields, in the outer-to-inner order of the proof formula. -/
def directExplicitWitnessValues
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    Fin 20 -> Nat :=
  ![witness.proofCode,
    witness.inputTokenCount,
    witness.inputTable,
    witness.inputOffsetTable,
    witness.inputWidth,
    witness.sourceTable,
    witness.sourceWidth,
    witness.sourceTokenCount,
    witness.proofStart,
    witness.proofFinish,
    witness.certificateStart,
    witness.certificateFinish,
    witness.split,
    witness.traceWidth,
    witness.traceTable,
    witness.traceValueBound,
    witness.formulaTokenCount,
    witness.formulaTable,
    witness.formulaOffsetTable,
    witness.formulaWidth]

/-- The 22-coordinate body used by the quoted direct proof formula. -/
def compactListedPADirectRawWitnessMatrix :
    LO.FirstOrder.ArithmeticSemiformula Empty 22 :=
  compactNumericListedDirectPredicateMatrixDef.val ⇜
    ![(#20 : LO.FirstOrder.ArithmeticSemiterm Empty 22),
      #21, #19, #18, #17, #16, #15, #14, #13, #12, #11, #10,
      #9, #8, #7, #6, #5, #4, #3, #2, #1, #0]

theorem compactListedPADirectProofFormula_eq_rawWitnessExsItr :
    compactListedPADirectProofFormula.val =
      ∃⁰^[20] compactListedPADirectRawWitnessMatrix := by
  rfl

/-- The direct matrix after fixing the two public coordinates, before closing
the twenty witness coordinates.  `qpow 20` carries the public substitution
under exactly the twenty existential binders without traversing the matrix. -/
def compactListedPADirectOpenWitnessMatrix
    (bound formulaCode : Nat) :
    LO.FirstOrder.ArithmeticSemiformula Nat 20 :=
  (Rew.subst
      ![shortBinaryNumeralTerm bound,
        shortBinaryNumeralTerm formulaCode]).qpow 20 ▹
    (Rewriting.emb (ξ := Nat) compactListedPADirectRawWitnessMatrix)

set_option maxHeartbeats 12000000 in
theorem compactListedPADirectProofInstance_eq_openWitnessExsClosure
    (bound formulaCode : Nat) :
    compactListedPADirectProofInstance bound formulaCode =
      ∃⁰* compactListedPADirectOpenWitnessMatrix bound formulaCode := by
  unfold compactListedPADirectProofInstance
  rw [compactListedPADirectProofFormula_eq_rawWitnessExsItr]
  simp [compactListedPADirectOpenWitnessMatrix]
  rfl

/-- Simultaneously instantiate the open matrix.  The substitution vector is
reverse to the outer binder order because de Bruijn coordinate zero is the
innermost remaining witness. -/
def compactListedPADirectOpenWitnessMatrixClosed
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    LO.FirstOrder.ArithmeticProposition :=
  compactListedPADirectOpenWitnessMatrix bound formulaCode ⇜
    ![shortBinaryNumeralTerm witness.formulaWidth,
      shortBinaryNumeralTerm witness.formulaOffsetTable,
      shortBinaryNumeralTerm witness.formulaTable,
      shortBinaryNumeralTerm witness.formulaTokenCount,
      shortBinaryNumeralTerm witness.traceValueBound,
      shortBinaryNumeralTerm witness.traceTable,
      shortBinaryNumeralTerm witness.traceWidth,
      shortBinaryNumeralTerm witness.split,
      shortBinaryNumeralTerm witness.certificateFinish,
      shortBinaryNumeralTerm witness.certificateStart,
      shortBinaryNumeralTerm witness.proofFinish,
      shortBinaryNumeralTerm witness.proofStart,
      shortBinaryNumeralTerm witness.sourceTokenCount,
      shortBinaryNumeralTerm witness.sourceWidth,
      shortBinaryNumeralTerm witness.sourceTable,
      shortBinaryNumeralTerm witness.inputWidth,
      shortBinaryNumeralTerm witness.inputOffsetTable,
      shortBinaryNumeralTerm witness.inputTable,
      shortBinaryNumeralTerm witness.inputTokenCount,
      shortBinaryNumeralTerm witness.proofCode]

set_option maxHeartbeats 12000000 in
theorem compactListedPADirectOpenWitnessMatrixClosed_eq_closedInstance
    {bound formulaCode : Nat}
    (witness : CompactListedPADirectWitness bound formulaCode) :
    compactListedPADirectOpenWitnessMatrixClosed witness =
      compactNumericListedDirectPredicateMatrixClosedInstance witness := by
  unfold compactListedPADirectOpenWitnessMatrixClosed
  unfold compactListedPADirectOpenWitnessMatrix
  unfold compactListedPADirectRawWitnessMatrix
  unfold compactNumericListedDirectPredicateMatrixClosedInstance
  simp only [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  ext coordinate
  · fin_cases coordinate <;>
      simp [Rew.comp_app, Rew.qpow, Rew.q,
        subst_bShift_tail_app]
  · exact Empty.elim coordinate

#print axioms compactListedPADirectProofInstance_eq_openWitnessExsClosure
#print axioms compactListedPADirectOpenWitnessMatrixClosed_eq_closedInstance

end FoundationCompactNumericListedDirectExplicitWitnessPACompiler
