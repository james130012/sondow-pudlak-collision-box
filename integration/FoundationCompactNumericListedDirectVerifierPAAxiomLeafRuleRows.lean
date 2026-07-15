import integration.FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck

/-!
# Unified direct PA-axiom leaf rule

The first 184 coordinates are exactly the checked induction-rule schema.
Coordinates 184 and 185 are the proof/certificate tags.  In the fixed branch,
four otherwise inactive induction coordinates carry the fixed certificate's
tag, arity, symbol code, and candidate length.  No extra result predicate is
introduced: both branches use their already proved direct rule-check graphs.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRows

open FoundationCompactNumericListedDirectGuardedInductionSentenceRoute
open FoundationCompactNumericListedDirectSuccIndOpenSubstitutionRoute
open FoundationCompactNumericListedDirectFixedPAAxiomRuleCheck
open FoundationCompactNumericListedDirectInductionPAAxiomRuleCheck

def CompactNumericVerifierPAAxiomLeafRuleRows
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate : CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates)
    (proofTag certificateTag : Nat) : Prop :=
  proofTag = 1 ∧
    certificateTag = 1 ∧
    (CompactAdditiveFixedPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary gammaCount
        candidate.start candidate.finish body.count
        body.start body.finish body.boundary resultBoolValue ∨
      CompactAdditiveInductionPAAxiomRuleCheck
        tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
        axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
        captureOne empty base negatedBase stepZero stepSuccessor
        negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
        quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
        generated candidate depth coordinates)

def compactPAAxiomLeafFixedRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 186 :=
  compactAdditiveFixedPAAxiomRuleCheckDef.val ⇜
    ![(#0 : Semiterm ℒₒᵣ Empty 186), #1, #2, #177, #178,
      #182, #183, #6, #3, #4, #5, #179]

def compactPAAxiomLeafInductionRuleLift :
    LO.FirstOrder.ArithmeticSemisentence 186 :=
  compactAdditiveInductionPAAxiomRuleCheckDef.val ⇜
    (fun index : Fin 184 =>
      (#(Fin.castLE (show 184 ≤ 186 by omega) index) :
        Semiterm ℒₒᵣ Empty 186))

def compactPAAxiomLeafTagsDef :
    LO.FirstOrder.ArithmeticSemisentence 186 :=
  “(#184 = 1 ∧ #185 = 1)”

def compactNumericVerifierPAAxiomLeafRuleRowsDef :
    𝚺₀.Semisentence 186 := .mkSigma
  (compactPAAxiomLeafTagsDef ⋏
    (compactPAAxiomLeafFixedRuleLift ⋎
      compactPAAxiomLeafInductionRuleLift))
  (by
    simp [compactPAAxiomLeafTagsDef,
      compactPAAxiomLeafFixedRuleLift,
      compactPAAxiomLeafInductionRuleLift])

def compactNumericVerifierPAAxiomLeafRuleRowsEnvironment
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate : CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates)
    (proofTag certificateTag : Nat) : Fin 186 → Nat :=
  Matrix.vecAppend rfl
    (compactAdditiveInductionPAAxiomRuleCheckEnvironment
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth axiomTokens body zeroWitness openZeroWitness
      openSuccessorWitness captureOne empty base negatedBase stepZero
      stepSuccessor negatedStepZero stepDisjunction quantifiedStep
      negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
      fvarList depthCapture fixed generated candidate coordinates)
    ![proofTag, certificateTag]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 8192 in
@[simp] theorem compactNumericVerifierPAAxiomLeafRuleRowsDef_spec
    (tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth : Nat)
    (axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
      stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
      innerDisjunction sentence fvarList depthCapture fixed generated
      candidate : CompactNatListRowSlot)
    (coordinates : CompactGuardedInductionSentenceRouteCoordinates)
    (proofTag certificateTag : Nat) :
    compactNumericVerifierPAAxiomLeafRuleRowsDef.val.Evalb
        (compactNumericVerifierPAAxiomLeafRuleRowsEnvironment
          tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
          depth axiomTokens body zeroWitness openZeroWitness
          openSuccessorWitness captureOne empty base negatedBase stepZero
          stepSuccessor negatedStepZero stepDisjunction quantifiedStep
          negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
          fvarList depthCapture fixed generated candidate coordinates
          proofTag certificateTag) ↔
      CompactNumericVerifierPAAxiomLeafRuleRows
        tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
        depth axiomTokens body zeroWitness openZeroWitness
        openSuccessorWitness captureOne empty base negatedBase stepZero
        stepSuccessor negatedStepZero stepDisjunction quantifiedStep
        negatedQuantifiedStep quantifiedFinal innerDisjunction sentence
        fvarList depthCapture fixed generated candidate coordinates
        proofTag certificateTag := by
  let innerEnv := compactAdditiveInductionPAAxiomRuleCheckEnvironment
    tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
    depth axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
    captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
    stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
    innerDisjunction sentence fvarList depthCapture fixed generated candidate
    coordinates
  let env := compactNumericVerifierPAAxiomLeafRuleRowsEnvironment
    tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
    depth axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
    captureOne empty base negatedBase stepZero stepSuccessor negatedStepZero
    stepDisjunction quantifiedStep negatedQuantifiedStep quantifiedFinal
    innerDisjunction sentence fvarList depthCapture fixed generated candidate
    coordinates proofTag certificateTag
  change compactNumericVerifierPAAxiomLeafRuleRowsDef.val.Evalb env ↔ _
  have hinductionEnv :
      (Semiterm.val env Empty.elim ∘
        (fun index : Fin 184 =>
          (#(Fin.castLE (show 184 ≤ 186 by omega) index) :
            Semiterm ℒₒᵣ Empty 186))) = innerEnv := by
    funext coordinate
    simp [env, innerEnv,
      compactNumericVerifierPAAxiomLeafRuleRowsEnvironment,
      Matrix.vecAppend_eq_ite]
  have hfixedEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 186), #1, #2, #177, #178,
          #182, #183, #6, #3, #4, #5, #179]) =
        ![tokenTable, width, tokenCount, gammaBoundary, gammaCount,
          candidate.start, candidate.finish, body.count,
          body.start, body.finish, body.boundary, resultBoolValue] := by
    funext coordinate
    fin_cases coordinate <;>
      simp [env,
        compactNumericVerifierPAAxiomLeafRuleRowsEnvironment,
        compactAdditiveInductionPAAxiomRuleCheckEnvironment,
        compactGuardedInductionSentenceRouteEnvironment,
        Matrix.vecAppend_eq_ite]
  have hfixedSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            ![(#0 : Semiterm ℒₒᵣ Empty 186), #1, #2, #177, #178,
              #182, #183, #6, #3, #4, #5, #179])
          Empty.elim compactAdditiveFixedPAAxiomRuleCheckDef.val ↔
        CompactAdditiveFixedPAAxiomRuleCheck
          tokenTable width tokenCount gammaBoundary gammaCount
          candidate.start candidate.finish body.count
          body.start body.finish body.boundary resultBoolValue := by
    rw [hfixedEnv]
    exact compactAdditiveFixedPAAxiomRuleCheckDef_spec
      tokenTable width tokenCount gammaBoundary gammaCount
      candidate.start candidate.finish body.count
      body.start body.finish body.boundary resultBoolValue
  have hinductionSpec :
      Semiformula.Eval
          (Semiterm.val env Empty.elim ∘
            (fun index : Fin 184 =>
              (#(Fin.castLE (show 184 ≤ 186 by omega) index) :
                Semiterm ℒₒᵣ Empty 186)))
          Empty.elim compactAdditiveInductionPAAxiomRuleCheckDef.val ↔
        CompactAdditiveInductionPAAxiomRuleCheck
          tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
          axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
          captureOne empty base negatedBase stepZero stepSuccessor
          negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
          quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
          generated candidate depth coordinates := by
    rw [hinductionEnv]
    exact compactAdditiveInductionPAAxiomRuleCheckDef_spec
      tokenTable width tokenCount gammaBoundary gammaCount resultBoolValue
      depth axiomTokens body zeroWitness openZeroWitness openSuccessorWitness
      captureOne empty base negatedBase stepZero stepSuccessor
      negatedStepZero stepDisjunction quantifiedStep negatedQuantifiedStep
      quantifiedFinal innerDisjunction sentence fvarList depthCapture fixed
      generated candidate coordinates
  have hproofTag : env 184 = proofTag := by
    simp [env, compactNumericVerifierPAAxiomLeafRuleRowsEnvironment,
      Matrix.vecAppend_eq_ite]
  have hcertificateTag : env 185 = certificateTag := by
    simp [env, compactNumericVerifierPAAxiomLeafRuleRowsEnvironment,
      Matrix.vecAppend_eq_ite]
  simp [compactNumericVerifierPAAxiomLeafRuleRowsDef,
    compactPAAxiomLeafTagsDef,
    compactPAAxiomLeafFixedRuleLift,
    compactPAAxiomLeafInductionRuleLift,
    CompactNumericVerifierPAAxiomLeafRuleRows,
    hfixedSpec, hinductionSpec, hproofTag, hcertificateTag]
  constructor
  · rintro ⟨⟨hproof, hcertificate⟩, hrule⟩
    exact ⟨hproof, hcertificate, hrule⟩
  · rintro ⟨hproof, hcertificate, hrule⟩
    exact ⟨⟨hproof, hcertificate⟩, hrule⟩

set_option maxRecDepth 8192 in
theorem compactNumericVerifierPAAxiomLeafRuleRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierPAAxiomLeafRuleRowsDef.val := by
  exact compactNumericVerifierPAAxiomLeafRuleRowsDef.sigma_prop

#print axioms compactNumericVerifierPAAxiomLeafRuleRowsDef_spec
#print axioms compactNumericVerifierPAAxiomLeafRuleRowsDef_sigmaZero

end FoundationCompactNumericListedDirectVerifierPAAxiomLeafRuleRows
