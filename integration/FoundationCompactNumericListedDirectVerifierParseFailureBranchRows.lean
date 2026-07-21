import integration.FoundationCompactNumericListedDirectVerifierParsePayloadFailureBoundedFormula
import integration.FoundationCompactNumericListedDirectVerifierParseFailureRows

/-!
# One bounded row schema for failed verifier parsing

The parser-failure witness and the state-update rows share one token table and
the exact proof/certificate slice endpoints.  Thus a failure certificate for
one payload cannot justify the transition of a different payload.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureBranchRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureBoundedFormula
open FoundationCompactNumericListedDirectVerifierParseFailureRows

def CompactNumericVerifierParseFailureBranchRows
    (tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) : Prop :=
  CompactNumericParsePayloadFailureBoundedGraph
      tokenTable width tokenCount
      currentStart currentProofFinish
      currentProofFinish currentCertificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound ∧
    CompactNumericVerifierParseFailureRows
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool

def compactNumericVerifierParseFailureBranchRowsDef :
    𝚺₀.Semisentence 38 := .mkSigma
  “tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound.
    !(compactNumericParsePayloadFailureBoundedGraphDef)
      tokenTable width tokenCount
      currentStart currentProofFinish
      currentProofFinish currentCertificateFinish
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound ∧
    !(compactNumericVerifierParseFailureRowsDef)
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool”

def compactNumericVerifierParseFailureBranchRowsEnvironment
    (tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) : Fin 38 → Nat :=
  ![tokenTable, width, tokenCount,
    currentStart, currentProofFinish, currentCertificateFinish,
    currentTaskBoundary, currentTaskCount,
    currentValueBoundary, currentValueCount,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextStart, nextCertificateFinish,
    nextTaskBoundary, nextTaskCount,
    nextValueBoundary, nextValueCount,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    nextStatusTag, nextStatusBool,
    rootStart, rootFinish, proofTag,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag,
    proofEndpointBound, certificateEndpointBound]

@[simp] theorem compactNumericVerifierParseFailureBranchRowsDef_spec
    (tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat) :
    compactNumericVerifierParseFailureBranchRowsDef.val.Evalb
        (compactNumericVerifierParseFailureBranchRowsEnvironment
          tokenTable width tokenCount
          currentStart currentProofFinish currentCertificateFinish
          currentTaskBoundary currentTaskCount
          currentValueBoundary currentValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextStart nextCertificateFinish
          nextTaskBoundary nextTaskCount
          nextValueBoundary nextValueCount
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStatusTag nextStatusBool
          rootStart rootFinish proofTag
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag
          proofEndpointBound certificateEndpointBound) ↔
      CompactNumericVerifierParseFailureBranchRows
        tokenTable width tokenCount
        currentStart currentProofFinish currentCertificateFinish
        currentTaskBoundary currentTaskCount
        currentValueBoundary currentValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextStart nextCertificateFinish
        nextTaskBoundary nextTaskCount
        nextValueBoundary nextValueCount
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStatusTag nextStatusBool
        rootStart rootFinish proofTag
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag
        proofEndpointBound certificateEndpointBound := by
  let env := compactNumericVerifierParseFailureBranchRowsEnvironment
    tokenTable width tokenCount
    currentStart currentProofFinish currentCertificateFinish
    currentTaskBoundary currentTaskCount
    currentValueBoundary currentValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextStart nextCertificateFinish
    nextTaskBoundary nextTaskCount
    nextValueBoundary nextValueCount
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStatusTag nextStatusBool
    rootStart rootFinish proofTag
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag
    proofEndpointBound certificateEndpointBound
  change compactNumericVerifierParseFailureBranchRowsDef.val.Evalb env ↔ _
  have hpayloadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #4, #4, #5, #26, #27, #28,
          #29, #30, #31, #32, #33, #34, #35, #36, #37]) =
        compactNumericParsePayloadFailureBoundedGraphEnvironment
          tokenTable width tokenCount
          currentStart currentProofFinish
          currentProofFinish currentCertificateFinish
          rootStart rootFinish proofTag
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag
          proofEndpointBound certificateEndpointBound := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hrowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 38), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11, #12, #13,
          #14, #15, #16, #17, #18, #19, #20, #21, #22, #23,
          #24, #25]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentCertificateFinish,
          currentTaskBoundary, currentTaskCount,
          currentValueBoundary, currentValueCount,
          currentTaskTableWidth, currentTaskValueBound,
          currentValueTableWidth, currentValueValueBound,
          nextStart, nextCertificateFinish,
          nextTaskBoundary, nextTaskCount,
          nextValueBoundary, nextValueCount,
          nextTaskTableWidth, nextTaskValueBound,
          nextValueTableWidth, nextValueValueBound,
          nextStatusTag, nextStatusBool] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseFailureBranchRowsDef,
    CompactNumericVerifierParseFailureBranchRows,
    hpayloadEnv, hrowsEnv]

theorem compactNumericVerifierParseFailureBranchRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseFailureBranchRowsDef.val := by
  simp [compactNumericVerifierParseFailureBranchRowsDef]

theorem CompactNumericVerifierParseFailureBranchRows.sound
    {tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextProofFinish nextCertificateFinish
      nextTaskBoundary nextValueBoundary
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound : Nat}
    {currentProof currentCertificate nextProof nextCertificate : List Nat}
    {currentTasks nextTasks : List CompactNumericVerifierTask}
    {currentValues nextValues : List CompactNumericChildResult}
    (hrows : CompactNumericVerifierParseFailureBranchRows
      tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentTasks.length
      currentValueBoundary currentValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTasks.length
      nextValueBoundary nextValues.length
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      rootStart rootFinish proofTag
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag
      proofEndpointBound certificateEndpointBound)
    (hcurrentProof : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount currentStart currentProofFinish currentProof)
    (hcurrentCertificate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount currentProofFinish currentCertificateFinish
        currentCertificate)
    (hnextProof : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount nextProofFinish nextCertificateFinish
        nextCertificate)
    (hcurrentTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      currentTaskBoundary currentTasks)
    (hnextTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout tokenTable width tokenCount
      nextTaskBoundary nextTasks)
    (hcurrentValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      currentValueBoundary currentValues)
    (hnextValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
      nextValueBoundary nextValues) :
    compactNumericParsePayload
        ((currentProof, currentCertificate),
          (currentTasks.drop 1, currentValues)) = none ∧
      nextProof = currentProof ∧
      nextCertificate = currentCertificate ∧
      nextTasks = currentTasks.drop 1 ∧
      nextValues = currentValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 1 ∧
      nextStatusBool = compactAdditiveBoolTag false := by
  rcases hrows with ⟨hfailure, hstateRows⟩
  have hparse := hfailure.sound
    (restTasks := currentTasks.drop 1) (values := currentValues)
    hcurrentProof hcurrentCertificate
  have hstate := hstateRows.sound
    hcurrentProof hcurrentCertificate hnextProof hnextCertificate
    hcurrentTaskRows hnextTaskRows hcurrentValueRows hnextValueRows
  exact ⟨hparse, hstate⟩

#print axioms compactNumericVerifierParseFailureBranchRowsDef_spec
#print axioms compactNumericVerifierParseFailureBranchRowsDef_sigmaZero
#print axioms CompactNumericVerifierParseFailureBranchRows.sound

end FoundationCompactNumericListedDirectVerifierParseFailureBranchRows
