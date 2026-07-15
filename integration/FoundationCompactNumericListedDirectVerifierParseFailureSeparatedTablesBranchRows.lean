import integration.FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula
import integration.FoundationCompactNumericListedDirectVerifierParseFailureRows

/-!
# One bounded row schema for failed verifier parsing with separated parser tables

The parser-failure graph uses independent proof and certificate parser tables,
while the state-transition rows continue to use the verifier state table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierParsePayloadFailureSeparatedTablesFormula
open FoundationCompactNumericListedDirectVerifierParseFailureRows

def CompactNumericVerifierParseFailureSeparatedTablesBranchRows
    (stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) : Prop :=
  CompactNumericParsePayloadFailureSeparatedTablesGraph
      stateTable stateWidth stateTokenCount
      currentStart currentProofFinish
      currentProofFinish currentCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound ∧
    CompactNumericVerifierParseFailureRows
      stateTable stateWidth stateTokenCount
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

def compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef :
    𝚺₀.Semisentence 48 := .mkSigma
  “stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound.
    !(compactNumericParsePayloadFailureSeparatedTablesGraphDef)
      stateTable stateWidth stateTokenCount
      currentStart currentProofFinish
      currentProofFinish currentCertificateFinish
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound ∧
    !(compactNumericVerifierParseFailureRowsDef)
      stateTable stateWidth stateTokenCount
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

def compactNumericVerifierParseFailureSeparatedTablesBranchRowsEnvironment
    (stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) : Fin 48 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
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
    proofTable, proofWidth, proofTokenCount, proofInputStart, proofInputFinish,
    rootStart, rootFinish, proofTag, proofEndpointBound,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateInputStart, certificateInputFinish,
    axiomStart, axiomFinish, formulaStart, formulaFinish,
    suffixStart, suffixFinish, certificateTag, certificateEndpointBound]

@[simp] theorem compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef_spec
    (stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat) :
    compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef.val.Evalb
        (compactNumericVerifierParseFailureSeparatedTablesBranchRowsEnvironment
          stateTable stateWidth stateTokenCount
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
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound) ↔
      CompactNumericVerifierParseFailureSeparatedTablesBranchRows
        stateTable stateWidth stateTokenCount
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
        proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
        rootStart rootFinish proofTag proofEndpointBound
        certificateTable certificateWidth certificateTokenCount
        certificateInputStart certificateInputFinish
        axiomStart axiomFinish formulaStart formulaFinish
        suffixStart suffixFinish certificateTag certificateEndpointBound := by
  let env := compactNumericVerifierParseFailureSeparatedTablesBranchRowsEnvironment
    stateTable stateWidth stateTokenCount
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
    proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
    rootStart rootFinish proofTag proofEndpointBound
    certificateTable certificateWidth certificateTokenCount
    certificateInputStart certificateInputFinish
    axiomStart axiomFinish formulaStart formulaFinish
    suffixStart suffixFinish certificateTag certificateEndpointBound
  change compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef.val.Evalb env ↔ _
  have hpayloadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 48), #1, #2, #3, #4, #4, #5,
          #26, #27, #28, #29, #30, #31, #32, #33, #34,
          #35, #36, #37, #38, #39, #40, #41, #42, #43, #44, #45, #46, #47]) =
        compactNumericParsePayloadFailureSeparatedTablesGraphEnvironment
          stateTable stateWidth stateTokenCount
          currentStart currentProofFinish
          currentProofFinish currentCertificateFinish
          proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
          rootStart rootFinish proofTag proofEndpointBound
          certificateTable certificateWidth certificateTokenCount
          certificateInputStart certificateInputFinish
          axiomStart axiomFinish formulaStart formulaFinish
          suffixStart suffixFinish certificateTag certificateEndpointBound := by
    funext coordinate
    set_option maxRecDepth 10000 in
      fin_cases coordinate <;> rfl
  have hrowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 48), #1, #2,
          #3, #5, #6, #7, #8, #9, #10, #11, #12, #13,
          #14, #15, #16, #17, #18, #19, #20, #21, #22, #23,
          #24, #25]) =
        ![stateTable, stateWidth, stateTokenCount,
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
    set_option maxRecDepth 10000 in
      fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef,
    CompactNumericVerifierParseFailureSeparatedTablesBranchRows,
    hpayloadEnv, hrowsEnv]

theorem compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef.val := by
  simp [compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef]

theorem CompactNumericVerifierParseFailureSeparatedTablesBranchRows.sound
    {stateTable stateWidth stateTokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextProofFinish nextCertificateFinish
      nextTaskBoundary nextValueBoundary
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound : Nat}
    {currentProof currentCertificate nextProof nextCertificate : List Nat}
    {currentTasks nextTasks : List CompactNumericVerifierTask}
    {currentValues nextValues : List CompactNumericChildResult}
    (hrows : CompactNumericVerifierParseFailureSeparatedTablesBranchRows
      stateTable stateWidth stateTokenCount
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
      proofTable proofWidth proofTokenCount proofInputStart proofInputFinish
      rootStart rootFinish proofTag proofEndpointBound
      certificateTable certificateWidth certificateTokenCount
      certificateInputStart certificateInputFinish
      axiomStart axiomFinish formulaStart formulaFinish
      suffixStart suffixFinish certificateTag certificateEndpointBound)
    (hcurrentProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount currentStart currentProofFinish currentProof)
    (hcurrentCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount currentProofFinish currentCertificateFinish currentCertificate)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish nextCertificate)
    (hcurrentTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout stateTable stateWidth stateTokenCount
      currentTaskBoundary currentTasks)
    (hnextTaskRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericVerifierTaskDirectLayout stateTable stateWidth stateTokenCount
      nextTaskBoundary nextTasks)
    (hcurrentValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout stateTable stateWidth stateTokenCount
      currentValueBoundary currentValues)
    (hnextValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout stateTable stateWidth stateTokenCount
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

#print axioms compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef_spec
#print axioms compactNumericVerifierParseFailureSeparatedTablesBranchRowsDef_sigmaZero
#print axioms CompactNumericVerifierParseFailureSeparatedTablesBranchRows.sound

end FoundationCompactNumericListedDirectVerifierParseFailureSeparatedTablesBranchRows
