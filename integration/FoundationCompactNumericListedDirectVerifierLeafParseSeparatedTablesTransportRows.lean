import integration.FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRows

/-!
# Arithmetic transport rows for a parsed verifier leaf

This reusable graph records the table transports and stack update induced by a
leaf result.  It intentionally does not include parse success or a semantic
soundness statement.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows

open FoundationCompactNumericListedDirectChildResultBoundedRowExposedFormula
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectVerifierLeafParseStackRows

def CompactNumericVerifierLeafParseSeparatedTablesTransportRows
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
      stateTable stateWidth stateTokenCount nextStart nextProofFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish ∧
    CompactNumericChildResultBoundedRowExposed
      stateTable stateWidth stateTokenCount targetValueBoundary nextValueValueBound 0
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize ∧
    CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      stateTable stateWidth stateTokenCount targetStart targetGammaFinish ∧
    targetBool = resultBool ∧
    CompactNumericVerifierLeafParseStackRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      targetGammaBoundary targetGammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag

def compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef :
    𝚺₀.Semisentence 43 := .mkSigma
  “stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool.
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
      stateTable stateWidth stateTokenCount nextStart nextProofFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish ∧
    !(compactNumericChildResultBoundedRowExposedDef)
      stateTable stateWidth stateTokenCount targetValueBoundary nextValueValueBound 0
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
      stateTable stateWidth stateTokenCount targetStart targetGammaFinish ∧
    targetBool = resultBool ∧
    !(compactNumericVerifierLeafParseStackRowsDef)
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      targetGammaBoundary targetGammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag”

def compactNumericVerifierLeafParseSeparatedTablesTransportRowsEnvironment
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) : Fin 43 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
    sourceTaskBoundary, sourceTaskCount, targetTaskBoundary, targetTaskCount,
    sourceValueBoundary, sourceValueCount, targetValueBoundary, targetValueCount,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    nextStart, nextProofFinish, nextCertificateFinish, nextStatusTag,
    proofTable, proofWidth, proofTokenCount, rootStart, rootGammaFinish,
    witnessFinish, rootFinish,
    certificateTable, certificateWidth, certificateTokenCount, suffixStart, suffixFinish,
    targetStart, targetFinish, targetGammaFinish, targetGammaCount,
    targetGammaBoundary, targetBool, targetGammaBoundarySize, resultBool]

@[simp] theorem compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef_spec
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) :
    compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef.val.Evalb
        (compactNumericVerifierLeafParseSeparatedTablesTransportRowsEnvironment
          stateTable stateWidth stateTokenCount
          sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
          sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          proofTable proofWidth proofTokenCount rootStart rootGammaFinish
          witnessFinish rootFinish
          certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize resultBool) ↔
      CompactNumericVerifierLeafParseSeparatedTablesTransportRows
        stateTable stateWidth stateTokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        proofTable proofWidth proofTokenCount rootStart rootGammaFinish
        witnessFinish rootFinish
        certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool := by
  let env := compactNumericVerifierLeafParseSeparatedTablesTransportRowsEnvironment
    stateTable stateWidth stateTokenCount
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    proofTable proofWidth proofTokenCount rootStart rootGammaFinish
    witnessFinish rootFinish
    certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
    targetStart targetFinish targetGammaFinish targetGammaCount
    targetGammaBoundary targetBool targetGammaBoundarySize resultBool
  change compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef.val.Evalb env ↔ _
  have hproofPayloadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#23 : Semiterm ℒₒᵣ Empty 43), #24, #25, #28, #29,
          #0, #1, #2, #19, #20]) =
        ![proofTable, proofWidth, proofTokenCount, witnessFinish, rootFinish,
          stateTable, stateWidth, stateTokenCount, nextStart, nextProofFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcertificatePayloadEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#30 : Semiterm ℒₒᵣ Empty 43), #31, #32, #33, #34,
          #0, #1, #2, #20, #21]) =
        ![certificateTable, certificateWidth, certificateTokenCount,
          suffixStart, suffixFinish,
          stateTable, stateWidth, stateTokenCount,
          nextProofFinish, nextCertificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htargetRowEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 43), #1, #2, #9, #18, ‘0’,
          #35, #36, #37, #38, #39, #40, #41]) =
        ![stateTable, stateWidth, stateTokenCount,
          targetValueBoundary, nextValueValueBound, 0,
          targetStart, targetFinish, targetGammaFinish, targetGammaCount,
          targetGammaBoundary, targetBool, targetGammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hproofGammaEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#23 : Semiterm ℒₒᵣ Empty 43), #24, #25,
          (‘(#26 + 1)’ : Semiterm ℒₒᵣ Empty 43), #27,
          #0, #1, #2, #35, #37]) =
        ![proofTable, proofWidth, proofTokenCount, rootStart + 1, rootGammaFinish,
          stateTable, stateWidth, stateTokenCount, targetStart, targetGammaFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hstackRowsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 43), #1, #2,
          #3, #4, #5, #6, #7, #8, #9, #10, #39, #38,
          #11, #12, #13, #14, #15, #16, #17, #18, #42, #22]) =
        ![stateTable, stateWidth, stateTokenCount,
          sourceTaskBoundary, sourceTaskCount, targetTaskBoundary, targetTaskCount,
          sourceValueBoundary, sourceValueCount, targetValueBoundary, targetValueCount,
          targetGammaBoundary, targetGammaCount,
          currentTaskTableWidth, currentTaskValueBound,
          currentValueTableWidth, currentValueValueBound,
          nextTaskTableWidth, nextTaskValueBound,
          nextValueTableWidth, nextValueValueBound,
          resultBool, nextStatusTag] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hproofPayload := compactFixedWidthCrossTableSlicesEqDef_spec
    proofTable proofWidth proofTokenCount witnessFinish rootFinish
    stateTable stateWidth stateTokenCount nextStart nextProofFinish
  have hcertificatePayload := compactFixedWidthCrossTableSlicesEqDef_spec
    certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
    stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish
  have htargetRow := compactNumericChildResultBoundedRowExposedDef_spec
    stateTable stateWidth stateTokenCount targetValueBoundary nextValueValueBound 0
    targetStart targetFinish targetGammaFinish targetGammaCount
    targetGammaBoundary targetBool targetGammaBoundarySize
  have hproofGamma := compactFixedWidthCrossTableSlicesEqDef_spec
    proofTable proofWidth proofTokenCount (rootStart + 1) rootGammaFinish
    stateTable stateWidth stateTokenCount targetStart targetGammaFinish
  have hstackRows := compactNumericVerifierLeafParseStackRowsDef_spec
    stateTable stateWidth stateTokenCount
    sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
    sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
    targetGammaBoundary targetGammaCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    resultBool nextStatusTag
  simp [compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef,
    CompactNumericVerifierLeafParseSeparatedTablesTransportRows,
    hproofPayloadEnv, hcertificatePayloadEnv, htargetRowEnv, hproofGammaEnv,
    hstackRowsEnv, hproofPayload, hcertificatePayload, htargetRow,
    hproofGamma, hstackRows]
  simp [env, compactNumericVerifierLeafParseSeparatedTablesTransportRowsEnvironment]

theorem compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef.val := by
  simp [compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef]

#print axioms compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef_spec
#print axioms compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef_sigmaZero
#print axioms CompactNumericVerifierLeafParseSeparatedTablesTransportRows

end FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
