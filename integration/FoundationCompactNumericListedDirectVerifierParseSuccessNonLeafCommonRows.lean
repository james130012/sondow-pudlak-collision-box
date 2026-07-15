import integration.FoundationCompactNumericListedDirectCrossTableSliceEquality
import integration.FoundationCompactNumericListedDirectChildResultListDropRows

/-!
# Common state rows for a successful non-leaf parse

These rows copy the proof and certificate suffixes into the next state,
preserve the child-result stack, preserve the public table bounds, and keep
the verifier running.  The one-parse/two-parse task schedule is deliberately
kept outside this common relation.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafCommonRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectCrossTableSliceEquality
open FoundationCompactNumericListedDirectChildResultListDropRows

def CompactNumericVerifierParseSuccessNonLeafCommonRows
    (stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish : Nat) : Prop :=
  CompactFixedWidthCrossTableSlicesEq
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      stateTable stateWidth stateTokenCount nextStart nextProofFinish ∧
    CompactFixedWidthCrossTableSlicesEq
      certificateTable certificateWidth certificateTokenCount
        certificateSuffixStart certificateSuffixFinish
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish ∧
    CompactNumericChildResultListDropRows
      stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentValueTableWidth currentValueValueBound 0 ∧
    nextTaskTableWidth = currentTaskTableWidth ∧
    nextTaskValueBound = currentTaskValueBound ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    nextStatusTag = 0

def compactNumericVerifierParseSuccessNonLeafCommonRowsDef :
    𝚺₀.Semisentence 29 := .mkSigma
  “stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish.
    !(compactFixedWidthCrossTableSlicesEqDef)
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      stateTable stateWidth stateTokenCount nextStart nextProofFinish ∧
    !(compactFixedWidthCrossTableSlicesEqDef)
      certificateTable certificateWidth certificateTokenCount
        certificateSuffixStart certificateSuffixFinish
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish ∧
    !(compactNumericChildResultListDropRowsDef)
      stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentValueTableWidth currentValueValueBound 0 ∧
    nextTaskTableWidth = currentTaskTableWidth ∧
    nextTaskValueBound = currentTaskValueBound ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    nextStatusTag = 0”

def compactNumericVerifierParseSuccessNonLeafCommonRowsEnvironment
    (stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish : Nat) : Fin 29 → Nat :=
  ![stateTable, stateWidth, stateTokenCount,
    sourceValueBoundary, sourceValueCount,
    targetValueBoundary, targetValueCount,
    currentTaskTableWidth, currentTaskValueBound,
    currentValueTableWidth, currentValueValueBound,
    nextTaskTableWidth, nextTaskValueBound,
    nextValueTableWidth, nextValueValueBound,
    nextStart, nextProofFinish, nextCertificateFinish, nextStatusTag,
    proofTable, proofWidth, proofTokenCount, proofSuffixStart, proofSuffixFinish,
    certificateTable, certificateWidth, certificateTokenCount,
    certificateSuffixStart, certificateSuffixFinish]

@[simp] theorem compactNumericVerifierParseSuccessNonLeafCommonRowsDef_spec
    (stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValueCount
      targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish : Nat) :
    compactNumericVerifierParseSuccessNonLeafCommonRowsDef.val.Evalb
        (compactNumericVerifierParseSuccessNonLeafCommonRowsEnvironment
          stateTable stateWidth stateTokenCount
          sourceValueBoundary sourceValueCount
          targetValueBoundary targetValueCount
          currentTaskTableWidth currentTaskValueBound
          currentValueTableWidth currentValueValueBound
          nextTaskTableWidth nextTaskValueBound
          nextValueTableWidth nextValueValueBound
          nextStart nextProofFinish nextCertificateFinish nextStatusTag
          proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
          certificateTable certificateWidth certificateTokenCount
          certificateSuffixStart certificateSuffixFinish) ↔
      CompactNumericVerifierParseSuccessNonLeafCommonRows
        stateTable stateWidth stateTokenCount
        sourceValueBoundary sourceValueCount
        targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
        certificateTable certificateWidth certificateTokenCount
        certificateSuffixStart certificateSuffixFinish := by
  let env := compactNumericVerifierParseSuccessNonLeafCommonRowsEnvironment
    stateTable stateWidth stateTokenCount
    sourceValueBoundary sourceValueCount
    targetValueBoundary targetValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStart nextProofFinish nextCertificateFinish nextStatusTag
    proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
    certificateTable certificateWidth certificateTokenCount
    certificateSuffixStart certificateSuffixFinish
  change compactNumericVerifierParseSuccessNonLeafCommonRowsDef.val.Evalb env ↔ _
  have hproofEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#19 : Semiterm ℒₒᵣ Empty 29), #20, #21, #22, #23,
          #0, #1, #2, #15, #16]) =
        ![proofTable, proofWidth, proofTokenCount,
          proofSuffixStart, proofSuffixFinish,
          stateTable, stateWidth, stateTokenCount, nextStart, nextProofFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hcertificateEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#24 : Semiterm ℒₒᵣ Empty 29), #25, #26, #27, #28,
          #0, #1, #2, #16, #17]) =
        ![certificateTable, certificateWidth, certificateTokenCount,
          certificateSuffixStart, certificateSuffixFinish,
          stateTable, stateWidth, stateTokenCount,
          nextProofFinish, nextCertificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvaluesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 29), #1, #2, #3, #4, #5, #6,
          #9, #10, ‘0’]) =
        ![stateTable, stateWidth, stateTokenCount,
          sourceValueBoundary, sourceValueCount,
          targetValueBoundary, targetValueCount,
          currentValueTableWidth, currentValueValueBound, 0] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseSuccessNonLeafCommonRowsDef,
    CompactNumericVerifierParseSuccessNonLeafCommonRows,
    hproofEnv, hcertificateEnv, hvaluesEnv]
  simp [env,
    compactNumericVerifierParseSuccessNonLeafCommonRowsEnvironment]

theorem compactNumericVerifierParseSuccessNonLeafCommonRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseSuccessNonLeafCommonRowsDef.val := by
  simp [compactNumericVerifierParseSuccessNonLeafCommonRowsDef]

theorem CompactNumericVerifierParseSuccessNonLeafCommonRows.sound
    {stateTable stateWidth stateTokenCount
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish : Nat}
    {proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceValues targetValues : List CompactNumericChildResult}
    (hrows : CompactNumericVerifierParseSuccessNonLeafCommonRows
      stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValues.length
      targetValueBoundary targetValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish)
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        proofSuffixStart proofSuffixFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateSuffixStart certificateSuffixFinish certificateSuffix)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues) :
    nextProof = proofSuffix ∧
      nextCertificate = certificateSuffix ∧
      targetValues = sourceValues ∧
      nextTaskTableWidth = currentTaskTableWidth ∧
      nextTaskValueBound = currentTaskValueBound ∧
      nextValueTableWidth = currentValueTableWidth ∧
      nextValueValueBound = currentValueValueBound ∧
      nextStatusTag = 0 := by
  rcases hrows with
    ⟨hproof, hcertificate, hvalues,
      htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩
  have hproofValue := hproof.natListValues_eq hproofSuffix hnextProof
  have hcertificateValue :=
    hcertificate.natListValues_eq hcertificateSuffix hnextCertificate
  have hvalueStack := hvalues.eq_drop_of_rows
    hsourceValueRows htargetValueRows
  exact ⟨hproofValue, hcertificateValue,
    by simpa using hvalueStack,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

theorem CompactNumericVerifierParseSuccessNonLeafCommonRows.of_components
    {stateTable stateWidth stateTokenCount
      sourceValueBoundary targetValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish : Nat}
    {proofSuffix certificateSuffix nextProof nextCertificate : List Nat}
    {sourceValues targetValues : List CompactNumericChildResult}
    (hproofSuffix : CompactAdditiveNatListDirectLayout
      proofTable proofWidth proofTokenCount
        proofSuffixStart proofSuffixFinish proofSuffix)
    (hcertificateSuffix : CompactAdditiveNatListDirectLayout
      certificateTable certificateWidth certificateTokenCount
        certificateSuffixStart certificateSuffixFinish certificateSuffix)
    (hnextProof : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount nextStart nextProofFinish nextProof)
    (hnextCertificate : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish nextCertificate)
    (hsourceValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount sourceValueBoundary sourceValues)
    (htargetValueRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout
        stateTable stateWidth stateTokenCount targetValueBoundary targetValues)
    (hsourceValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount sourceValueBoundary
        sourceValues.length currentValueTableWidth currentValueValueBound)
    (htargetValueGraph : CompactNumericChildResultListRowsGraph
      stateTable stateWidth stateTokenCount targetValueBoundary
        targetValues.length currentValueTableWidth currentValueValueBound)
    (hnextProofValue : nextProof = proofSuffix)
    (hnextCertificateValue : nextCertificate = certificateSuffix)
    (hvalues : targetValues = sourceValues)
    (htaskWidth : nextTaskTableWidth = currentTaskTableWidth)
    (htaskBound : nextTaskValueBound = currentTaskValueBound)
    (hvalueWidth : nextValueTableWidth = currentValueTableWidth)
    (hvalueBound : nextValueValueBound = currentValueValueBound)
    (hstatus : nextStatusTag = 0) :
    CompactNumericVerifierParseSuccessNonLeafCommonRows
      stateTable stateWidth stateTokenCount
      sourceValueBoundary sourceValues.length
      targetValueBoundary targetValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount proofSuffixStart proofSuffixFinish
      certificateTable certificateWidth certificateTokenCount
      certificateSuffixStart certificateSuffixFinish := by
  have hnextProof' : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextStart nextProofFinish proofSuffix := by
    simpa only [hnextProofValue] using hnextProof
  have hnextCertificate' : CompactAdditiveNatListDirectLayout
      stateTable stateWidth stateTokenCount
        nextProofFinish nextCertificateFinish certificateSuffix := by
    simpa only [hnextCertificateValue] using hnextCertificate
  have hproof := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    hproofSuffix hnextProof'
  have hcertificate := CompactFixedWidthCrossTableSlicesEq.of_natListLayouts
    hcertificateSuffix hnextCertificate'
  have hdrop : targetValues = sourceValues.drop 0 := by
    simpa only [List.drop_zero] using hvalues
  have hvalueRows :=
    CompactAdditiveStructuredListElementRowLayouts.childResultDropRows
      hsourceValueRows htargetValueRows hsourceValueGraph htargetValueGraph
      (consumed := 0) (by omega) hdrop
  exact ⟨hproof, hcertificate, hvalueRows,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound, hstatus⟩

#print axioms compactNumericVerifierParseSuccessNonLeafCommonRowsDef_spec
#print axioms compactNumericVerifierParseSuccessNonLeafCommonRowsDef_sigmaZero
#print axioms CompactNumericVerifierParseSuccessNonLeafCommonRows.sound
#print axioms CompactNumericVerifierParseSuccessNonLeafCommonRows.of_components

end FoundationCompactNumericListedDirectVerifierParseSuccessNonLeafCommonRows
