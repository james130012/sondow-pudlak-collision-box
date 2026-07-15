import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRows
import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRows
import integration.FoundationCompactNumericListedDirectChildResultListDropRows
import integration.FoundationCompactNumericListedDirectTokenSliceEquality
import integration.FoundationCompactNumericListedDirectVerifierPayloadEquality

/-!
# Common state rows for failed parsing

A failed parse preserves both streams and the child-result stack, removes the
parse-task head, and stores `some false`.  Parser-specific failure witnesses
are deliberately separate from this state transition.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierParseFailureRows

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedTaskMachine
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectChildResultListDropRows
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectVerifierPayloadEquality

def CompactNumericVerifierParseFailureRows
    (tokenTable width tokenCount
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
      nextStatusTag nextStatusBool : Nat) : Prop :=
  nextTaskTableWidth = currentTaskTableWidth ∧
    nextTaskValueBound = currentTaskValueBound ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    CompactFixedWidthTokenSlicesEq tokenTable width tokenCount
      currentStart currentCertificateFinish
      nextStart nextCertificateFinish ∧
    CompactNumericVerifierTaskListDropRows
      tokenTable width tokenCount
      currentTaskBoundary currentTaskCount nextTaskBoundary nextTaskCount
      currentTaskTableWidth currentTaskValueBound 1 ∧
    CompactNumericChildResultListDropRows
      tokenTable width tokenCount
      currentValueBoundary currentValueCount nextValueBoundary nextValueCount
      currentValueTableWidth currentValueValueBound 0 ∧
    nextStatusTag = 1 ∧
    nextStatusBool = 0

def compactNumericVerifierParseFailureRowsDef :
    𝚺₀.Semisentence 25 := .mkSigma
  “tokenTable width tokenCount
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
      nextStatusTag nextStatusBool.
    nextTaskTableWidth = currentTaskTableWidth ∧
    nextTaskValueBound = currentTaskValueBound ∧
    nextValueTableWidth = currentValueTableWidth ∧
    nextValueValueBound = currentValueValueBound ∧
    !(compactFixedWidthTokenSlicesEqDef)
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      nextStart nextCertificateFinish ∧
    !(compactNumericVerifierTaskListDropRowsDef)
      tokenTable width tokenCount
      currentTaskBoundary currentTaskCount nextTaskBoundary nextTaskCount
      currentTaskTableWidth currentTaskValueBound 1 ∧
    !(compactNumericChildResultListDropRowsDef)
      tokenTable width tokenCount
      currentValueBoundary currentValueCount nextValueBoundary nextValueCount
      currentValueTableWidth currentValueValueBound 0 ∧
    nextStatusTag = 1 ∧ nextStatusBool = 0”

@[simp] theorem compactNumericVerifierParseFailureRowsDef_spec
    (tokenTable width tokenCount
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
      nextStatusTag nextStatusBool : Nat) :
    compactNumericVerifierParseFailureRowsDef.val.Evalb
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
          nextStatusTag, nextStatusBool] ↔
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
        nextStatusTag nextStatusBool := by
  let env : Fin 25 → Nat :=
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
      nextStatusTag, nextStatusBool]
  change compactNumericVerifierParseFailureRowsDef.val.Evalb env ↔ _
  have hslicesEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2, #3, #4, #13, #14]) =
        ![tokenTable, width, tokenCount,
          currentStart, currentCertificateFinish,
          nextStart, nextCertificateFinish] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have htaskEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2,
          #5, #6, #15, #16, #9, #10, ‘1’]) =
        ![tokenTable, width, tokenCount,
          currentTaskBoundary, currentTaskCount,
          nextTaskBoundary, nextTaskCount,
          currentTaskTableWidth, currentTaskValueBound, 1] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  have hvalueEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 25), #1, #2,
          #7, #8, #17, #18, #11, #12, ‘0’]) =
        ![tokenTable, width, tokenCount,
          currentValueBoundary, currentValueCount,
          nextValueBoundary, nextValueCount,
          currentValueTableWidth, currentValueValueBound, 0] := by
    funext coordinate
    fin_cases coordinate <;> rfl
  simp [compactNumericVerifierParseFailureRowsDef,
    CompactNumericVerifierParseFailureRows,
    hslicesEnv, htaskEnv, hvalueEnv]
  simp [env]

theorem compactNumericVerifierParseFailureRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactNumericVerifierParseFailureRowsDef.val := by
  exact compactNumericVerifierParseFailureRowsDef.sigma_prop

theorem CompactNumericVerifierParseFailureRows.sound
    {tokenTable width tokenCount
      currentStart currentProofFinish currentCertificateFinish
      currentTaskBoundary currentValueBoundary
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextProofFinish nextCertificateFinish
      nextTaskBoundary nextValueBoundary
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool : Nat}
    {currentProof currentCertificate nextProof nextCertificate : List Nat}
    {currentTasks nextTasks : List CompactNumericVerifierTask}
    {currentValues nextValues : List CompactNumericChildResult}
    (hrows : CompactNumericVerifierParseFailureRows
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTasks.length
      currentValueBoundary currentValues.length
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTasks.length
      nextValueBoundary nextValues.length
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool)
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
  rcases hrows with
    ⟨htaskWidth, htaskBound, hvalueWidth, hvalueBound,
      hstreams, htaskDrop, hvalueDrop, hstatusTag, hstatusBool⟩
  have hcurrentProofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hcurrentProof
  have hnextProofFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hnextProof
  have hcurrentCertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hcurrentCertificate
  have hnextCertificateFinish :=
    CompactAdditiveNatListDirectLayout.finish_eq hnextCertificate
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := 0) hstreams rfl rfl
      (by omega) (by omega) (by omega)
      hcurrentProof hnextProof with
    ⟨proofOffset, hcurrentProofAt, hnextProofAt, hproofEq⟩
  rcases CompactFixedWidthTokenSlicesEq.natListPrefix_eq
      (offset := proofOffset) hstreams
      hcurrentProofAt hnextProofAt
      (by omega) (le_refl currentCertificateFinish)
      (le_refl nextCertificateFinish)
      hcurrentCertificate hnextCertificate with
    ⟨_certificateOffset, _hcurrentCertificateAt,
      _hnextCertificateAt, hcertificateEq⟩
  have htasks := htaskDrop.eq_drop_of_rows
    hcurrentTaskRows hnextTaskRows
  have hvalues := hvalueDrop.eq_drop_of_rows
    hcurrentValueRows hnextValueRows
  exact ⟨hproofEq, hcertificateEq,
    by simpa using htasks, by simpa using hvalues,
    htaskWidth, htaskBound, hvalueWidth, hvalueBound,
    hstatusTag, by simpa [compactAdditiveBoolTag] using hstatusBool⟩

#print axioms compactNumericVerifierParseFailureRowsDef_spec
#print axioms compactNumericVerifierParseFailureRowsDef_sigmaZero
#print axioms CompactNumericVerifierParseFailureRows.sound

end FoundationCompactNumericListedDirectVerifierParseFailureRows
