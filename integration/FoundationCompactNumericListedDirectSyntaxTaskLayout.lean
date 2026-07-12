import integration.FoundationCompactNumericListedDirectAtomicListLayouts
import integration.FoundationCompactSyntaxTokenMachine

/-!
# Direct layout of one compact syntax-parser task

A task is exactly three additive natural-number tokens: its task kind, binder
arity, and repeat count.  The direct layout exposes those three consecutive
cells in the common trace token table.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskLayout

open FoundationCompactAdditiveTokenCodec
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph

attribute [local instance]
  FoundationCompactNumericListedDirectTraceCode.compactSyntaxTaskAdditiveCodec

@[simp] theorem compactAdditiveEncode_syntaxTask
    (task : CompactSyntaxTask) :
    compactAdditiveEncode task = [task.1, task.2.1, task.2.2] := by
  rcases task with ⟨kind, binderArity, count⟩
  simp [compactAdditiveEncode_prod]

def CompactSyntaxTaskDirectLayout
    (tokenTable width tokenCount start finish : Nat)
    (task : CompactSyntaxTask) : Prop :=
  ∃ binderStart countStart,
    CompactAdditiveTokenCell
      tokenTable width tokenCount start task.1 binderStart ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount binderStart task.2.1 countStart ∧
    CompactAdditiveTokenCell
      tokenTable width tokenCount countStart task.2.2 finish

theorem compactSyntaxTaskDirectLayout_canonical
    (frontTokens : List Nat) (task : CompactSyntaxTask)
    (backTokens : List Nat) :
    let taskTokens := compactAdditiveEncode task
    let tokens := frontTokens ++ taskTokens ++ backTokens
    let width := (compactBinaryNatPayloadBits tokens).length
    let start := frontTokens.length
    let finish := start + taskTokens.length
    CompactSyntaxTaskDirectLayout
      (compactFixedWidthTableCode width tokens)
      width tokens.length start finish task := by
  let taskTokens := compactAdditiveEncode task
  let tokens := frontTokens ++ taskTokens ++ backTokens
  let width := (compactBinaryNatPayloadBits tokens).length
  let start := frontTokens.length
  let binderStart := start + 1
  let countStart := start + 2
  let finish := start + taskTokens.length
  have htaskTokens : taskTokens = [task.1, task.2.1, task.2.2] := by
    exact compactAdditiveEncode_syntaxTask task
  have hwidth : ∀ token ∈ tokens, Nat.size token ≤ width := by
    intro token htoken
    exact compactBinaryNatToken_size_le_payloadLength tokens token htoken
  have hstartLt : start < tokens.length := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens]
    simp [start]
  have hbinderStartLt : binderStart < tokens.length := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens]
    simp [binderStart, start]
  have hcountStartLt : countStart < tokens.length := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens]
    simp [countStart, start]
  have hstartValue : tokens.getI start = task.1 := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens
      ([task.1, task.2.1, task.2.2] ++ backTokens)
      start (by simp [start])]
    simp [start]
  have hbinderValue : tokens.getI binderStart = task.2.1 := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens
      ([task.1, task.2.1, task.2.2] ++ backTokens)
      binderStart (by simp [binderStart, start])]
    simp [binderStart, start]
  have hcountValue : tokens.getI countStart = task.2.2 := by
    rw [show tokens = frontTokens ++ taskTokens ++ backTokens by rfl]
    rw [htaskTokens, List.append_assoc]
    rw [List.getI_append_right frontTokens
      ([task.1, task.2.1, task.2.2] ++ backTokens)
      countStart (by simp [countStart, start])]
    simp [countStart, start]
  have hstartCell := compactAdditiveTokenCell_canonical
    tokens width start hstartLt hwidth
  have hbinderCell := compactAdditiveTokenCell_canonical
    tokens width binderStart hbinderStartLt hwidth
  have hcountCell := compactAdditiveTokenCell_canonical
    tokens width countStart hcountStartLt hwidth
  rw [hstartValue] at hstartCell
  rw [hbinderValue] at hbinderCell
  rw [hcountValue] at hcountCell
  have hfinish : finish = countStart + 1 := by
    simp [finish, countStart, htaskTokens]
  refine ⟨binderStart, countStart, ?_, ?_, ?_⟩
  · simpa [taskTokens, tokens, width, start, binderStart] using hstartCell
  · simpa [taskTokens, tokens, width, start, binderStart,
      countStart] using hbinderCell
  · simpa [taskTokens, tokens, width, start, finish, countStart,
      hfinish] using hcountCell

#print axioms compactAdditiveEncode_syntaxTask
#print axioms compactSyntaxTaskDirectLayout_canonical

end FoundationCompactNumericListedDirectSyntaxTaskLayout
