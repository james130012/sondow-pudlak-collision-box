import integration.FoundationCompactNumericListedDirectSyntaxTaskListTailTable
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRows

/-!
# Exact bounded uncons graph for syntax-task lists

The source list is split into one explicit three-field head task and a
canonical tail boundary table.  DropRows proves that the tail is the source
without its first row; ConsRows proves the converse reconstruction.  The tail
table carries its exact binary size and the public row-area bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows

open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListTailTable

def CompactAdditiveSyntaxTaskListUnconsRowsWithSize
    (tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount : Nat) : Prop :=
  0 < sourceCount ∧
    CompactAdditiveSyntaxTaskListDropRows
      tokenTable width tokenCount sourceBoundary sourceCount
        tailBoundary tailCount 1 ∧
    CompactAdditiveTripleBoundaryRows
      tokenCount tailCount tailBoundary ∧
    CompactAdditiveSyntaxTaskListConsRows
      tokenTable width tokenCount tailBoundary tailCount
        sourceBoundary sourceCount
        headKind headBinderArity headRepeatCount ∧
    tailBoundarySize = Nat.size tailBoundary ∧
    tailBoundarySize ≤ (tailCount + 1) * tokenCount

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef :
    𝚺₀.Semisentence 11 := .mkSigma
  “tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount.
    0 < sourceCount ∧
    !(compactAdditiveSyntaxTaskListDropRowsDef)
      tokenTable width tokenCount sourceBoundary sourceCount
        tailBoundary tailCount 1 ∧
    !(compactAdditiveTripleBoundaryRowsDef)
      tokenCount tailCount tailBoundary ∧
    !(compactAdditiveSyntaxTaskListConsRowsDef)
      tokenTable width tokenCount tailBoundary tailCount
        sourceBoundary sourceCount
        headKind headBinderArity headRepeatCount ∧
    !(compactNatSizeDef) tailBoundarySize tailBoundary ∧
    tailBoundarySize ≤ (tailCount + 1) * tokenCount”

def compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment
    (tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount : Nat) : Fin 11 → Nat :=
  ![tokenTable, width, tokenCount,
    sourceBoundary, sourceCount, tailBoundary, tailCount, tailBoundarySize,
    headKind, headBinderArity, headRepeatCount]

@[simp] theorem compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_spec
    (tokenTable width tokenCount
      sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
      headKind headBinderArity headRepeatCount : Nat) :
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val.Evalb
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment
          tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKind headBinderArity headRepeatCount) ↔
      CompactAdditiveSyntaxTaskListUnconsRowsWithSize
        tokenTable width tokenCount
          sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
          headKind headBinderArity headRepeatCount := by
  let env := compactAdditiveSyntaxTaskListUnconsRowsWithSizeEnvironment
    tokenTable width tokenCount
    sourceBoundary sourceCount tailBoundary tailCount tailBoundarySize
    headKind headBinderArity headRepeatCount
  change compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val.Evalb env ↔ _
  have hdropEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #3, #4, #5, #6,
          (↑(1 : Nat) : Semiterm ℒₒᵣ Empty 11)]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, tailBoundary, tailCount, 1] := by
    funext index
    fin_cases index <;> rfl
  have htripleEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#2 : Semiterm ℒₒᵣ Empty 11), #6, #5]) =
        ![tokenCount, tailCount, tailBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hconsEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 11), #1, #2, #5, #6, #3, #4,
          #8, #9, #10]) =
        ![tokenTable, width, tokenCount,
          tailBoundary, tailCount, sourceBoundary, sourceCount,
          headKind, headBinderArity, headRepeatCount] := by
    funext index
    fin_cases index <;> rfl
  have hsourceCountValue : env 4 = sourceCount := rfl
  have htailBoundaryValue : env 5 = tailBoundary := rfl
  have htailCountValue : env 6 = tailCount := rfl
  have htailBoundarySizeValue : env 7 = tailBoundarySize := rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  simp [compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef,
    CompactAdditiveSyntaxTaskListUnconsRowsWithSize,
    hdropEnv, htripleEnv, hconsEnv,
    hsourceCountValue, htailBoundaryValue, htailCountValue,
    htailBoundarySizeValue, htokenCountValue]

theorem compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef.val := by
  simp [compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef]

theorem exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff
    {tokenTable width tokenCount sourceBoundary : Nat}
    {source : List CompactSyntaxTask}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (headKind headBinderArity headRepeatCount : Nat) :
    (∃ tailBoundary tailCount tailBoundarySize,
        CompactAdditiveSyntaxTaskListUnconsRowsWithSize
          tokenTable width tokenCount sourceBoundary source.length
            tailBoundary tailCount tailBoundarySize
            headKind headBinderArity headRepeatCount) ↔
      ∃ tail,
        source = (headKind, headBinderArity, headRepeatCount) :: tail := by
  constructor
  · rintro ⟨tailBoundary, tailCount, _tailBoundarySize,
      _hpositive, _hdrop, htriple, hcons, _hsizeEq, _hsizeBound⟩
    let tail := compactAdditiveSyntaxTaskListRowValues
      tokenTable width tokenCount tailBoundary tailCount
    have htailRows : CompactAdditiveStructuredListElementRowLayouts
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          tailBoundary tail :=
      CompactAdditiveTripleBoundaryRows.realizedTaskRows htriple
    have hcons' : CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount tailBoundary tail.length
          sourceBoundary source.length
          headKind headBinderArity headRepeatCount := by
      simpa [tail] using hcons
    have hsourceEq :=
      (compactAdditiveSyntaxTaskListConsRows_iff_cons_of_rows
        (head := (headKind, headBinderArity, headRepeatCount))
        htailRows hsource).mp hcons'
    exact ⟨tail, hsourceEq⟩
  · rintro ⟨tail, hsourceEq⟩
    have hpositive : 0 < source.length := by simp [hsourceEq]
    rcases
        CompactAdditiveStructuredListElementRowLayouts.exists_taskTailTable
          hsource hpositive with
      ⟨tailBoundary, tailBoundarySize,
        htailRows, hdrop, hsizeEq, hsizeBound⟩
    have htailEq : source.drop 1 = tail := by simp [hsourceEq]
    have htailRows' : CompactAdditiveStructuredListElementRowLayouts
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          tailBoundary tail := by
      simpa only [htailEq] using htailRows
    have hdrop' : CompactAdditiveSyntaxTaskListDropRows
        tokenTable width tokenCount sourceBoundary source.length
          tailBoundary tail.length 1 := by
      simpa only [htailEq] using hdrop
    have htriple : CompactAdditiveTripleBoundaryRows
        tokenCount tail.length tailBoundary :=
      CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
        htailRows'
    have hcons : CompactAdditiveSyntaxTaskListConsRows
        tokenTable width tokenCount tailBoundary tail.length
          sourceBoundary source.length
          headKind headBinderArity headRepeatCount :=
      CompactAdditiveStructuredListElementRowLayouts.taskConsRows
        htailRows' hsource hsourceEq
    have hsizeBound' : tailBoundarySize ≤
        (tail.length + 1) * tokenCount := by
      simpa only [htailEq] using hsizeBound
    exact ⟨tailBoundary, tail.length, tailBoundarySize,
      hpositive, hdrop', htriple, hcons, hsizeEq, hsizeBound'⟩

#print axioms compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_spec
#print axioms compactAdditiveSyntaxTaskListUnconsRowsWithSizeDef_sigmaZero
#print axioms exists_compactAdditiveSyntaxTaskListUnconsRowsWithSize_iff

end FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
