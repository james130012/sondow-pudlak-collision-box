import integration.FoundationCompactNumericListedDirectParserStateAtRows
import integration.FoundationCompactNumericListedDirectCompletedOutputSameRows

/-!
# Handwritten bounded formula for a parser final-state output

The nested completed-status prefix is followed by one structured natural list.
Its rows must equal a supplied source list, and its boundary-table code carries
the same explicit size guard used by the parser step formulas.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectParserFinalFormula

open FoundationCompactParserDirectTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedOutputSameRows
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateAtRows

def CompactUnifiedParserFinalStateRows
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) : Prop :=
  CompactBinaryNatCompletedOutputSameRowsWithSize
    tokenTable width tokenCount coordinates.tasksFinish coordinates.finish
      sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize

def compactUnifiedParserFinalStateRowsDef : 𝚺₀.Semisentence 16 := .mkSigma
  “tokenTable width tokenCount
      start finish tokensFinish tasksFinish
      tokensBoundary tokensCount tasksBoundary tasksCount
      sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize.
    !(compactBinaryNatCompletedStatusPrefixDef)
      tokenTable width tokenCount tasksFinish outputStart ∧
    !(compactAdditiveStructuredListLayoutDef)
      tokenTable width tokenCount
        outputStart sourceCount finish outputBoundary ∧
    !(compactAdditiveNatListSameRowsDef)
      tokenTable width tokenCount
        sourceBoundary sourceCount outputBoundary sourceCount ∧
    !(compactNatSizeDef) outputBoundarySize outputBoundary ∧
    outputBoundarySize ≤ (sourceCount + 1) * tokenCount”

def compactUnifiedParserFinalStateRowsEnvironment
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) : Fin 16 → Nat :=
  ![tokenTable, width, tokenCount,
    coordinates.start, coordinates.finish,
    coordinates.tokensFinish, coordinates.tasksFinish,
    coordinates.tokensBoundary, coordinates.tokensCount,
    coordinates.tasksBoundary, coordinates.tasksCount,
    sourceBoundary, sourceCount, outputStart, outputBoundary,
    outputBoundarySize]

@[simp] theorem compactUnifiedParserFinalStateRowsDef_spec
    (tokenTable width tokenCount : Nat)
    (coordinates : CompactUnifiedParserStateRowCoordinates)
    (sourceBoundary sourceCount outputStart outputBoundary outputBoundarySize :
      Nat) :
    compactUnifiedParserFinalStateRowsDef.val.Evalb
        (compactUnifiedParserFinalStateRowsEnvironment
          tokenTable width tokenCount coordinates sourceBoundary sourceCount
            outputStart outputBoundary outputBoundarySize) ↔
      CompactUnifiedParserFinalStateRows
        tokenTable width tokenCount coordinates sourceBoundary sourceCount
          outputStart outputBoundary outputBoundarySize := by
  let env := compactUnifiedParserFinalStateRowsEnvironment
    tokenTable width tokenCount coordinates sourceBoundary sourceCount
      outputStart outputBoundary outputBoundarySize
  change compactUnifiedParserFinalStateRowsDef.val.Evalb env ↔ _
  have hprefixEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2, #6, #13]) =
        ![tokenTable, width, tokenCount,
          coordinates.tasksFinish, outputStart] := by
    funext index
    fin_cases index <;> rfl
  have hlayoutEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2,
          #13, #12, #4, #14]) =
        ![tokenTable, width, tokenCount,
          outputStart, sourceCount, coordinates.finish, outputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have hsameEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#0 : Semiterm ℒₒᵣ Empty 16), #1, #2,
          #11, #12, #14, #12]) =
        ![tokenTable, width, tokenCount,
          sourceBoundary, sourceCount, outputBoundary, sourceCount] := by
    funext index
    fin_cases index <;> rfl
  have hsizeEnv :
      (Semiterm.val env Empty.elim ∘
        ![(#15 : Semiterm ℒₒᵣ Empty 16), #14]) =
        ![outputBoundarySize, outputBoundary] := by
    funext index
    fin_cases index <;> rfl
  have htokenCountValue : env 2 = tokenCount := rfl
  have hsourceCountValue : env 12 = sourceCount := rfl
  have houtputBoundarySizeValue : env 15 = outputBoundarySize := rfl
  simp [compactUnifiedParserFinalStateRowsDef,
    CompactUnifiedParserFinalStateRows,
    CompactBinaryNatCompletedOutputSameRowsWithSize,
    CompactBinaryNatCompletedOutputSameRows,
    hprefixEnv, hlayoutEnv, hsameEnv, hsizeEnv,
    htokenCountValue, hsourceCountValue, houtputBoundarySizeValue]
  constructor
  · rintro ⟨hprefix, hlayout, hsame, hsize, hbound⟩
    exact ⟨⟨hprefix, hlayout, hsame⟩, hsize, hbound⟩
  · rintro ⟨⟨hprefix, hlayout, hsame⟩, hsize, hbound⟩
    exact ⟨hprefix, hlayout, hsame, hsize, hbound⟩

theorem compactUnifiedParserFinalStateRowsDef_sigmaZero :
    LO.FirstOrder.Arithmetic.Hierarchy LO.Polarity.sigma 0
      compactUnifiedParserFinalStateRowsDef.val := by
  simp [compactUnifiedParserFinalStateRowsDef]

theorem exists_compactUnifiedParserFinalStateRows_iff
    {tokenTable width tokenCount sourceBoundary : Nat}
    {coordinates : CompactUnifiedParserStateRowCoordinates}
    {source : List Nat} {state : CompactUnifiedParserState}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hstate : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount coordinates state) :
    (∃ outputStart outputBoundary outputBoundarySize,
        CompactUnifiedParserFinalStateRows
          tokenTable width tokenCount coordinates sourceBoundary source.length
            outputStart outputBoundary outputBoundarySize) ↔
      state.2.2 = some (some source) := by
  simpa [CompactUnifiedParserFinalStateRows] using
    completedOutputSameRowsWithSize_iff hsource hstate.statusLayout

#print axioms compactUnifiedParserFinalStateRowsDef_spec
#print axioms compactUnifiedParserFinalStateRowsDef_sigmaZero
#print axioms exists_compactUnifiedParserFinalStateRows_iff

end FoundationCompactNumericListedDirectParserFinalFormula
