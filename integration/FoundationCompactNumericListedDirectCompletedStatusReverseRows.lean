import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases
import integration.FoundationCompactNumericListedDirectNatListReverseRows
import integration.FoundationCompactNumericListedDirectNatListBoundaryRigidity

/-!
# Direct completed-status output reversal

The completed status prefix, its structured output list, and the direct row
reversal relation are tied together.  Boundary rigidity excludes a second
list-table witness that points at different token rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCompletedStatusReverseRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectNatListReverseRows
open FoundationCompactNumericListedDirectNatListBoundaryRigidity

def CompactBinaryNatCompletedOutputReverseRows
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount outputStart outputBoundary : Nat) : Prop :=
  CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount statusStart outputStart ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount outputStart sourceCount statusFinish
        outputBoundary ∧
    CompactAdditiveNatListReverseRows
      tokenTable width tokenCount sourceBoundary sourceCount
        outputBoundary sourceCount

def CompactBinaryNatCompletedOutputReverseRowsWithSize
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount outputStart outputBoundary
      outputBoundarySize : Nat) : Prop :=
  CompactBinaryNatCompletedOutputReverseRows
      tokenTable width tokenCount statusStart statusFinish
        sourceBoundary sourceCount outputStart outputBoundary ∧
    outputBoundarySize = Nat.size outputBoundary ∧
    outputBoundarySize ≤ (sourceCount + 1) * tokenCount

def compactBinaryNatCompletedOutputReverseRowsFormulaBundle :
    𝚺₀.Semisentence 5 × 𝚺₀.Semisentence 7 × 𝚺₀.Semisentence 7 :=
  (compactBinaryNatCompletedStatusPrefixDef,
    compactAdditiveStructuredListLayoutDef,
    compactAdditiveNatListReverseRowsDef)

@[simp] theorem compactBinaryNatCompletedOutputReverseRowsFormulaBundle_spec
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount outputStart outputBoundary : Nat) :
    (compactBinaryNatCompletedOutputReverseRowsFormulaBundle.1.val.Evalb
          ![tokenTable, width, tokenCount, statusStart, outputStart] ∧
      compactBinaryNatCompletedOutputReverseRowsFormulaBundle.2.1.val.Evalb
          ![tokenTable, width, tokenCount, outputStart, sourceCount,
            statusFinish, outputBoundary] ∧
      compactBinaryNatCompletedOutputReverseRowsFormulaBundle.2.2.val.Evalb
          ![tokenTable, width, tokenCount, sourceBoundary, sourceCount,
            outputBoundary, sourceCount]) ↔
      CompactBinaryNatCompletedOutputReverseRows
        tokenTable width tokenCount statusStart statusFinish
          sourceBoundary sourceCount outputStart outputBoundary := by
  simp [compactBinaryNatCompletedOutputReverseRowsFormulaBundle,
    CompactBinaryNatCompletedOutputReverseRows]

theorem CompactAdditiveNatListReverseRows.targetUnitBoundaryRows
    {tokenTable width tokenCount sourceBoundary sourceCount
      targetBoundary targetCount : Nat}
    (hreverse : CompactAdditiveNatListReverseRows
      tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary targetCount) :
    CompactAdditiveUnitBoundaryRows
      tokenCount targetCount targetBoundary := by
  intro index hindex
  rcases hreverse.2 index hindex with
    ⟨sourceIndex, hsourceIndex, hindexSum,
      sourceLeft, hsourceLeft, sourceRight, hsourceRight,
      targetLeft, htargetLeft, targetRight, htargetRight,
      hsourceLeftEntry, hsourceRightEntry,
      htargetLeftEntry, htargetRightEntry, hrowEq⟩
  exact ⟨targetLeft, htargetLeft, targetRight, htargetRight,
    htargetLeftEntry, htargetRightEntry, hrowEq.2.2.2.1⟩

theorem completedOutputReverseRows_iff
    {tokenTable width tokenCount statusStart statusFinish sourceBoundary : Nat}
    {source : List Nat} {status : Option (Option (List Nat))}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount statusStart statusFinish status) :
    (∃ outputStart outputBoundary,
        CompactBinaryNatCompletedOutputReverseRows
          tokenTable width tokenCount statusStart statusFinish
            sourceBoundary source.length outputStart outputBoundary) ↔
      status = some (some source.reverse) := by
  constructor
  · rintro ⟨outputStart, outputBoundary,
      hprefix, houtputLayout, hreverseRows⟩
    rcases
        (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
          hstatus).mp hprefix with
      ⟨output, hstatusEq, houtputStart⟩
    subst status
    rcases hstatus with
      ⟨outerPayloadStart, houter,
        innerPayloadStart, hinner,
        actualBoundary, hactualLayout, hactualRows, _hactualSize⟩
    have hinnerPayloadStart : innerPayloadStart = statusStart + 2 := by
      have houterNext := houter.1.2.1
      have hinnerNext := hinner.1.2.1
      omega
    have hsameStart : innerPayloadStart = outputStart := by
      omega
    have hformulaUnit : CompactAdditiveUnitBoundaryRows
        tokenCount source.length outputBoundary :=
      CompactAdditiveNatListReverseRows.targetUnitBoundaryRows hreverseRows
    have hactualUnit : CompactAdditiveUnitBoundaryRows
        tokenCount output.length actualBoundary :=
      CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
        hactualRows
    have hformulaFinish :
        statusFinish = outputStart + 1 + source.length :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        houtputLayout hformulaUnit
    have hactualFinish :
        statusFinish = innerPayloadStart + 1 + output.length :=
      CompactAdditiveStructuredListLayout.finish_eq_start_add_count
        hactualLayout hactualUnit
    have hcount : output.length = source.length := by
      omega
    have htargetRows :
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
            outputBoundary output := by
      intro index hindex
      have hsourceIndex : index < source.length := by
        omega
      rcases hreverseRows.2 index hsourceIndex with
        ⟨sourceIndex, _hsourceIndex, _hindexSum,
          sourceLeft, _hsourceLeft, sourceRight, _hsourceRight,
          targetLeft, htargetLeft, targetRight, htargetRight,
          _hsourceLeftEntry, _hsourceRightEntry,
          htargetLeftEntry, htargetRightEntry, _hrowEq⟩
      rcases hactualRows index hindex with
        ⟨actualLeft, _hactualLeft, actualRight, _hactualRight,
          hactualLeftEntry, hactualRightEntry, hactualValue⟩
      have hformulaLeftCanonical :=
        CompactAdditiveStructuredListLayout.entry_eq_start_add
          houtputLayout hformulaUnit index (by omega)
      have hformulaRightCanonical :=
        CompactAdditiveStructuredListLayout.entry_eq_start_add
          houtputLayout hformulaUnit (index + 1) (by omega)
      have hactualLeftCanonical :=
        CompactAdditiveStructuredListLayout.entry_eq_start_add
          hactualLayout hactualUnit index (by omega)
      have hactualRightCanonical :=
        CompactAdditiveStructuredListLayout.entry_eq_start_add
          hactualLayout hactualUnit (index + 1) (by omega)
      have htargetLeftCursor :
          targetLeft = outputStart + 1 + index :=
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetLeftEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue
              hformulaLeftCanonical).symm
      have htargetRightCursor :
          targetRight = outputStart + 1 + (index + 1) :=
        (CompactFixedWidthEntry.value_eq_tableValue
          htargetRightEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue
              hformulaRightCanonical).symm
      have hactualLeftCursor :
          actualLeft = innerPayloadStart + 1 + index :=
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualLeftEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue
              hactualLeftCanonical).symm
      have hactualRightCursor :
          actualRight = innerPayloadStart + 1 + (index + 1) :=
        (CompactFixedWidthEntry.value_eq_tableValue
          hactualRightEntry).trans
            (CompactFixedWidthEntry.value_eq_tableValue
              hactualRightCanonical).symm
      have hleft : targetLeft = actualLeft := by
        omega
      have hright : targetRight = actualRight := by
        omega
      refine ⟨targetLeft, htargetLeft, targetRight, htargetRight,
        htargetLeftEntry, htargetRightEntry, ?_⟩
      rw [hleft, hright]
      exact hactualValue
    have htypedReverseRows : CompactAdditiveNatListReverseRows
        tokenTable width tokenCount sourceBoundary source.length
          outputBoundary output.length := by
      simpa only [hcount] using hreverseRows
    have houtput : output = source.reverse :=
      CompactAdditiveNatListReverseRows.eq_reverse_of_rows
        htypedReverseRows hsource htargetRows
    simp [houtput]
  · intro hstatusEq
    subst status
    have hstatusCopy := hstatus
    rcases hstatus with
      ⟨outerPayloadStart, houter,
        innerPayloadStart, hinner,
        outputBoundary, houtputLayout, houtputRows, _houtputSize⟩
    have hinnerPayloadStart : innerPayloadStart = statusStart + 2 := by
      have houterNext := houter.1.2.1
      have hinnerNext := hinner.1.2.1
      omega
    have hprefix : CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount statusStart innerPayloadStart :=
      (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
        hstatusCopy).mpr
        ⟨source.reverse, rfl, hinnerPayloadStart⟩
    have houtputLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount innerPayloadStart source.length
          statusFinish outputBoundary := by
      simpa using houtputLayout
    have hreverseRows : CompactAdditiveNatListReverseRows
        tokenTable width tokenCount sourceBoundary source.length
          outputBoundary source.length := by
      simpa using
        (CompactAdditiveStructuredListElementRowLayouts.natReverseRows
          hsource houtputRows rfl)
    exact ⟨innerPayloadStart, outputBoundary,
      hprefix, houtputLayout', hreverseRows⟩

theorem completedOutputReverseRowsWithSize_iff
    {tokenTable width tokenCount statusStart statusFinish sourceBoundary : Nat}
    {source : List Nat} {status : Option (Option (List Nat))}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount statusStart statusFinish status) :
    (∃ outputStart outputBoundary outputBoundarySize,
        CompactBinaryNatCompletedOutputReverseRowsWithSize
          tokenTable width tokenCount statusStart statusFinish
            sourceBoundary source.length outputStart outputBoundary
            outputBoundarySize) ↔
      status = some (some source.reverse) := by
  constructor
  · rintro ⟨outputStart, outputBoundary, outputBoundarySize,
      hrelation, _hsizeEq, _hsizeBound⟩
    exact (completedOutputReverseRows_iff hsource hstatus).mp
      ⟨outputStart, outputBoundary, hrelation⟩
  · intro hstatusEq
    subst status
    have hstatusCopy := hstatus
    rcases hstatus with
      ⟨outerPayloadStart, houter,
        innerPayloadStart, hinner,
        outputBoundary, houtputLayout, houtputRows, houtputSize⟩
    have hinnerPayloadStart : innerPayloadStart = statusStart + 2 := by
      have houterNext := houter.1.2.1
      have hinnerNext := hinner.1.2.1
      omega
    have hprefix : CompactBinaryNatCompletedStatusPrefix
        tokenTable width tokenCount statusStart innerPayloadStart :=
      (CompactBinaryNatStreamStatusDirectLayout.completedPrefix_iff
        hstatusCopy).mpr
          ⟨source.reverse, rfl, hinnerPayloadStart⟩
    have houtputLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount innerPayloadStart source.length
          statusFinish outputBoundary := by
      simpa using houtputLayout
    have hreverseRows : CompactAdditiveNatListReverseRows
        tokenTable width tokenCount sourceBoundary source.length
          outputBoundary source.length := by
      simpa using
        (CompactAdditiveStructuredListElementRowLayouts.natReverseRows
          hsource houtputRows rfl)
    exact ⟨innerPayloadStart, outputBoundary, Nat.size outputBoundary,
      ⟨hprefix, houtputLayout', hreverseRows⟩, rfl, by simpa using houtputSize⟩

#print axioms compactBinaryNatCompletedOutputReverseRowsFormulaBundle_spec
#print axioms CompactAdditiveNatListReverseRows.targetUnitBoundaryRows
#print axioms completedOutputReverseRows_iff
#print axioms completedOutputReverseRowsWithSize_iff

end FoundationCompactNumericListedDirectCompletedStatusReverseRows
