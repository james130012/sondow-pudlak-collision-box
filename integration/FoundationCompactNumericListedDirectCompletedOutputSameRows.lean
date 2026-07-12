import integration.FoundationCompactNumericListedDirectBinaryNatStatusCases
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectNatListBoundaryRigidity
import integration.FoundationCompactNumericListedDirectCompletedStatusSameRows

/-!
# Direct completed-status output equality with a source natural list

The completed status prefix, its structured output list, and direct equality
with a source natural-number list are tied together.  Unit-boundary rigidity
forces the formula-side output table onto the actual status payload rows, so an
alternative table cannot certify a different output.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectCompletedOutputSameRows

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectTokenStreamInverse
open FoundationCompactNumericListedDirectTokenStreamTableau
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRows

def CompactBinaryNatCompletedOutputSameRows
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount outputStart outputBoundary : Nat) : Prop :=
  CompactBinaryNatCompletedStatusPrefix
      tokenTable width tokenCount statusStart outputStart ∧
    CompactAdditiveStructuredListLayout
      tokenTable width tokenCount outputStart sourceCount statusFinish
        outputBoundary ∧
    CompactAdditiveNatListSameRows
      tokenTable width tokenCount sourceBoundary sourceCount
        outputBoundary sourceCount

def CompactBinaryNatCompletedOutputSameRowsWithSize
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount outputStart outputBoundary
      outputBoundarySize : Nat) : Prop :=
  CompactBinaryNatCompletedOutputSameRows
      tokenTable width tokenCount statusStart statusFinish
        sourceBoundary sourceCount outputStart outputBoundary ∧
    outputBoundarySize = Nat.size outputBoundary ∧
    outputBoundarySize ≤ (sourceCount + 1) * tokenCount

def compactBinaryNatCompletedOutputSameRowsFormulaBundle :
    𝚺₀.Semisentence 5 × 𝚺₀.Semisentence 7 × 𝚺₀.Semisentence 7 :=
  (compactBinaryNatCompletedStatusPrefixDef,
    compactAdditiveStructuredListLayoutDef,
    compactAdditiveNatListSameRowsDef)

@[simp] theorem compactBinaryNatCompletedOutputSameRowsFormulaBundle_spec
    (tokenTable width tokenCount statusStart statusFinish
      sourceBoundary sourceCount outputStart outputBoundary : Nat) :
    (compactBinaryNatCompletedOutputSameRowsFormulaBundle.1.val.Evalb
          ![tokenTable, width, tokenCount, statusStart, outputStart] ∧
      compactBinaryNatCompletedOutputSameRowsFormulaBundle.2.1.val.Evalb
          ![tokenTable, width, tokenCount, outputStart, sourceCount,
            statusFinish, outputBoundary] ∧
      compactBinaryNatCompletedOutputSameRowsFormulaBundle.2.2.val.Evalb
          ![tokenTable, width, tokenCount, sourceBoundary, sourceCount,
            outputBoundary, sourceCount]) ↔
      CompactBinaryNatCompletedOutputSameRows
        tokenTable width tokenCount statusStart statusFinish
          sourceBoundary sourceCount outputStart outputBoundary := by
  simp [compactBinaryNatCompletedOutputSameRowsFormulaBundle,
    CompactBinaryNatCompletedOutputSameRows]

theorem completedOutputSameRows_iff
    {tokenTable width tokenCount statusStart statusFinish sourceBoundary : Nat}
    {source : List Nat} {status : Option (Option (List Nat))}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount statusStart statusFinish status) :
    (∃ outputStart outputBoundary,
        CompactBinaryNatCompletedOutputSameRows
          tokenTable width tokenCount statusStart statusFinish
            sourceBoundary source.length outputStart outputBoundary) ↔
      status = some (some source) := by
  constructor
  · rintro ⟨outputStart, outputBoundary,
      hprefix, houtputLayout, hsameRows⟩
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
    have hsameStart : innerPayloadStart = outputStart := by omega
    have hformulaUnit : CompactAdditiveUnitBoundaryRows
        tokenCount source.length outputBoundary :=
      CompactAdditiveNatListSameRows.targetUnitBoundaryRows hsameRows
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
    have hcount : output.length = source.length := by omega
    have hformulaLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount innerPayloadStart output.length
          statusFinish outputBoundary := by
      rw [hcount, hsameStart]
      exact houtputLayout
    have hformulaRows :
        CompactAdditiveStructuredListElementRowLayouts
          CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
            outputBoundary output :=
      CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary
        hactualLayout hactualRows hformulaLayout'
          (by simpa [hcount] using hformulaUnit)
    have htypedSameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          outputBoundary output.length := by
      simpa only [hcount] using hsameRows
    have houtput : output = source :=
      CompactAdditiveNatListSameRows.eq_of_rows
        htypedSameRows hsource hformulaRows
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
          ⟨source, rfl, hinnerPayloadStart⟩
    have houtputLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount innerPayloadStart source.length
          statusFinish outputBoundary := by
      simpa using houtputLayout
    have hsameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          outputBoundary source.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hsource houtputRows rfl
    exact ⟨innerPayloadStart, outputBoundary,
      hprefix, houtputLayout', hsameRows⟩

theorem completedOutputSameRowsWithSize_iff
    {tokenTable width tokenCount statusStart statusFinish sourceBoundary : Nat}
    {source : List Nat} {status : Option (Option (List Nat))}
    (hsource : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (hstatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount statusStart statusFinish status) :
    (∃ outputStart outputBoundary outputBoundarySize,
        CompactBinaryNatCompletedOutputSameRowsWithSize
          tokenTable width tokenCount statusStart statusFinish
            sourceBoundary source.length outputStart outputBoundary
            outputBoundarySize) ↔
      status = some (some source) := by
  constructor
  · rintro ⟨outputStart, outputBoundary, outputBoundarySize,
      hrelation, _hsizeEq, _hsizeBound⟩
    exact (completedOutputSameRows_iff hsource hstatus).mp
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
          ⟨source, rfl, hinnerPayloadStart⟩
    have houtputLayout' : CompactAdditiveStructuredListLayout
        tokenTable width tokenCount innerPayloadStart source.length
          statusFinish outputBoundary := by
      simpa using houtputLayout
    have hsameRows : CompactAdditiveNatListSameRows
        tokenTable width tokenCount sourceBoundary source.length
          outputBoundary source.length :=
      CompactAdditiveStructuredListElementRowLayouts.natSameRows
        hsource houtputRows rfl
    exact ⟨innerPayloadStart, outputBoundary, Nat.size outputBoundary,
      ⟨hprefix, houtputLayout', hsameRows⟩,
      rfl, by simpa using houtputSize⟩

#print axioms compactBinaryNatCompletedOutputSameRowsFormulaBundle_spec
#print axioms completedOutputSameRows_iff
#print axioms completedOutputSameRowsWithSize_iff

end FoundationCompactNumericListedDirectCompletedOutputSameRows
