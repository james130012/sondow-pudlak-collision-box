import integration.FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

/-!
# Uniform size bounds for verifier child-result components

Each indexed child-result row exposes its context-list boundary and Boolean
component.  Their sizes are bounded solely by the ambient token count.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierChildResultComponentBounds

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectVerifierChildResultFormula
open FoundationCompactNumericListedDirectVerifierCombineStateGraphCompleteness

theorem CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds
    {tokenTable width tokenCount valueBoundary rowIndex : Nat}
    {values : List CompactNumericChildResult}
    (hrows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        valueBoundary values)
    (hrowIndex : rowIndex < values.length) :
    ∃ gammaCount gammaBoundary boolValue,
      gammaCount = (values.getI rowIndex).1.length ∧
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatListDirectLayout tokenTable width tokenCount
          gammaBoundary (values.getI rowIndex).1 ∧
      boolValue = compactAdditiveBoolTag (values.getI rowIndex).2 ∧
      gammaCount ≤ tokenCount ∧
      Nat.size gammaCount ≤ tokenCount ∧
      Nat.size gammaBoundary ≤ (tokenCount + 1) * tokenCount ∧
      Nat.size boolValue ≤ 1 := by
  rcases CompactAdditiveStructuredListElementRowLayouts.childResult_components_at
      hrows rowIndex hrowIndex with
    ⟨_componentGammaBoundary, boolValue, _componentGammaRows, hboolValue⟩
  rcases hrows rowIndex hrowIndex with
    ⟨_start, _hstart, _finish, _hfinish,
      _hstartEntry, _hfinishEntry, hlayout⟩
  rcases CompactNumericChildResultDirectLayout.toCoreGraph hlayout with
    ⟨coordinates, sizeWitness,
      _hcoordinatesStart, _hcoordinatesFinish, hcoordinatesBool, hcore⟩
  have hcoreBounds := CompactNumericChildResultCoreGraph.bounds hcore
  rcases hlayout with
    ⟨_gammaFinish, gammaBoundary, _layoutBoolValue,
      _hproduct, hgammaLayout, hgammaRows,
      _hlayoutBoolValue, _hbool, hgammaBoundarySize⟩
  rcases hgammaLayout with
    ⟨gammaBodyStart, _hgammaBodyStart, hgammaHeader, _hgammaBoundary⟩
  have hgammaCountBound :
      gammaBodyStart + (values.getI rowIndex).1.length ≤ tokenCount :=
    hgammaHeader.2
  have hgammaCountLe : (values.getI rowIndex).1.length ≤ tokenCount := by
    omega
  have hgammaCountSize : Nat.size (values.getI rowIndex).1.length ≤ tokenCount :=
    Nat.size_le.mpr (hgammaCountLe.trans_lt tokenCount.lt_two_pow_self)
  have hgammaBoundaryArea :
      ((values.getI rowIndex).1.length + 1) * tokenCount ≤
        (tokenCount + 1) * tokenCount :=
    Nat.mul_le_mul_right tokenCount
      (Nat.add_le_add_right hgammaCountLe 1)
  have hboolValueEq : boolValue = coordinates.boolValue :=
    hboolValue.trans hcoordinatesBool.symm
  have hboolValueSize : Nat.size boolValue ≤ 1 := by
    rw [hboolValueEq]
    simpa using Nat.size_le_size hcoreBounds.boolValue_le_one
  exact ⟨(values.getI rowIndex).1.length, gammaBoundary, boolValue,
    rfl, hgammaRows, hboolValue, hgammaCountLe, hgammaCountSize,
    hgammaBoundarySize.trans hgammaBoundaryArea, hboolValueSize⟩

#print axioms
  CompactAdditiveStructuredListElementRowLayouts.childResult_component_size_bounds

end FoundationCompactNumericListedDirectVerifierChildResultComponentBounds
