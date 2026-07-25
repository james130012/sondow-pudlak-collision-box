import integration.FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectFreeVariableBounds

/-!
# Uniform context bounds for direct additive unit-boundary rows

The open row terminal has exactly one possible free coordinate: the row index.
Consequently its valuation context has one uniform formula-code bound, independent
of the concrete row and boundary-table values.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectUniformContextBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsFixedWidthEntryBounds
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectCompiler
open FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectFreeVariableBounds

private abbrev unitZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsExplicitHybridCertificate.zeroValuation

private theorem valuationContext_formulaCodeSum_le_singleton
    (vars : Finset Nat) (valuation : Nat -> Nat) (numericBound : Nat)
    (hvariables : vars ⊆ {0})
    (hvaluation : valuation 0 <= numericBound) :
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext vars valuation) <=
      unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
  have hcard : vars.card <= 1 :=
    (Finset.card_le_card hvariables).trans (by simp)
  have hvalues : forall coordinate, coordinate ∈ vars ->
      valuation coordinate <= numericBound := by
    intro coordinate hcoordinate
    have hsingleton := hvariables hcoordinate
    simp only [Finset.mem_singleton] at hsingleton
    subst coordinate
    exact hvaluation
  have htermCodes : forall coordinate, coordinate ∈ vars ->
      (binaryTermCode (&coordinate : ValuationTerm)).length <=
        (binaryTermCode (&0 : ValuationTerm)).length := by
    intro coordinate hcoordinate
    have hsingleton := hvariables hcoordinate
    simp only [Finset.mem_singleton] at hsingleton
    subst coordinate
    exact le_rfl
  have hraw :=
    FoundationCompactPAValuationTermCompilerPublicBounds.valuationContext_formulaCodeSum_le_uniform
      vars valuation 1 numericBound
      (binaryTermCode (&0 : ValuationTerm)).length hcard hvalues htermCodes
  change
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext vars valuation) <=
      FoundationCompactPAValuationTermCompilerPublicBounds.valuationContextFormulaCodeSumEnvelope
        1 numericBound (binaryTermCode (&0 : ValuationTerm)).length
  exact hraw

theorem compactAdditiveUnitBoundaryRowsBranchTerminal_contextCodeSum_le
    (tokenCount boundaryTable index numericBound : Nat)
    (hindex : index <= numericBound) :
    FoundationCompactPAValuationTermCompilerPublicBounds.formulaCodeSum
        (valuationContext
          (compactAdditiveUnitBoundaryRowsBranchTerminal
            tokenCount boundaryTable).freeVariables
          (extendValuation index unitZeroValuation)) <=
      unitBoundaryTerminalContextFormulaCodeSumEnvelope numericBound := by
  let vars := (compactAdditiveUnitBoundaryRowsBranchTerminal
    tokenCount boundaryTable).freeVariables
  let valuation := extendValuation index unitZeroValuation
  have hvariables : vars ⊆ {0} :=
    compactAdditiveUnitBoundaryRowsBranchTerminal_freeVariables_subset_singleton
      tokenCount boundaryTable
  have hvaluation : valuation 0 <= numericBound := by
    change index <= numericBound
    exact hindex
  exact valuationContext_formulaCodeSum_le_singleton vars valuation numericBound
    hvariables hvaluation

#print axioms compactAdditiveUnitBoundaryRowsBranchTerminal_contextCodeSum_le

end FoundationCompactNumericListedDirectAdditiveUnitBoundaryRowsDirectUniformContextBounds
