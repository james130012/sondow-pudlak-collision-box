import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-!
# Closed general bounds for an outer selected parser branch

The enough path has syntax `empty ⋎ (guard ⋏ (lookup ⋏ branch))`.  The empty
path selects the left side of the same outer disjunction.  A single code bound
for the complete closed formula controls every connective assembly.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false

namespace FoundationCompactPAHybridOuterSelectedBranchClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

private theorem binaryFormulaCode_and_left_le_outerSelected
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_and_right_le_outerSelected
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_left_le_outerSelected
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le_outerSelected
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def outerSelectedEnoughPayloadEnvelope
    (syntaxResource guardResource lookupResource branchResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridConjunctionGeneralPayloadEnvelope syntaxResource guardResource
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource lookupResource
        branchResource))

theorem checkedHybridOuterEnoughPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (empty guard lookup branch : ValuationFormula)
    (guardCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation guard)
    (lookupCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation lookup)
    (branchCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation branch)
    (guardResource lookupResource branchResource syntaxResource : Nat)
    (hguard :
      hybridFormulaStructuralPayloadBound guardCertificate <= guardResource)
    (hlookup :
      hybridFormulaStructuralPayloadBound lookupCertificate <= lookupResource)
    (hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <= branchResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (empty ⋎ (guard ⋏ (lookup ⋏ branch))).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (empty ⋎ (guard ⋏ (lookup ⋏ branch)))).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := empty)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            guardCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              lookupCertificate branchCertificate))) <=
      outerSelectedEnoughPayloadEnvelope syntaxResource guardResource
        lookupResource branchResource := by
  have hc : empty.freeVariables = ∅ ∧ guard.freeVariables = ∅ ∧
      lookup.freeVariables = ∅ ∧ branch.freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_or,
      LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
    simpa only [Finset.union_eq_empty] using hclosed
  have henoughCode :
      (binaryFormulaCode (guard ⋏ (lookup ⋏ branch))).length <=
        syntaxResource :=
    (binaryFormulaCode_or_right_le_outerSelected empty
      (guard ⋏ (lookup ⋏ branch))).trans hcode
  have htailCode :
      (binaryFormulaCode (lookup ⋏ branch)).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_outerSelected guard
      (lookup ⋏ branch)).trans henoughCode
  have hguardCode :
      (binaryFormulaCode guard).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_outerSelected guard
      (lookup ⋏ branch)).trans henoughCode
  have hlookupCode :
      (binaryFormulaCode lookup).length <= syntaxResource :=
    (binaryFormulaCode_and_left_le_outerSelected lookup branch).trans htailCode
  have hbranchCode :
      (binaryFormulaCode branch).length <= syntaxResource :=
    (binaryFormulaCode_and_right_le_outerSelected lookup branch).trans htailCode
  have hemptyCode :
      (binaryFormulaCode empty).length <= syntaxResource :=
    (binaryFormulaCode_or_left_le_outerSelected empty
      (guard ⋏ (lookup ⋏ branch))).trans hcode
  have hinner :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral lookupCertificate
      branchCertificate lookupResource branchResource syntaxResource hlookup
      hbranch hpositive hc.2.2.1 hc.2.2.2 hlookupCode hbranchCode htailCode
  have hmiddle :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral guardCertificate
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        lookupCertificate branchCertificate)
      guardResource
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource lookupResource
        branchResource)
      syntaxResource hguard hinner hpositive hc.2.1
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hc.2.2.1, hc.2.2.2]
        simp)
      hguardCode htailCode henoughCode
  unfold outerSelectedEnoughPayloadEnvelope
  exact
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        guardCertificate
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          lookupCertificate branchCertificate))
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource guardResource
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource lookupResource
          branchResource))
      syntaxResource hmiddle hpositive hc.1
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hc.2.1,
          LO.FirstOrder.Semiformula.freeVariables_and, hc.2.2.1, hc.2.2.2]
        simp)
      hemptyCode henoughCode hcode

def outerSelectedEmptyPayloadEnvelope
    (syntaxResource emptyResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource emptyResource

theorem checkedHybridOuterEmptyPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (empty enough : ValuationFormula)
    (emptyCertificate :
      CheckedHybridValuationBoundedFormulaCertificate valuation empty)
    (emptyResource syntaxResource : Nat)
    (hempty :
      hybridFormulaStructuralPayloadBound emptyCertificate <= emptyResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (empty ⋎ enough).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (empty ⋎ enough)).length <= syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := enough) emptyCertificate) <=
      outerSelectedEmptyPayloadEnvelope syntaxResource emptyResource := by
  have hc : empty.freeVariables = ∅ ∧ enough.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
    exact Finset.union_eq_empty.mp hclosed
  unfold outerSelectedEmptyPayloadEnvelope
  exact
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral emptyCertificate
      emptyResource syntaxResource hempty hpositive hc.1 hc.2
      ((binaryFormulaCode_or_left_le_outerSelected empty enough).trans hcode)
      ((binaryFormulaCode_or_right_le_outerSelected empty enough).trans hcode)
      hcode

end FoundationCompactPAHybridOuterSelectedBranchClosedGeneralBounds
