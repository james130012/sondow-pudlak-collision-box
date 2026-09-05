import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardLeafFixedCore
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-! # Uniform closed conjunction assembly for term-output-row guards -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 120000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

def termRowsTwoGuardFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (termRowsGuardFormulaCodePolynomial bitBound)
    (termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (termRowsGuardLeafFixedPayloadPolynomial bitBound)

def termRowsThreeGuardFixedPayloadPolynomial (bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (termRowsGuardFormulaCodePolynomial bitBound)
    (termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (termRowsGuardLeafFixedPayloadPolynomial bitBound)

private theorem termRowsConjunction_left_code_le
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

private theorem termRowsConjunction_right_code_le
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp [binaryFormulaCode]
  omega

theorem termRowsTwoGuardEnvelope_le_fixed
    (valuation : Nat -> Nat) (formula1 formula2 : ValuationFormula)
    (resource1 resource2 bitBound : Nat)
    (hresource1 : resource1 <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (hresource2 : resource2 <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (hclosed : (formula1 ⋏ formula2).freeVariables = ∅)
    (hcode : (binaryFormulaCode (formula1 ⋏ formula2)).length <=
      termRowsGuardFormulaCodePolynomial bitBound) :
    transparentHybridConjunctionPayloadEnvelope valuation formula1 formula2
        resource1 resource2 <=
      termRowsTwoGuardFixedPayloadPolynomial bitBound := by
  have hmono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 formula2 hresource1 hresource2
  have hformula1Closed : formula1.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
    exact (Finset.union_eq_empty.mp hclosed).1
  have hformula2Closed : formula2.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_and] at hclosed
    exact (Finset.union_eq_empty.mp hclosed).2
  have hformula1Code : (binaryFormulaCode formula1).length <=
      termRowsGuardFormulaCodePolynomial bitBound :=
    (termRowsConjunction_left_code_le formula1 formula2).trans hcode
  have hformula2Code : (binaryFormulaCode formula2).length <=
      termRowsGuardFormulaCodePolynomial bitBound :=
    (termRowsConjunction_right_code_le formula1 formula2).trans hcode
  have hgeneral :=
    FoundationCompactPAHybridConjunctionGeneralContextBounds.transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      valuation formula1 formula2
      (termRowsGuardLeafFixedPayloadPolynomial bitBound)
      (termRowsGuardLeafFixedPayloadPolynomial bitBound)
      (termRowsGuardFormulaCodePolynomial bitBound)
      (termRowsGuardFormulaCodePolynomial_positive bitBound)
      hformula1Closed hformula2Closed hformula1Code hformula2Code hcode
  unfold termRowsTwoGuardFixedPayloadPolynomial
  exact hmono.trans hgeneral

theorem termRowsThreeGuardEnvelope_le_fixed
    (valuation : Nat -> Nat)
    (formula1 formula2 formula3 : ValuationFormula)
    (resource1 resource2 resource3 bitBound : Nat)
    (hresource1 : resource1 <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (hresource2 : resource2 <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (hresource3 : resource3 <=
      termRowsGuardLeafFixedPayloadPolynomial bitBound)
    (hclosed : (formula1 ⋏ (formula2 ⋏ formula3)).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (formula1 ⋏ (formula2 ⋏ formula3))).length <=
        termRowsGuardFormulaCodePolynomial bitBound) :
    transparentHybridConjunctionPayloadEnvelope valuation formula1
        (formula2 ⋏ formula3) resource1
        (transparentHybridConjunctionPayloadEnvelope valuation formula2
          formula3 resource2 resource3) <=
      termRowsThreeGuardFixedPayloadPolynomial bitBound := by
  have hinnerMono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula2 formula3 hresource2 hresource3
  have houterMono := transparentHybridConjunctionPayloadEnvelope_mono valuation
    formula1 (formula2 ⋏ formula3) hresource1 hinnerMono
  have hgeneral :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral valuation
      formula1 formula2 formula3
      (termRowsGuardLeafFixedPayloadPolynomial bitBound)
      (termRowsGuardLeafFixedPayloadPolynomial bitBound)
      (termRowsGuardLeafFixedPayloadPolynomial bitBound)
      (termRowsGuardFormulaCodePolynomial bitBound)
      (termRowsGuardFormulaCodePolynomial_positive bitBound) hclosed hcode
  unfold termRowsThreeGuardFixedPayloadPolynomial
  exact houterMono.trans hgeneral

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsGuardFixedBounds
