import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

/-! # Closed bounds for a three-way right disjunction -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds

def threeRightDisjunctionPathZeroPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource

def threeRightDisjunctionPathOnePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)

def threeRightDisjunctionPathTwoPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  threeRightDisjunctionPathOnePayloadEnvelope syntaxResource childResource

private theorem binaryFormulaCode_or_left_le_three
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le_three
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem threeRightOuterParts
    (a b c : ValuationFormula)
    (hclosed : (a ⋎ b ⋎ c).freeVariables = ∅)
    (syntaxResource : Nat)
    (hcode : (binaryFormulaCode (a ⋎ b ⋎ c)).length <= syntaxResource) :
    a.freeVariables = ∅ ∧
    (b ⋎ c).freeVariables = ∅ ∧
    (binaryFormulaCode a).length <= syntaxResource ∧
    (binaryFormulaCode (b ⋎ c)).length <= syntaxResource := by
  have hc := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hclosed)
  exact ⟨hc.1, hc.2,
    (binaryFormulaCode_or_left_le_three a (b ⋎ c)).trans hcode,
    (binaryFormulaCode_or_right_le_three a (b ⋎ c)).trans hcode⟩

theorem threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c).freeVariables = ∅)
    (hcode : (binaryFormulaCode (a ⋎ b ⋎ c)).length <= syntaxResource) :
    transparentHybridDisjunctionLeftPayloadEnvelope valuation a (b ⋎ c)
        childResource <=
      threeRightDisjunctionPathZeroPayloadEnvelope syntaxResource
        childResource := by
  have hp := threeRightOuterParts a b c hclosed syntaxResource hcode
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  unfold threeRightDisjunctionPathZeroPayloadEnvelope
  exact transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation a
    (b ⋎ c) childResource syntaxResource hpositive hcontext hp.2.2.1
    hp.2.2.2 hcode

theorem threeRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c).freeVariables = ∅)
    (hcode : (binaryFormulaCode (a ⋎ b ⋎ c)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a (b ⋎ c)
        (transparentHybridDisjunctionLeftPayloadEnvelope valuation b c
          childResource) <=
      threeRightDisjunctionPathOnePayloadEnvelope syntaxResource
        childResource := by
  have hp := threeRightOuterParts a b c hclosed syntaxResource hcode
  have hbc := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hp.2.1)
  have hbCode :=
    (binaryFormulaCode_or_left_le_three b c).trans hp.2.2.2
  have hcCode :=
    (binaryFormulaCode_or_right_le_three b c).trans hp.2.2.2
  have htailContext :
      formulaCodeSum (valuationContext (b ⋎ c).freeVariables valuation) <=
        syntaxResource := by
    rw [hp.2.1]
    simp [valuationContext, formulaCodeSum]
  have hinner :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation b c
      childResource syntaxResource hpositive htailContext hbCode hcCode
      hp.2.2.2
  have hmono :=
    transparentHybridDisjunctionRightPayloadEnvelope_mono valuation a (b ⋎ c)
      hinner
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have houter :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation a
      (b ⋎ c)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hpositive hcontext hp.2.2.1 hp.2.2.2 hcode
  unfold threeRightDisjunctionPathOnePayloadEnvelope
  exact hmono.trans houter

theorem threeRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c).freeVariables = ∅)
    (hcode : (binaryFormulaCode (a ⋎ b ⋎ c)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a (b ⋎ c)
        (transparentHybridDisjunctionRightPayloadEnvelope valuation b c
          childResource) <=
      threeRightDisjunctionPathTwoPayloadEnvelope syntaxResource
        childResource := by
  have hp := threeRightOuterParts a b c hclosed syntaxResource hcode
  have hbc := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hp.2.1)
  have hbCode :=
    (binaryFormulaCode_or_left_le_three b c).trans hp.2.2.2
  have hcCode :=
    (binaryFormulaCode_or_right_le_three b c).trans hp.2.2.2
  have htailContext :
      formulaCodeSum (valuationContext (b ⋎ c).freeVariables valuation) <=
        syntaxResource := by
    rw [hp.2.1]
    simp [valuationContext, formulaCodeSum]
  have hinner :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation b c
      childResource syntaxResource hpositive htailContext hbCode hcCode
      hp.2.2.2
  have hmono :=
    transparentHybridDisjunctionRightPayloadEnvelope_mono valuation a (b ⋎ c)
      hinner
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have houter :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation a
      (b ⋎ c)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hpositive hcontext hp.2.2.1 hp.2.2.2 hcode
  unfold threeRightDisjunctionPathTwoPayloadEnvelope
    threeRightDisjunctionPathOnePayloadEnvelope
  exact hmono.trans houter

#print axioms
  threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
#print axioms
  threeRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
#print axioms
  threeRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral

end FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds
