import integration.FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds

/-! # Closed bounds for a four-way right disjunction -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPAHybridFourRightDisjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridThreeRightDisjunctionClosedGeneralBounds

def fourRightDisjunctionPathZeroPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource

def fourRightDisjunctionPathOnePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (threeRightDisjunctionPathZeroPayloadEnvelope syntaxResource childResource)

def fourRightDisjunctionPathTwoPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (threeRightDisjunctionPathOnePayloadEnvelope syntaxResource childResource)

def fourRightDisjunctionPathThreePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (threeRightDisjunctionPathTwoPayloadEnvelope syntaxResource childResource)

private theorem binaryFormulaCode_or_left_le_four
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le_four
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem fourRightOuterParts
    (a b c d : ValuationFormula)
    (hclosed : (a ⋎ b ⋎ c ⋎ d).freeVariables = ∅)
    (syntaxResource : Nat)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d)).length <= syntaxResource) :
    a.freeVariables = ∅ ∧
    (b ⋎ c ⋎ d).freeVariables = ∅ ∧
    (binaryFormulaCode a).length <= syntaxResource ∧
    (binaryFormulaCode (b ⋎ c ⋎ d)).length <= syntaxResource := by
  have hc := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hclosed)
  exact ⟨hc.1, hc.2,
    (binaryFormulaCode_or_left_le_four a (b ⋎ c ⋎ d)).trans hcode,
    (binaryFormulaCode_or_right_le_four a (b ⋎ c ⋎ d)).trans hcode⟩

theorem fourRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d)).length <= syntaxResource) :
    transparentHybridDisjunctionLeftPayloadEnvelope valuation a
        (b ⋎ c ⋎ d) childResource <=
      fourRightDisjunctionPathZeroPayloadEnvelope syntaxResource
        childResource := by
  have hp := fourRightOuterParts a b c d hclosed syntaxResource hcode
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c ⋎ d).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  unfold fourRightDisjunctionPathZeroPayloadEnvelope
  exact transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation a
    (b ⋎ c ⋎ d) childResource syntaxResource hpositive hcontext hp.2.2.1
    hp.2.2.2 hcode

private theorem fourRightTailAssembly
    (valuation : Nat -> Nat)
    (a tail : ValuationFormula)
    (childEnvelope childGeneral syntaxResource : Nat)
    (htail : childEnvelope <= childGeneral)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ tail).freeVariables = ∅)
    (hcode : (binaryFormulaCode (a ⋎ tail)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a tail
        childEnvelope <=
      hybridDisjunctionGeneralPayloadEnvelope syntaxResource childGeneral := by
  have hc := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hclosed)
  have haCode :=
    (binaryFormulaCode_or_left_le_four a tail).trans hcode
  have htailCode :=
    (binaryFormulaCode_or_right_le_four a tail).trans hcode
  have hmono :=
    transparentHybridDisjunctionRightPayloadEnvelope_mono valuation a tail
      htail
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ tail).freeVariables valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have houter :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation a
      tail childGeneral syntaxResource hpositive hcontext haCode htailCode
      hcode
  exact hmono.trans houter

theorem fourRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a
        (b ⋎ c ⋎ d)
        (transparentHybridDisjunctionLeftPayloadEnvelope valuation b (c ⋎ d)
          childResource) <=
      fourRightDisjunctionPathOnePayloadEnvelope syntaxResource
        childResource := by
  have hp := fourRightOuterParts a b c d hclosed syntaxResource hcode
  have htail :=
    threeRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral valuation
      b c d childResource syntaxResource hpositive hp.2.1 hp.2.2.2
  unfold fourRightDisjunctionPathOnePayloadEnvelope
  exact fourRightTailAssembly valuation a (b ⋎ c ⋎ d) _ _ syntaxResource
    htail hpositive hclosed hcode

theorem fourRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a
        (b ⋎ c ⋎ d)
        (transparentHybridDisjunctionRightPayloadEnvelope valuation b (c ⋎ d)
          (transparentHybridDisjunctionLeftPayloadEnvelope valuation c d
            childResource)) <=
      fourRightDisjunctionPathTwoPayloadEnvelope syntaxResource
        childResource := by
  have hp := fourRightOuterParts a b c d hclosed syntaxResource hcode
  have htail :=
    threeRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral valuation
      b c d childResource syntaxResource hpositive hp.2.1 hp.2.2.2
  unfold fourRightDisjunctionPathTwoPayloadEnvelope
  exact fourRightTailAssembly valuation a (b ⋎ c ⋎ d) _ _ syntaxResource
    htail hpositive hclosed hcode

theorem fourRightDisjunctionPathThreeTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d)).length <= syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a
        (b ⋎ c ⋎ d)
        (transparentHybridDisjunctionRightPayloadEnvelope valuation b (c ⋎ d)
          (transparentHybridDisjunctionRightPayloadEnvelope valuation c d
            childResource)) <=
      fourRightDisjunctionPathThreePayloadEnvelope syntaxResource
        childResource := by
  have hp := fourRightOuterParts a b c d hclosed syntaxResource hcode
  have htail :=
    threeRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral valuation
      b c d childResource syntaxResource hpositive hp.2.1 hp.2.2.2
  unfold fourRightDisjunctionPathThreePayloadEnvelope
  exact fourRightTailAssembly valuation a (b ⋎ c ⋎ d) _ _ syntaxResource
    htail hpositive hclosed hcode

#print axioms
  fourRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
#print axioms
  fourRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
#print axioms
  fourRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
#print axioms
  fourRightDisjunctionPathThreeTransparentEnvelope_le_closedGeneral

end FoundationCompactPAHybridFourRightDisjunctionClosedGeneralBounds
