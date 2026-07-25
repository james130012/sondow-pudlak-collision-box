import integration.FoundationCompactPAHybridFiveRightDisjunctionClosedGeneralBounds

/-!
# Closed bounds for all selected paths in a six-way right disjunction

The syntax tree is `a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f`. One closed-formula code budget
controls every selected path and no certificate is required for an unselected
leaf.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactPAHybridFiveRightDisjunctionClosedGeneralBounds

def sixRightDisjunctionPathZeroPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource

def sixRightDisjunctionPathOnePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)

def sixRightDisjunctionPathTwoPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (fiveRightDisjunctionPathOnePayloadEnvelope syntaxResource childResource)

def sixRightDisjunctionPathThreePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (fiveRightDisjunctionPathTwoPayloadEnvelope syntaxResource childResource)

def sixRightDisjunctionPathFourPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (fiveRightDisjunctionPathThreePayloadEnvelope syntaxResource childResource)

def sixRightDisjunctionPathFivePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  sixRightDisjunctionPathFourPayloadEnvelope syntaxResource childResource

private theorem binaryFormulaCode_or_left_le_six
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le_six
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem sixRightOuterParts
    (a b c d e f : ValuationFormula)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (syntaxResource : Nat)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    a.freeVariables = ∅ ∧
    (b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅ ∧
    (binaryFormulaCode a).length <= syntaxResource ∧
    (binaryFormulaCode (b ⋎ c ⋎ d ⋎ e ⋎ f)).length <= syntaxResource := by
  have hc := Finset.union_eq_empty.mp (by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_or] using hclosed)
  exact ⟨hc.1, hc.2,
    (binaryFormulaCode_or_left_le_six a (b ⋎ c ⋎ d ⋎ e ⋎ f)).trans hcode,
    (binaryFormulaCode_or_right_le_six a (b ⋎ c ⋎ d ⋎ e ⋎ f)).trans hcode⟩

theorem sixRightDisjunctionPathZeroTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d e f : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    transparentHybridDisjunctionLeftPayloadEnvelope valuation a
        (b ⋎ c ⋎ d ⋎ e ⋎ f) childResource <=
      sixRightDisjunctionPathZeroPayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables
            valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  unfold sixRightDisjunctionPathZeroPayloadEnvelope
  exact transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation a
    (b ⋎ c ⋎ d ⋎ e ⋎ f) childResource syntaxResource hpositive hcontext
    hp.2.2.1 hp.2.2.2 hcode

theorem sixRightDisjunctionPathOneTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d e f : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a
        (b ⋎ c ⋎ d ⋎ e ⋎ f)
        (transparentHybridDisjunctionLeftPayloadEnvelope valuation b
          (c ⋎ d ⋎ e ⋎ f) childResource) <=
      sixRightDisjunctionPathOnePayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htailClosed := hp.2.1
  have htailCode := hp.2.2.2
  have hbc :
      b.freeVariables = ∅ ∧
      (c ⋎ d ⋎ e ⋎ f).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or] at htailClosed
    exact Finset.union_eq_empty.mp htailClosed
  have htailContext :
      formulaCodeSum
          (valuationContext (b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables valuation) <=
        syntaxResource := by
    rw [hp.2.1]
    simp [valuationContext, formulaCodeSum]
  have hbCode :=
    (binaryFormulaCode_or_left_le_six b (c ⋎ d ⋎ e ⋎ f)).trans htailCode
  have hrestCode :=
    (binaryFormulaCode_or_right_le_six b (c ⋎ d ⋎ e ⋎ f)).trans htailCode
  have hinner :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation b
      (c ⋎ d ⋎ e ⋎ f) childResource syntaxResource hpositive htailContext
      hbCode hrestCode htailCode
  have hmono :=
    transparentHybridDisjunctionRightPayloadEnvelope_mono valuation a
      (b ⋎ c ⋎ d ⋎ e ⋎ f) hinner
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables
            valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have houter :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation a
      (b ⋎ c ⋎ d ⋎ e ⋎ f)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hpositive hcontext hp.2.2.1 hp.2.2.2 hcode
  unfold sixRightDisjunctionPathOnePayloadEnvelope
  exact hmono.trans houter

theorem sixRightDisjunctionPathTwoTransparentEnvelope_le_closedGeneral
    (valuation : Nat -> Nat)
    (a b c d e f : ValuationFormula)
    (childResource syntaxResource : Nat)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    transparentHybridDisjunctionRightPayloadEnvelope valuation a
        (b ⋎ c ⋎ d ⋎ e ⋎ f)
        (transparentHybridDisjunctionRightPayloadEnvelope valuation b
          (c ⋎ d ⋎ e ⋎ f)
          (transparentHybridDisjunctionLeftPayloadEnvelope valuation c
            (d ⋎ e ⋎ f) childResource)) <=
      sixRightDisjunctionPathTwoPayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htail1Closed := hp.2.1
  have htail1Code := hp.2.2.2
  have hbc :
      b.freeVariables = ∅ ∧
      (c ⋎ d ⋎ e ⋎ f).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or] at htail1Closed
    exact Finset.union_eq_empty.mp htail1Closed
  have hbCode :=
    (binaryFormulaCode_or_left_le_six b (c ⋎ d ⋎ e ⋎ f)).trans htail1Code
  have htail2Code :=
    (binaryFormulaCode_or_right_le_six b (c ⋎ d ⋎ e ⋎ f)).trans htail1Code
  have htail2Closed := hbc.2
  have hcd :
      c.freeVariables = ∅ ∧ (d ⋎ e ⋎ f).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or] at htail2Closed
    exact Finset.union_eq_empty.mp htail2Closed
  have hcCode :=
    (binaryFormulaCode_or_left_le_six c (d ⋎ e ⋎ f)).trans htail2Code
  have hrestCode :=
    (binaryFormulaCode_or_right_le_six c (d ⋎ e ⋎ f)).trans htail2Code
  have htail2Context :
      formulaCodeSum
          (valuationContext (c ⋎ d ⋎ e ⋎ f).freeVariables valuation) <=
        syntaxResource := by
    rw [hbc.2]
    simp [valuationContext, formulaCodeSum]
  have hinner :=
    transparentHybridDisjunctionLeftPayloadEnvelope_le_general valuation c
      (d ⋎ e ⋎ f) childResource syntaxResource hpositive htail2Context hcCode
      hrestCode htail2Code
  have hmiddleMono :=
    transparentHybridDisjunctionRightPayloadEnvelope_mono valuation b
      (c ⋎ d ⋎ e ⋎ f) hinner
  have htail1Context :
      formulaCodeSum
          (valuationContext (b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables valuation) <=
        syntaxResource := by
    rw [hp.2.1]
    simp [valuationContext, formulaCodeSum]
  have hmiddleGeneral :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation b
      (c ⋎ d ⋎ e ⋎ f)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hpositive htail1Context hbCode htail2Code htail1Code
  have hmiddle := hmiddleMono.trans hmiddleGeneral
  have houterMono :=
    transparentHybridDisjunctionRightPayloadEnvelope_mono valuation a
      (b ⋎ c ⋎ d ⋎ e ⋎ f) hmiddle
  have hcontext :
      formulaCodeSum
          (valuationContext (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables
            valuation) <=
        syntaxResource := by
    rw [hclosed]
    simp [valuationContext, formulaCodeSum]
  have houterGeneral :=
    transparentHybridDisjunctionRightPayloadEnvelope_le_general valuation a
      (b ⋎ c ⋎ d ⋎ e ⋎ f)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource))
      syntaxResource hpositive hcontext hp.2.2.1 hp.2.2.2 hcode
  unfold sixRightDisjunctionPathTwoPayloadEnvelope
    fiveRightDisjunctionPathOnePayloadEnvelope
  exact houterMono.trans houterGeneral

theorem sixRightDisjunctionPathZeroPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (a b c d e f : ValuationFormula)
    (selected : CheckedHybridValuationBoundedFormulaCertificate valuation a)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionLeft (right := b ⋎ c ⋎ d ⋎ e ⋎ f) selected) <=
      sixRightDisjunctionPathZeroPayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  unfold sixRightDisjunctionPathZeroPayloadEnvelope
  exact checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
    childResource syntaxResource hselected hpositive hp.1 hp.2.1 hp.2.2.1
    hp.2.2.2 hcode

theorem sixRightDisjunctionPathOnePayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (a b c d e f : ValuationFormula)
    (selected : CheckedHybridValuationBoundedFormulaCertificate valuation b)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionLeft (right := c ⋎ d ⋎ e ⋎ f) selected)) <=
      sixRightDisjunctionPathOnePayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htailClosed := hp.2.1
  have htailCode := hp.2.2.2
  have hbc :
      b.freeVariables = ∅ ∧
      (c ⋎ d ⋎ e ⋎ f).freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or] at htailClosed
    exact Finset.union_eq_empty.mp htailClosed
  have hbCode :=
    (binaryFormulaCode_or_left_le_six b (c ⋎ d ⋎ e ⋎ f)).trans htailCode
  have hrestCode :=
    (binaryFormulaCode_or_right_le_six b (c ⋎ d ⋎ e ⋎ f)).trans htailCode
  have hinner :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
      childResource syntaxResource hselected hpositive hbc.1 hbc.2 hbCode
      hrestCode htailCode
  unfold sixRightDisjunctionPathOnePayloadEnvelope
  exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
    (.disjunctionLeft (right := c ⋎ d ⋎ e ⋎ f) selected)
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
    syntaxResource hinner hpositive hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hcode

theorem sixRightDisjunctionPathTwoPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (a b c d e f : ValuationFormula)
    (selected : CheckedHybridValuationBoundedFormulaCertificate valuation c)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionLeft (right := d ⋎ e ⋎ f) selected))) <=
      sixRightDisjunctionPathTwoPayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htail :=
    fiveRightDisjunctionPathOnePayloadBound_le_closedGeneral b c d e f
      selected childResource syntaxResource hselected hpositive hp.2.1 hp.2.2.2
  unfold sixRightDisjunctionPathTwoPayloadEnvelope
  exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
    (.disjunctionRight (left := b)
      (.disjunctionLeft (right := d ⋎ e ⋎ f) selected))
    (fiveRightDisjunctionPathOnePayloadEnvelope syntaxResource childResource)
    syntaxResource htail hpositive hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hcode

theorem sixRightDisjunctionPathThreePayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (a b c d e f : ValuationFormula)
    (selected : CheckedHybridValuationBoundedFormulaCertificate valuation d)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionRight (left := c)
              (.disjunctionLeft (right := e ⋎ f) selected)))) <=
      sixRightDisjunctionPathThreePayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htail :=
    fiveRightDisjunctionPathTwoPayloadBound_le_closedGeneral b c d e f
      selected childResource syntaxResource hselected hpositive hp.2.1 hp.2.2.2
  unfold sixRightDisjunctionPathThreePayloadEnvelope
  exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
    (.disjunctionRight (left := b)
      (.disjunctionRight (left := c)
        (.disjunctionLeft (right := e ⋎ f) selected)))
    (fiveRightDisjunctionPathTwoPayloadEnvelope syntaxResource childResource)
    syntaxResource htail hpositive hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hcode

theorem sixRightDisjunctionPathFourPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (a b c d e f : ValuationFormula)
    (selected : CheckedHybridValuationBoundedFormulaCertificate valuation e)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionRight (left := c)
              (.disjunctionRight (left := d)
                (.disjunctionLeft (right := f) selected))))) <=
      sixRightDisjunctionPathFourPayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htail :=
    fiveRightDisjunctionPathThreeLeftPayloadBound_le_closedGeneral b c d e f
      selected childResource syntaxResource hselected hpositive hp.2.1 hp.2.2.2
  unfold sixRightDisjunctionPathFourPayloadEnvelope
  exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
    (.disjunctionRight (left := b)
      (.disjunctionRight (left := c)
        (.disjunctionRight (left := d)
          (.disjunctionLeft (right := f) selected))))
    (fiveRightDisjunctionPathThreePayloadEnvelope syntaxResource childResource)
    syntaxResource htail hpositive hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hcode

theorem sixRightDisjunctionPathFivePayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (a b c d e f : ValuationFormula)
    (selected : CheckedHybridValuationBoundedFormulaCertificate valuation f)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed : (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode (a ⋎ b ⋎ c ⋎ d ⋎ e ⋎ f)).length <=
        syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (.disjunctionRight (left := a)
          (.disjunctionRight (left := b)
            (.disjunctionRight (left := c)
              (.disjunctionRight (left := d)
                (.disjunctionRight (left := e) selected))))) <=
      sixRightDisjunctionPathFivePayloadEnvelope syntaxResource
        childResource := by
  have hp := sixRightOuterParts a b c d e f hclosed syntaxResource hcode
  have htail :=
    fiveRightDisjunctionPathThreeRightPayloadBound_le_closedGeneral b c d e f
      selected childResource syntaxResource hselected hpositive hp.2.1 hp.2.2.2
  unfold sixRightDisjunctionPathFivePayloadEnvelope
    sixRightDisjunctionPathFourPayloadEnvelope
  exact checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
    (.disjunctionRight (left := b)
      (.disjunctionRight (left := c)
        (.disjunctionRight (left := d)
          (.disjunctionRight (left := e) selected))))
    (fiveRightDisjunctionPathThreePayloadEnvelope syntaxResource childResource)
    syntaxResource htail hpositive hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 hcode

end FoundationCompactPAHybridSixRightDisjunctionClosedGeneralBounds
