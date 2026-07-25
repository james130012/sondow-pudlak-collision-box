import integration.FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Closed bounds for paths in a five-way right-associated disjunction

The syntax tree is `first ⋎ second ⋎ third ⋎ fourth ⋎ fifth`.  A single
closed-formula code budget pays every selected path; no certificate or graph is
required for an unselected leaf.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false

namespace FoundationCompactPAHybridFiveRightDisjunctionClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds

def fiveRightDisjunctionPathOnePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)

def fiveRightDisjunctionPathTwoPayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (fiveRightDisjunctionPathOnePayloadEnvelope syntaxResource childResource)

def fiveRightDisjunctionPathThreePayloadEnvelope
    (syntaxResource childResource : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource
    (fiveRightDisjunctionPathTwoPayloadEnvelope syntaxResource childResource)

private theorem binaryFormulaCode_or_left_le_fivePath
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le_fivePath
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem fiveRightDisjunctionClosedParts
    (first second third fourth fifth : ValuationFormula)
    (hclosed :
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅) :
    first.freeVariables = ∅ ∧
    second.freeVariables = ∅ ∧
    third.freeVariables = ∅ ∧
    fourth.freeVariables = ∅ ∧
    fifth.freeVariables = ∅ := by
  simp only [LO.FirstOrder.Semiformula.freeVariables_or] at hclosed
  simpa only [Finset.union_eq_empty] using hclosed

private theorem fiveRightDisjunctionCodeParts
    (first second third fourth fifth : ValuationFormula)
    (syntaxResource : Nat)
    (hcode :
      (binaryFormulaCode
        (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
          syntaxResource) :
    (binaryFormulaCode first).length <= syntaxResource ∧
    (binaryFormulaCode second).length <= syntaxResource ∧
    (binaryFormulaCode third).length <= syntaxResource ∧
    (binaryFormulaCode fourth).length <= syntaxResource ∧
    (binaryFormulaCode fifth).length <= syntaxResource ∧
    (binaryFormulaCode (second ⋎ third ⋎ fourth ⋎ fifth)).length <=
      syntaxResource ∧
    (binaryFormulaCode (third ⋎ fourth ⋎ fifth)).length <= syntaxResource ∧
    (binaryFormulaCode (fourth ⋎ fifth)).length <= syntaxResource := by
  have hrest2345 :=
    (binaryFormulaCode_or_right_le_fivePath first
      (second ⋎ third ⋎ fourth ⋎ fifth)).trans hcode
  have hrest345 :=
    (binaryFormulaCode_or_right_le_fivePath second
      (third ⋎ fourth ⋎ fifth)).trans hrest2345
  have hrest45 :=
    (binaryFormulaCode_or_right_le_fivePath third
      (fourth ⋎ fifth)).trans hrest345
  exact ⟨
    (binaryFormulaCode_or_left_le_fivePath first
      (second ⋎ third ⋎ fourth ⋎ fifth)).trans hcode,
    (binaryFormulaCode_or_left_le_fivePath second
      (third ⋎ fourth ⋎ fifth)).trans hrest2345,
    (binaryFormulaCode_or_left_le_fivePath third
      (fourth ⋎ fifth)).trans hrest345,
    (binaryFormulaCode_or_left_le_fivePath fourth fifth).trans hrest45,
    (binaryFormulaCode_or_right_le_fivePath fourth fifth).trans hrest45,
    hrest2345, hrest345, hrest45⟩

theorem fiveRightDisjunctionPathOnePayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (first second third fourth fifth : ValuationFormula)
    (selected :
      CheckedHybridValuationBoundedFormulaCertificate valuation second)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
          syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := third ⋎ fourth ⋎ fifth) selected)) <=
      fiveRightDisjunctionPathOnePayloadEnvelope syntaxResource
        childResource := by
  have hc := fiveRightDisjunctionClosedParts first second third fourth fifth
    hclosed
  have hs := fiveRightDisjunctionCodeParts first second third fourth fifth
    syntaxResource hcode
  have hrest345Closed :
      (third ⋎ fourth ⋎ fifth).freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.1,
      hc.2.2.2.1, hc.2.2.2.2, Finset.union_empty]
  have hinner :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
      childResource syntaxResource hselected hpositive hc.2.1 hrest345Closed
      hs.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.1
  unfold fiveRightDisjunctionPathOnePayloadEnvelope
  exact
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := third ⋎ fourth ⋎ fifth) selected)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hinner hpositive hc.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.1,
          hrest345Closed, Finset.union_empty])
      hs.1 hs.2.2.2.2.2.1 hcode

theorem fiveRightDisjunctionPathTwoPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (first second third fourth fifth : ValuationFormula)
    (selected :
      CheckedHybridValuationBoundedFormulaCertificate valuation third)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
          syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := second)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := fourth ⋎ fifth) selected))) <=
      fiveRightDisjunctionPathTwoPayloadEnvelope syntaxResource
        childResource := by
  have hc := fiveRightDisjunctionClosedParts first second third fourth fifth
    hclosed
  have hs := fiveRightDisjunctionCodeParts first second third fourth fifth
    syntaxResource hcode
  have h45Closed : (fourth ⋎ fifth).freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.2.1,
      hc.2.2.2.2, Finset.union_empty]
  have hthirdPath :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
      childResource syntaxResource hselected hpositive hc.2.2.1 h45Closed
      hs.2.2.1 hs.2.2.2.2.2.2.2 hs.2.2.2.2.2.2.1
  have hsecondPath :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := fourth ⋎ fifth) selected)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hthirdPath hpositive hc.2.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.1,
          h45Closed, Finset.union_empty])
      hs.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.1
  unfold fiveRightDisjunctionPathTwoPayloadEnvelope
    fiveRightDisjunctionPathOnePayloadEnvelope
  exact
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := second)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := fourth ⋎ fifth) selected))
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource))
      syntaxResource hsecondPath hpositive hc.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.1,
          hc.2.2.1, h45Closed, Finset.union_empty])
      hs.1 hs.2.2.2.2.2.1 hcode

theorem fiveRightDisjunctionPathThreeLeftPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (first second third fourth fifth : ValuationFormula)
    (selected :
      CheckedHybridValuationBoundedFormulaCertificate valuation fourth)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
          syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := second)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := third)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (right := fifth) selected)))) <=
      fiveRightDisjunctionPathThreePayloadEnvelope syntaxResource
        childResource := by
  have hc := fiveRightDisjunctionClosedParts first second third fourth fifth
    hclosed
  have hs := fiveRightDisjunctionCodeParts first second third fourth fifth
    syntaxResource hcode
  have hfourthPath :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral selected
      childResource syntaxResource hselected hpositive hc.2.2.2.1 hc.2.2.2.2
      hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have hthirdPath :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := fifth) selected)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hfourthPath hpositive hc.2.2.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.2.1,
          hc.2.2.2.2, Finset.union_empty])
      hs.2.2.1 hs.2.2.2.2.2.2.2 hs.2.2.2.2.2.2.1
  have hsecondPath :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := third)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := fifth) selected))
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource))
      syntaxResource hthirdPath hpositive hc.2.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.1,
          hc.2.2.2.1, hc.2.2.2.2, Finset.union_empty])
      hs.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.1
  unfold fiveRightDisjunctionPathThreePayloadEnvelope
    fiveRightDisjunctionPathTwoPayloadEnvelope
    fiveRightDisjunctionPathOnePayloadEnvelope
  exact
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := second)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := third)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := fifth) selected)))
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
          (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
            childResource)))
      syntaxResource hsecondPath hpositive hc.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.1,
          hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, Finset.union_empty])
      hs.1 hs.2.2.2.2.2.1 hcode

theorem fiveRightDisjunctionPathThreeRightPayloadBound_le_closedGeneral
    {valuation : Nat -> Nat}
    (first second third fourth fifth : ValuationFormula)
    (selected :
      CheckedHybridValuationBoundedFormulaCertificate valuation fifth)
    (childResource syntaxResource : Nat)
    (hselected :
      hybridFormulaStructuralPayloadBound selected <= childResource)
    (hpositive : 1 <= syntaxResource)
    (hclosed :
      (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth).freeVariables = ∅)
    (hcode :
      (binaryFormulaCode
        (first ⋎ second ⋎ third ⋎ fourth ⋎ fifth)).length <=
          syntaxResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := first)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := second)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := third)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (left := fourth) selected)))) <=
      fiveRightDisjunctionPathThreePayloadEnvelope syntaxResource
        childResource := by
  have hc := fiveRightDisjunctionClosedParts first second third fourth fifth
    hclosed
  have hs := fiveRightDisjunctionCodeParts first second third fourth fifth
    syntaxResource hcode
  have hfourthPath :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral selected
      childResource syntaxResource hselected hpositive hc.2.2.2.1 hc.2.2.2.2
      hs.2.2.2.1 hs.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have hthirdPath :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := fourth) selected)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource)
      syntaxResource hfourthPath hpositive hc.2.2.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.2.1,
          hc.2.2.2.2, Finset.union_empty])
      hs.2.2.1 hs.2.2.2.2.2.2.2 hs.2.2.2.2.2.2.1
  have hsecondPath :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := third)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := fourth) selected))
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource childResource))
      syntaxResource hthirdPath hpositive hc.2.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.2.1,
          hc.2.2.2.1, hc.2.2.2.2, Finset.union_empty])
      hs.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.1
  unfold fiveRightDisjunctionPathThreePayloadEnvelope
    fiveRightDisjunctionPathTwoPayloadEnvelope
    fiveRightDisjunctionPathOnePayloadEnvelope
  exact
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := second)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := third)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := fourth) selected)))
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
          (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
            childResource)))
      syntaxResource hsecondPath hpositive hc.1
      (by
        simp only [LO.FirstOrder.Semiformula.freeVariables_or, hc.2.1,
          hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, Finset.union_empty])
      hs.1 hs.2.2.2.2.2.1 hcode

#print axioms fiveRightDisjunctionPathOnePayloadBound_le_closedGeneral
#print axioms fiveRightDisjunctionPathTwoPayloadBound_le_closedGeneral
#print axioms fiveRightDisjunctionPathThreeLeftPayloadBound_le_closedGeneral
#print axioms fiveRightDisjunctionPathThreeRightPayloadBound_le_closedGeneral

end FoundationCompactPAHybridFiveRightDisjunctionClosedGeneralBounds
