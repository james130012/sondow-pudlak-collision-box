import integration.FoundationCompactNumericListedDirectSimpleCombineTransitionRows

/-!
# Constructors for the simple successful combine rows

These are the converse constructors for conjunction, disjunction, and
weakening.  Real child-result heads and the semantic pushed target stack
produce every field of the corresponding bounded transition rows.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectSimpleCombineTransitionRowsCompleteness

open FoundationCompactNumericListedRuleChecks
open FoundationCompactNumericListedDirectAdditiveTypeCanonical
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectNatListListRowsFormula
open FoundationCompactNumericListedDirectVerifierChildResultListRowsFormula
open FoundationCompactNumericListedDirectChildResultBoundedHeadEquality
open FoundationCompactNumericListedDirectChildResultListPushDropRows
open FoundationCompactNumericListedDirectSimpleCombineRuleRows
open FoundationCompactNumericListedDirectSimpleCombineTransitionRows
open FoundationCompactNumericListedDirectAndRuleCheck
open FoundationCompactNumericListedDirectOrRuleCheck
open FoundationCompactNumericListedDirectWkRuleCheck

theorem CompactNumericSimpleCombineTransitionRows.of_and
    {tokenTable width tokenCount taskTag
      gammaFinish gammaBoundary firstFinish secondFinish
      rightGammaBoundary rightBoolValue
      leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary tableWidth valueBound : Nat}
    {Gamma : List (List Nat)} {firstFormula secondFormula : List Nat}
    {rightConclusion leftConclusion : List (List Nat)}
    {rightValid leftValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hfirst : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish firstFormula)
    (hsecond : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount firstFinish secondFinish secondFormula)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightGammaBoundary rightConclusion)
    (hleft : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        leftGammaBoundary leftConclusion)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid)
    (hleftBool : leftBoolValue = compactAdditiveBoolTag leftValid)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htag : taskTag = 3)
    (hsourceCount : 2 ≤ source.length)
    (hrightValue : source.getI 0 = (rightConclusion, rightValid))
    (hleftValue : source.getI 1 = (leftConclusion, leftValid))
    (htarget : target =
      (Gamma, compactAndRuleCheck
        (Gamma, firstFormula, secondFormula,
          (leftConclusion, leftValid), rightConclusion, rightValid)) ::
        source.drop 2) :
    CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish Gamma.length gammaBoundary
      firstFinish firstFormula.length secondFinish secondFormula.length
      rightConclusion.length rightGammaBoundary rightBoolValue
      leftConclusion.length leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound
      (compactAdditiveBoolTag
        (compactAndRuleCheck
          (Gamma, firstFormula, secondFormula,
            (leftConclusion, leftValid), rightConclusion, rightValid))) := by
  let result := compactAndRuleCheck
    (Gamma, firstFormula, secondFormula,
      (leftConclusion, leftValid), rightConclusion, rightValid)
  have hcheck : CompactAdditiveAndRuleCheck tokenTable width tokenCount
      gammaBoundary Gamma.length
      gammaFinish firstFinish firstFormula.length
      firstFinish secondFinish secondFormula.length
      leftGammaBoundary leftConclusion.length leftBoolValue
      rightGammaBoundary rightConclusion.length rightBoolValue
      (compactAdditiveBoolTag result) :=
    (compactAdditiveAndRuleCheck_iff
      hGamma hfirst hsecond hleft hright hleftBool hrightBool).mpr rfl
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 2
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hrightHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hright hsourceRows hrightValue
  have hrightHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      rightGammaBoundary rightConclusion.length valueBound
      0 rightBoolValue := by
    simpa only [hrightBool] using hrightHeadCanonical
  have hleftHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hleft hsourceRows hleftValue
  have hleftHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      leftGammaBoundary leftConclusion.length valueBound
      1 leftBoolValue := by
    simpa only [hleftBool] using hleftHeadCanonical
  refine ⟨Or.inl ⟨htag, hsourceCount, hcheck, hpush⟩,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hright,
    hrightHead, ?_⟩
  intro _htagThree
  exact ⟨
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hleft,
    hleftHead⟩

theorem CompactNumericSimpleCombineTransitionRows.of_or
    {tokenTable width tokenCount taskTag
      gammaFinish gammaBoundary firstFinish secondFinish
      rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary tableWidth valueBound : Nat}
    {Gamma : List (List Nat)} {firstFormula secondFormula : List Nat}
    {rightConclusion : List (List Nat)} {rightValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hfirst : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount gammaFinish firstFinish firstFormula)
    (hsecond : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount firstFinish secondFinish secondFormula)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightGammaBoundary rightConclusion)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htag : taskTag = 4)
    (hsourceCount : 1 ≤ source.length)
    (hrightValue : source.getI 0 = (rightConclusion, rightValid))
    (htarget : target =
      (Gamma, compactOrRuleCheck
        (Gamma, firstFormula, secondFormula,
          rightConclusion, rightValid)) :: source.drop 1) :
    CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish Gamma.length gammaBoundary
      firstFinish firstFormula.length secondFinish secondFormula.length
      rightConclusion.length rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound
      (compactAdditiveBoolTag
        (compactOrRuleCheck
          (Gamma, firstFormula, secondFormula,
            rightConclusion, rightValid))) := by
  let result := compactOrRuleCheck
    (Gamma, firstFormula, secondFormula, rightConclusion, rightValid)
  have hcheck : CompactAdditiveOrRuleCheck tokenTable width tokenCount
      gammaBoundary Gamma.length
      gammaFinish firstFinish firstFormula.length
      firstFinish secondFinish secondFormula.length
      rightGammaBoundary rightConclusion.length rightBoolValue
      (compactAdditiveBoolTag result) :=
    (compactAdditiveOrRuleCheck_iff
      hGamma hfirst hsecond hright hrightBool).mpr rfl
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 1
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hrightHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hright hsourceRows hrightValue
  have hrightHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      rightGammaBoundary rightConclusion.length valueBound
      0 rightBoolValue := by
    simpa only [hrightBool] using hrightHeadCanonical
  refine ⟨Or.inr <| Or.inl ⟨htag, hsourceCount, hcheck, hpush⟩,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hright,
    hrightHead, ?_⟩
  intro htagThree
  omega

theorem CompactNumericSimpleCombineTransitionRows.of_wk
    {tokenTable width tokenCount taskTag
      gammaFinish gammaBoundary firstFinish firstCount secondFinish secondCount
      rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary targetBoundary tableWidth valueBound : Nat}
    {Gamma rightConclusion : List (List Nat)} {rightValid : Bool}
    {source target : List CompactNumericChildResult}
    (hGamma : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        gammaBoundary Gamma)
    (hright : CompactAdditiveStructuredListElementRowLayouts
      CompactAdditiveNatListDirectLayout tokenTable width tokenCount
        rightGammaBoundary rightConclusion)
    (hrightBool : rightBoolValue = compactAdditiveBoolTag rightValid)
    (hsourceRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        sourceBoundary source)
    (htargetRows : CompactAdditiveStructuredListElementRowLayouts
      CompactNumericChildResultDirectLayout tokenTable width tokenCount
        targetBoundary target)
    (hsourceGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount sourceBoundary source.length
        tableWidth valueBound)
    (htargetGraph : CompactNumericChildResultListRowsGraph
      tokenTable width tokenCount targetBoundary target.length
        tableWidth valueBound)
    (htag : taskTag = 7)
    (hsourceCount : 1 ≤ source.length)
    (hrightValue : source.getI 0 = (rightConclusion, rightValid))
    (htarget : target =
      (Gamma, compactWkRuleCheck
        (Gamma, rightConclusion, rightValid)) :: source.drop 1) :
    CompactNumericSimpleCombineTransitionRows
      tokenTable width tokenCount
      taskTag gammaFinish Gamma.length gammaBoundary
      firstFinish firstCount secondFinish secondCount
      rightConclusion.length rightGammaBoundary rightBoolValue
      leftGammaCount leftGammaBoundary leftBoolValue
      sourceBoundary source.length targetBoundary target.length
      tableWidth valueBound
      (compactAdditiveBoolTag
        (compactWkRuleCheck (Gamma, rightConclusion, rightValid))) := by
  let result := compactWkRuleCheck (Gamma, rightConclusion, rightValid)
  have hcheck : CompactAdditiveWkRuleCheck tokenTable width tokenCount
      gammaBoundary Gamma.length
      rightGammaBoundary rightConclusion.length rightBoolValue
      (compactAdditiveBoolTag result) :=
    (compactAdditiveWkRuleCheck_iff hGamma hright hrightBool).mpr rfl
  have hpush : CompactNumericChildResultListPushDropRows
      tokenTable width tokenCount
      sourceBoundary source.length targetBoundary target.length
      gammaBoundary Gamma.length tableWidth valueBound 1
      (compactAdditiveBoolTag result) :=
    CompactAdditiveStructuredListElementRowLayouts.childResultPushDropRows
      hsourceRows htargetRows hGamma hsourceGraph htargetGraph
      hsourceCount (by simpa [result] using htarget)
  have hrightHeadCanonical :=
    CompactNumericChildResultBoundedHeadEq.of_value_eq
      hsourceGraph (by omega) hright hsourceRows hrightValue
  have hrightHead : CompactNumericChildResultBoundedHeadEq
      tokenTable width tokenCount sourceBoundary
      rightGammaBoundary rightConclusion.length valueBound
      0 rightBoolValue := by
    simpa only [hrightBool] using hrightHeadCanonical
  refine ⟨Or.inr <| Or.inr ⟨htag, hsourceCount, hcheck, hpush⟩,
    CompactAdditiveStructuredListElementRowLayouts.natListListRowsWellFormed
      hright,
    hrightHead, ?_⟩
  intro htagThree
  omega

#print axioms CompactNumericSimpleCombineTransitionRows.of_and
#print axioms CompactNumericSimpleCombineTransitionRows.of_or
#print axioms CompactNumericSimpleCombineTransitionRows.of_wk

end FoundationCompactNumericListedDirectSimpleCombineTransitionRowsCompleteness
