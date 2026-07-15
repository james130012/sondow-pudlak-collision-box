import integration.FoundationCompactNumericListedDirectFormulaTransformStateFormula
import integration.FoundationCompactNumericListedDirectNatListSameRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskListSameRows
import integration.FoundationCompactNumericListedDirectSyntaxTaskBoundaryRigidity

/-!
# Determinacy of direct formula-transform state layouts

The additive encodings used by formula-transform traces are self-delimiting.
Consequently, two typed layouts beginning at the same token cursor decode the
same parser state and emitted output and finish at the same cursor.  This is
the gluing lemma needed to identify the shared row between adjacent bounded
trace-step certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy

open FoundationCompactParserDirectTrace
open FoundationCompactSyntaxTokenMachine
open FoundationCompactNumericFormulaTransformTrace
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectAdditiveTypeLayouts
open FoundationCompactNumericListedDirectAtomicListLayouts
open FoundationCompactNumericListedDirectNatListBoundaryRigidity
open FoundationCompactNumericListedDirectNatListSameRows
open FoundationCompactNumericListedDirectSyntaxTaskLayout
open FoundationCompactNumericListedDirectSyntaxTaskRowRealization
open FoundationCompactNumericListedDirectSyntaxTaskBoundaryRigidity
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows
open FoundationCompactNumericListedDirectBinaryNatStreamStatusLayout
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectVerifierValueLayouts
open FoundationCompactNumericListedDirectFormulaTransformStateFormula

private theorem structuredList_count_eq_of_same_start
    {tokenTable width tokenCount start
      leftCount leftFinish leftBoundary
      rightCount rightFinish rightBoundary : Nat}
    (hleft : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start leftCount leftFinish leftBoundary)
    (hright : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start rightCount rightFinish rightBoundary) :
    leftCount = rightCount := by
  rcases hleft with
    ⟨_leftBody, _hleftBody, hleftHeader, _hleftBoundary⟩
  rcases hright with
    ⟨_rightBody, _hrightBody, hrightHeader, _hrightBoundary⟩
  exact (CompactAdditiveTokenCell.value_eq_tableValue hleftHeader.1).trans
    (CompactAdditiveTokenCell.value_eq_tableValue hrightHeader.1).symm

theorem CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
    {tokenTable width tokenCount start leftFinish rightFinish : Nat}
    {left right : List Nat}
    (hleft : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start leftFinish left)
    (hright : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount start rightFinish right) :
    right = left ∧ rightFinish = leftFinish := by
  rcases hleft with
    ⟨leftBoundary, hleftLayout, hleftRows, _hleftSize⟩
  rcases hright with
    ⟨rightBoundary, hrightLayout, hrightRows, _hrightSize⟩
  have hlength : left.length = right.length :=
    structuredList_count_eq_of_same_start hleftLayout hrightLayout
  have hleftUnit : CompactAdditiveUnitBoundaryRows
      tokenCount left.length leftBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hleftRows
  have hrightUnit : CompactAdditiveUnitBoundaryRows
      tokenCount right.length rightBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.natUnitBoundaryRows
      hrightRows
  have hleftFinish :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      hleftLayout hleftUnit
  have hrightFinish :=
    CompactAdditiveStructuredListLayout.finish_eq_start_add_count
      hrightLayout hrightUnit
  have hfinish : rightFinish = leftFinish := by omega
  have hrightLayout' : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start left.length leftFinish
        rightBoundary := by
    simpa only [← hlength, hfinish] using hrightLayout
  have hrightUnit' : CompactAdditiveUnitBoundaryRows
      tokenCount left.length rightBoundary := by
    simpa only [← hlength] using hrightUnit
  have hleftRowsOnRight :
      CompactAdditiveStructuredListElementRowLayouts
        CompactAdditiveNatValueDirectLayout tokenTable width tokenCount
          rightBoundary left :=
    CompactAdditiveStructuredListElementRowLayouts.natRows_on_unitBoundary
      hleftLayout hleftRows hrightLayout' hrightUnit'
  have hsame : CompactAdditiveNatListSameRows
      tokenTable width tokenCount leftBoundary left.length
        rightBoundary left.length :=
    CompactAdditiveStructuredListElementRowLayouts.natSameRows
      hleftRows hleftRowsOnRight rfl
  have hsame' : CompactAdditiveNatListSameRows
      tokenTable width tokenCount leftBoundary left.length
        rightBoundary right.length := by
    simpa only [← hlength] using hsame
  exact ⟨hsame'.eq_of_rows hleftRows hrightRows, hfinish⟩

private theorem syntaxTaskLists_eq_and_finish_of_same_start
    {tokenTable width tokenCount start leftFinish rightFinish
      leftBoundary rightBoundary : Nat}
    {left right : List CompactSyntaxTask}
    (hleftLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start left.length leftFinish leftBoundary)
    (hleftRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        leftBoundary left)
    (hrightLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start right.length rightFinish rightBoundary)
    (hrightRows : CompactAdditiveStructuredListElementRowLayouts
      CompactSyntaxTaskDirectLayout tokenTable width tokenCount
        rightBoundary right) :
    right = left ∧ rightFinish = leftFinish := by
  have hlength : left.length = right.length :=
    structuredList_count_eq_of_same_start hleftLayout hrightLayout
  have hleftTriple : CompactAdditiveTripleBoundaryRows
      tokenCount left.length leftBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
      hleftRows
  have hrightTriple : CompactAdditiveTripleBoundaryRows
      tokenCount right.length rightBoundary :=
    CompactAdditiveStructuredListElementRowLayouts.tripleBoundaryRows
      hrightRows
  have hleftFinish :=
    CompactAdditiveStructuredListLayout.taskFinish_eq_start_add_count
      hleftLayout hleftTriple
  have hrightFinish :=
    CompactAdditiveStructuredListLayout.taskFinish_eq_start_add_count
      hrightLayout hrightTriple
  have hfinish : rightFinish = leftFinish := by omega
  have hrightLayout' : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount start left.length leftFinish
        rightBoundary := by
    simpa only [← hlength, hfinish] using hrightLayout
  have hrightTriple' : CompactAdditiveTripleBoundaryRows
      tokenCount left.length rightBoundary := by
    simpa only [← hlength] using hrightTriple
  have hleftRowsOnRight :
      CompactAdditiveStructuredListElementRowLayouts
        CompactSyntaxTaskDirectLayout tokenTable width tokenCount
          rightBoundary left :=
    CompactAdditiveStructuredListElementRowLayouts.taskRows_on_tripleBoundary
      hleftLayout hleftRows hrightLayout' hrightTriple'
  have hsame : CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount leftBoundary left.length
        rightBoundary left.length :=
    CompactAdditiveStructuredListElementRowLayouts.taskSameRows
      hleftRows hleftRowsOnRight rfl
  have hsame' : CompactAdditiveSyntaxTaskListSameRows
      tokenTable width tokenCount leftBoundary left.length
        rightBoundary right.length := by
    simpa only [← hlength] using hsame
  exact ⟨hsame'.eq_of_rows hleftRows hrightRows, hfinish⟩

private theorem option_zero_finish
    {tokenTable width tokenCount start payloadStart finish : Nat}
    (hlayout : CompactAdditiveOptionLayout
      tokenTable width tokenCount start 0 payloadStart finish) :
    payloadStart = start + 1 ∧ finish = payloadStart := by
  have hpayload : payloadStart = start + 1 := hlayout.1.2.1
  rcases hlayout.2 with hzero | hone
  · exact ⟨hpayload, hzero.2⟩
  · omega

theorem CompactBinaryNatStreamStatusDirectLayout.eq_and_finish_of_same_start
    {tokenTable width tokenCount start leftFinish rightFinish : Nat}
    {left right : Option (Option (List Nat))}
    (hleft : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start leftFinish left)
    (hright : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount start rightFinish right) :
    right = left ∧ rightFinish = leftFinish := by
  cases left with
  | none =>
      rcases hleft with ⟨leftPayload, hleftOuter, _⟩
      rcases option_zero_finish hleftOuter with
        ⟨hleftPayload, hleftFinish⟩
      cases right with
      | none =>
          rcases hright with ⟨rightPayload, hrightOuter, _⟩
          rcases option_zero_finish hrightOuter with
            ⟨hrightPayload, hrightFinish⟩
          exact ⟨rfl, by omega⟩
      | some rightInner =>
          rcases hright with
            ⟨_rightPayload, hrightOuter, _rightInnerPayload,
              _hrightInner, _hrightPayload⟩
          have hzeroOne : 0 = 1 :=
            CompactAdditiveTokenCell.value_eq_of_same_cursor
              hleftOuter.1 hrightOuter.1
          omega
  | some leftInner =>
      rcases hleft with
        ⟨leftOuterPayload, hleftOuter, leftInnerPayload,
          hleftInner, hleftPayload⟩
      cases right with
      | none =>
          rcases hright with ⟨_rightPayload, hrightOuter, _⟩
          have honeZero : 1 = 0 :=
            CompactAdditiveTokenCell.value_eq_of_same_cursor
              hleftOuter.1 hrightOuter.1
          omega
      | some rightInner =>
          rcases hright with
            ⟨rightOuterPayload, hrightOuter, rightInnerPayload,
              hrightInner, hrightPayload⟩
          have houterPayload :
              rightOuterPayload = leftOuterPayload := by
            have hleftNext := hleftOuter.1.2.1
            have hrightNext := hrightOuter.1.2.1
            omega
          subst rightOuterPayload
          cases leftInner with
          | none =>
              rcases option_zero_finish hleftInner with
                ⟨hleftInnerPayload, hleftFinish⟩
              cases rightInner with
              | none =>
                  rcases option_zero_finish hrightInner with
                    ⟨hrightInnerPayload, hrightFinish⟩
                  exact ⟨rfl, by omega⟩
              | some rightOutput =>
                  rcases hrightPayload with
                    ⟨_rightBoundary, _hrightLayout,
                      _hrightRows, _hrightSize⟩
                  have hzeroOne : 0 = 1 :=
                    CompactAdditiveTokenCell.value_eq_of_same_cursor
                      hleftInner.1 hrightInner.1
                  omega
          | some leftOutput =>
              rcases hleftPayload with
                ⟨leftBoundary, hleftOutputLayout,
                  hleftOutputRows, hleftOutputSize⟩
              cases rightInner with
              | none =>
                  have honeZero : 1 = 0 :=
                    CompactAdditiveTokenCell.value_eq_of_same_cursor
                      hleftInner.1 hrightInner.1
                  omega
              | some rightOutput =>
                  rcases hrightPayload with
                    ⟨rightBoundary, hrightOutputLayout,
                      hrightOutputRows, hrightOutputSize⟩
                  have hinnerPayload :
                      rightInnerPayload = leftInnerPayload := by
                    have hleftNext := hleftInner.1.2.1
                    have hrightNext := hrightInner.1.2.1
                    omega
                  subst rightInnerPayload
                  let hleftOutput : CompactAdditiveNatListDirectLayout
                      tokenTable width tokenCount leftInnerPayload
                        leftFinish leftOutput :=
                    ⟨leftBoundary, hleftOutputLayout,
                      hleftOutputRows, hleftOutputSize⟩
                  let hrightOutput : CompactAdditiveNatListDirectLayout
                      tokenTable width tokenCount leftInnerPayload
                        rightFinish rightOutput :=
                    ⟨rightBoundary, hrightOutputLayout,
                      hrightOutputRows, hrightOutputSize⟩
                  rcases
                      CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
                        hleftOutput hrightOutput with
                    ⟨houtput, hfinish⟩
                  exact
                    ⟨congrArg some (congrArg some houtput), hfinish⟩

theorem CompactUnifiedParserStateFixedLayout.eq_and_finish_of_same_start
    {tokenTable width tokenCount : Nat}
    {leftCoordinates rightCoordinates : CompactUnifiedParserStateRowCoordinates}
    {left right : CompactUnifiedParserState}
    (hstart : rightCoordinates.start = leftCoordinates.start)
    (hleft : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount leftCoordinates left)
    (hright : CompactUnifiedParserStateFixedLayout
      tokenTable width tokenCount rightCoordinates right) :
    right = left ∧ rightCoordinates.finish = leftCoordinates.finish := by
  let hleftTokens : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount leftCoordinates.start
        leftCoordinates.tokensFinish left.1 :=
    ⟨leftCoordinates.tokensBoundary,
      (by simpa only [hleft.tokensCount_eq] using hleft.tokensLayout),
      hleft.tokensRows,
      (by simpa only [hleft.tokensCount_eq] using
        hleft.tokensBoundarySize)⟩
  let hrightTokens : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount leftCoordinates.start
        rightCoordinates.tokensFinish right.1 :=
    ⟨rightCoordinates.tokensBoundary,
      (by simpa only [hstart, hright.tokensCount_eq] using
        hright.tokensLayout),
      hright.tokensRows,
      (by simpa only [hright.tokensCount_eq] using
        hright.tokensBoundarySize)⟩
  rcases
      CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hleftTokens hrightTokens with
    ⟨htokens, htokensFinish⟩
  have hrightTasksLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount leftCoordinates.tokensFinish
        right.2.1.length rightCoordinates.tasksFinish
        rightCoordinates.tasksBoundary := by
    simpa only [htokensFinish, hright.tasksCount_eq] using
      hright.tasksLayout
  have hleftTasksLayout : CompactAdditiveStructuredListLayout
      tokenTable width tokenCount leftCoordinates.tokensFinish
        left.2.1.length leftCoordinates.tasksFinish
        leftCoordinates.tasksBoundary := by
    simpa only [hleft.tasksCount_eq] using hleft.tasksLayout
  rcases syntaxTaskLists_eq_and_finish_of_same_start
      hleftTasksLayout hleft.tasksRows
      hrightTasksLayout hright.tasksRows with
    ⟨htasks, htasksFinish⟩
  have hrightStatus : CompactBinaryNatStreamStatusDirectLayout
      tokenTable width tokenCount leftCoordinates.tasksFinish
        rightCoordinates.finish right.2.2 := by
    simpa only [htasksFinish] using hright.statusLayout
  rcases
      CompactBinaryNatStreamStatusDirectLayout.eq_and_finish_of_same_start
        hleft.statusLayout hrightStatus with
    ⟨hstatus, hfinish⟩
  exact ⟨Prod.ext htokens (Prod.ext htasks hstatus), hfinish⟩

theorem CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start
    {tokenTable width tokenCount : Nat}
    {leftCoordinates rightCoordinates : CompactFormulaTransformStateRowCoordinates}
    {left right : CompactFormulaTransformState}
    (hstart : rightCoordinates.start = leftCoordinates.start)
    (hleft : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount leftCoordinates left)
    (hright : CompactFormulaTransformStateFixedLayout
      tokenTable width tokenCount rightCoordinates right) :
    right = left ∧ rightCoordinates.finish = leftCoordinates.finish := by
  have hparserStart :
      rightCoordinates.parser.start = leftCoordinates.parser.start := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using hstart
  rcases
      CompactUnifiedParserStateFixedLayout.eq_and_finish_of_same_start
        hparserStart hleft.parserLayout hright.parserLayout with
    ⟨hparser, hparserFinish⟩
  have hparserFinish' :
      rightCoordinates.parserFinish = leftCoordinates.parserFinish := by
    simpa [CompactFormulaTransformStateRowCoordinates.parser] using
      hparserFinish
  let hleftOutput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount leftCoordinates.parserFinish
        leftCoordinates.finish left.2 :=
    ⟨leftCoordinates.outputBoundary,
      (by simpa only [hleft.outputCount_eq] using hleft.outputLayout),
      hleft.outputRows,
      (by simpa only [hleft.outputCount_eq] using
        hleft.outputBoundarySize)⟩
  let hrightOutput : CompactAdditiveNatListDirectLayout
      tokenTable width tokenCount leftCoordinates.parserFinish
        rightCoordinates.finish right.2 :=
    ⟨rightCoordinates.outputBoundary,
      (by simpa only [hparserFinish', hright.outputCount_eq] using
        hright.outputLayout),
      hright.outputRows,
      (by simpa only [hright.outputCount_eq] using
        hright.outputBoundarySize)⟩
  rcases
      CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
        hleftOutput hrightOutput with
    ⟨houtput, hfinish⟩
  exact ⟨Prod.ext hparser houtput, hfinish⟩

#print axioms CompactAdditiveNatListDirectLayout.eq_and_finish_of_same_start
#print axioms CompactBinaryNatStreamStatusDirectLayout.eq_and_finish_of_same_start
#print axioms CompactUnifiedParserStateFixedLayout.eq_and_finish_of_same_start
#print axioms CompactFormulaTransformStateFixedLayout.eq_and_finish_of_same_start

end FoundationCompactNumericListedDirectFormulaTransformStateDeterminacy
