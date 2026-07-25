import integration.FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler
import integration.FoundationCompactPADirectConnectiveTransparentBounds

/-! # Uniform direct compiler for the completed parser status alternative -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectCompletedStatusSameRows
open FoundationCompactNumericListedDirectCompletedStatusSameRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneUniformDirectCompiler

private abbrev doneStatusZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

noncomputable def compileCompactUnifiedParserDoneStatusUniformDirect
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hstatus :
      (CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish) ∨
      CompactBinaryNatCompletedStatusSameRowsWithSize tokenTable width
        tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.outputCount <= numericBound)
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (((compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
            tokenCount current.tasksFinish current.finish ⋏
          compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
            tokenCount next.tasksFinish next.finish) ⋎
          compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
            tokenTable width tokenCount current.tasksFinish current.finish
            next.tasksFinish next.finish witness.sourceOutputStart
            witness.sourceOutputBoundary witness.sourceOutputBoundarySize
            witness.targetOutputStart witness.targetOutputBoundary
            witness.targetOutputBoundarySize
            witness.outputCount).freeVariables)
        doneStatusZeroValuation)
      ((compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
          tokenCount current.tasksFinish current.finish ⋏
        compactBinaryNatFailedStatusSliceClosedFormula tokenTable width
          tokenCount next.tasksFinish next.finish) ⋎
        compactBinaryNatCompletedStatusSameRowsWithSizeExplicitFormula
          tokenTable width tokenCount current.tasksFinish current.finish
          next.tasksFinish next.finish witness.sourceOutputStart
          witness.sourceOutputBoundary witness.sourceOutputBoundarySize
          witness.targetOutputStart witness.targetOutputBoundary
          witness.targetOutputBoundarySize witness.outputCount) := by
  by_cases hfailed :
      CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          current.tasksFinish current.finish ∧
        CompactBinaryNatFailedStatusSlice tokenTable width tokenCount
          next.tasksFinish next.finish
  · let currentCertificate :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish
        hfailed.1
    let nextCertificate :=
      compactBinaryNatFailedStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount next.tasksFinish next.finish hfailed.2
    let pair := compileDirectConjunction currentCertificate.compile
      nextCertificate.compile
    exact compileDirectDisjunctionLeft pair
  · have hcompleted : CompactBinaryNatCompletedStatusSameRowsWithSize
        tokenTable width tokenCount current.tasksFinish current.finish
        next.tasksFinish next.finish witness.sourceOutputStart
        witness.sourceOutputBoundary witness.sourceOutputBoundarySize
        witness.targetOutputStart witness.targetOutputBoundary
        witness.targetOutputBoundarySize witness.outputCount := by
      rcases hstatus with hfailed' | hcompleted
      · exact False.elim (hfailed hfailed')
      · exact hcompleted
    let completed :=
      compileCompactBinaryNatCompletedStatusSameRowsUniformDirect tokenTable
        width tokenCount current.tasksFinish current.finish next.tasksFinish
        next.finish witness.sourceOutputStart witness.sourceOutputBoundary
        witness.sourceOutputBoundarySize witness.targetOutputStart
        witness.targetOutputBoundary witness.targetOutputBoundarySize
        witness.outputCount numericBound bitBound hcompleted htokenCount
        houtputCount hsourceBoundarySize htargetBoundarySize hnumericSize
    exact compileDirectDisjunctionRight completed

end FoundationCompactNumericListedDirectParserDoneStatusUniformDirectCompiler
