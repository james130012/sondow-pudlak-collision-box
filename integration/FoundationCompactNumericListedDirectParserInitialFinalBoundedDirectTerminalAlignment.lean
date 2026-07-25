import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectClosedTermsAlignment
import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectRawTermsSubstitution

/-! # Terminal substitution alignment for the bounded parser endpoints -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectTerminalAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectParserInitialFinalFormula
open FoundationCompactNumericListedDirectParserInitialFinalExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectClosedTermsAlignment
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectRawTermsSubstitution

theorem compactParserInitialFinalBoundedDirectRawTerminal_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount : Nat)
    (witness : CompactParserInitialFinalWitnessCoordinates) :
    compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount ⇜
      (fun index => shortBinaryNumeralTerm
        (compactParserInitialFinalBoundedDirectWitnessValues witness index)) =
    compactUnifiedParserInitialFinalRowsClosedFormula tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      witness := by
  change Rew.subst (fun index => shortBinaryNumeralTerm
      (compactParserInitialFinalBoundedDirectWitnessValues witness index)) ▹
    compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount = _
  unfold compactParserInitialFinalBoundedDirectRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  rw [compactParserInitialFinalBoundedDirectRawTerms_substitution]
  exact
    (compactUnifiedParserInitialFinalRowsClosedFormula_eq_directClosedTerms
      tokenTable width tokenCount stateBoundary stateCount fuel inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount witness).symm

#print axioms compactParserInitialFinalBoundedDirectRawTerminal_alignment

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectTerminalAlignment
