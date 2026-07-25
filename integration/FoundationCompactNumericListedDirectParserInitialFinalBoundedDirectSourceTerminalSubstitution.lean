import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTermsSubstitution

/-! # Public substitution of the endpoint terminal formula -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSubstitution

open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserSyntaxAdjacentRowBoundedAtValuationIndexSyntaxBase
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTermsSubstitution

theorem compactParserInitialFinalBoundedDirectSourceRawTerminal_rewriting
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    sourceSubstitutionQpow
        (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount valueBound) 23 ▹
      compactParserInitialFinalBoundedDirectSourceRawTerminal =
    compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
      tokenCount stateBoundary stateCount fuel inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount := by
  unfold compactParserInitialFinalBoundedDirectSourceRawTerminal
    compactParserInitialFinalBoundedDirectRawTerminal
  rw [rewriting_embeddedFormulaSubstitution]
  rw [compactParserInitialFinalBoundedDirectSourceRawTerms_rewriting]

#print axioms
  compactParserInitialFinalBoundedDirectSourceRawTerminal_rewriting

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSubstitution
