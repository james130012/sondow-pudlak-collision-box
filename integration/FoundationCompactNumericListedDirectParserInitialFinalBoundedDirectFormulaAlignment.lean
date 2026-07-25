import integration.FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSubstitution

/-! # Closed public-source formula alignment for twenty-three endpoint witnesses -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFormulaAlignment

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectBoundedEndpointExplicitHybridSupport
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceSyntax
open FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectSourceTerminalSubstitution

theorem compactParserInitialFinalBoundedDirectClosedFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount fuel
      inputBoundary inputCount expectedBoundary expectedCount
      taskKind taskBinderArity taskRepeatCount valueBound : Nat) :
    compactParserInitialFinalBoundedDirectClosedFormula tokenTable width
        tokenCount stateBoundary stateCount fuel inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount valueBound =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 23
        (compactParserInitialFinalBoundedDirectRawTerminal tokenTable width
          tokenCount stateBoundary stateCount fuel inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount) := by
  unfold compactParserInitialFinalBoundedDirectClosedFormula
    compactParserInitialFinalBoundedDirectSourceRawBody
  rw [sourceSubstitution_sourceBoundedWitnessFormula]
  rw [compactParserInitialFinalBoundedDirectSourceRawTerminal_rewriting]
  have hbound :
      Rew.subst
          (compactParserInitialFinalBoundedDirectSourceTerms tokenTable width
            tokenCount stateBoundary stateCount fuel inputBoundary inputCount
            expectedBoundary expectedCount taskKind taskBinderArity
            taskRepeatCount valueBound)
          (#13 : ArithmeticSemiterm Nat 14) =
        shortBinaryNumeralTerm valueBound := by
    simp [Rew.subst_bvar,
      compactParserInitialFinalBoundedDirectSourceTerms,
      Matrix.vecAppend_eq_ite]
  rw [hbound]
  rfl

#print axioms compactParserInitialFinalBoundedDirectClosedFormula_alignment

end FoundationCompactNumericListedDirectParserInitialFinalBoundedDirectFormulaAlignment
