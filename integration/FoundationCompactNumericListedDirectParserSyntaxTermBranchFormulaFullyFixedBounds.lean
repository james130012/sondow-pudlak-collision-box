import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds

/-! # Closed syntax and fixed code bounds for the complete Term branch formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000

namespace FoundationCompactNumericListedDirectParserSyntaxTermBranchFormulaFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueTwoFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds

theorem
    compactUnifiedParserSyntaxTermDecisionExplicitFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
      tokenCount current next binderArity witness).freeVariables = ∅ := by
  have hcontinue :
      (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2).freeVariables = ∅ :=
    compactUnifiedParserSyntaxTermContinueTwoClosedFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  have hzeroSuccess :
      (syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount current
        next binderArity witness).freeVariables = ∅ := by
    unfold syntaxTermZeroSuccessDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortLtFormula_freeVariables_eq_empty, hcontinue]
    simp
  have hzeroFailure :
      (syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount current
        next binderArity witness).freeVariables = ∅ := by
    unfold syntaxTermZeroFailureDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortLeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hone :
      (syntaxTermOneDecisionFormula tokenTable width tokenCount current next
        witness).freeVariables = ∅ := by
    unfold syntaxTermOneDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeEqFormula_freeVariables_eq_empty, hcontinue]
    simp
  have htwo :
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness).freeVariables = ∅ :=
    syntaxTermTwoDecisionFormula_freeVariables_eq_empty_fullyFixed tokenTable
      width tokenCount current next binderArity witness
  have hinvalid :
      (syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
        next witness).freeVariables = ∅ := by
    unfold syntaxTermInvalidTagDecisionFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeNeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  rw [syntaxTermDecisionExplicitFormula_component_alignment]
  unfold syntaxTermZeroPairDecisionFormula syntaxTermDecisionRightTailFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_or,
    LO.FirstOrder.Semiformula.freeVariables_or, hzeroSuccess, hzeroFailure,
    LO.FirstOrder.Semiformula.freeVariables_or, hone,
    LO.FirstOrder.Semiformula.freeVariables_or, htwo, hinvalid]
  simp

theorem
    compactUnifiedParserSyntaxTermBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness).freeVariables = ∅ := by
  unfold compactUnifiedParserSyntaxTermBranchExplicitFormula
  rw [LO.FirstOrder.Semiformula.freeVariables_or,
    LO.FirstOrder.Semiformula.freeVariables_and,
    syntaxTermShortNativeLeFormula_freeVariables_eq_empty,
    syntaxTermFailureClosedFormula_freeVariables_eq_empty,
    LO.FirstOrder.Semiformula.freeVariables_and,
    syntaxTermNativeShortLeFormula_freeVariables_eq_empty,
    LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
    LO.FirstOrder.Semiformula.freeVariables_and,
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
    compactUnifiedParserSyntaxTermDecisionExplicitFormula_freeVariables_eq_empty_fullyFixed]
  simp

theorem
    compactUnifiedParserSyntaxTermBranchExplicitFormula_code_length_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (bitBound : Nat)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    (binaryFormulaCode
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness)).length <=
      syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound := by
  have hsub :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
          tokenCount current next binderArity witness)).length <=
        (binaryFormulaCode
          (compactUnifiedParserSyntaxTermExplicitFormula tokenTable width
            tokenCount current next binderArity witness)).length := by
    unfold compactUnifiedParserSyntaxTermExplicitFormula
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hfull :=
    compactUnifiedParserSyntaxTermExplicitFormula_code_length_le_fixed
      tokenTable width tokenCount current next binderArity witness bitBound
      hsize
  exact hsub.trans (hfull.trans (by
    unfold syntaxTermFunctionDecisionFixedSyntaxPolynomial
    omega))

#print axioms
  compactUnifiedParserSyntaxTermDecisionExplicitFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactUnifiedParserSyntaxTermBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  compactUnifiedParserSyntaxTermBranchExplicitFormula_code_length_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermBranchFormulaFullyFixedBounds
