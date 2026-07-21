import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsBranchFormula

/-!
# Binder-freeing alignment for verifier task-list rows

This cached syntax proof releases the bounded row index and then the fourteen
bounded row witnesses without changing the represented verifier formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierTaskListRowsFormula
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting

private theorem compactNumericVerifierTaskListRowsTerminal_free_alignment
    (tokenTable width tokenCount taskBoundary : Nat) :
    Rewriting.free
        (compactNumericVerifierTaskListRowsTerminal
          tokenTable width tokenCount taskBoundary) =
      compactNumericVerifierTaskListRowsBranchTerminal
        tokenTable width tokenCount taskBoundary (&0 : ValuationTerm) := by
  have hfreeTaskBoundary :=
    free_closedShift_shortBinaryNumeralTerm 14 taskBoundary
  have hfreeTokenCount :=
    free_closedShift_shortBinaryNumeralTerm 14 tokenCount
  have hfreeTokenTable :=
    free_closedShift_shortBinaryNumeralTerm 14 tokenTable
  have hfreeWidth :=
    free_closedShift_shortBinaryNumeralTerm 14 width
  have hstartTerms :
      ((Rew.free (L := ℒₒᵣ) (n := 14)) ∘
        ![closedShift 15 (shortBinaryNumeralTerm taskBoundary),
          closedShift 15 (shortBinaryNumeralTerm tokenCount),
          (#14 : ArithmeticSemiterm Nat 15), #13]) =
        ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          closedShift 14 (&0 : ValuationTerm),
          (#13 : ArithmeticSemiterm Nat 14)] := by
    funext coordinate
    fin_cases coordinate
    · exact hfreeTaskBoundary
    · exact hfreeTokenCount
    · simp [closedShift, Rew.comp_app, Rew.subst_bvar]
    · simp [Rew.comp_app, Rew.subst_bvar]
  have hfinishTerms :
      ((Rew.free (L := ℒₒᵣ) (n := 14)) ∘
        ![closedShift 15 (shortBinaryNumeralTerm taskBoundary),
          closedShift 15 (shortBinaryNumeralTerm tokenCount),
          (‘#14 + 1’ : ArithmeticSemiterm Nat 15), #12]) =
        ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          closedShift 14 (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm),
          (#12 : ArithmeticSemiterm Nat 14)] := by
    funext coordinate
    fin_cases coordinate
    · exact hfreeTaskBoundary
    · exact hfreeTokenCount
    · simp [closedShift, Rew.comp_app, Rew.subst_bvar]
    · simp [Rew.comp_app, Rew.subst_bvar]
  have hcoreTerms :
      ((Rew.free (L := ℒₒᵣ) (n := 14)) ∘
        ![closedShift 15 (shortBinaryNumeralTerm tokenTable),
          closedShift 15 (shortBinaryNumeralTerm width),
          closedShift 15 (shortBinaryNumeralTerm tokenCount),
          (#13 : ArithmeticSemiterm Nat 15), #12, #11, #10, #9, #8,
          #7, #6, #5, #4, #3, #2, #1, #0]) =
        ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
          closedShift 14 (shortBinaryNumeralTerm width),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8,
          #7, #6, #5, #4, #3, #2, #1, #0] := by
    funext coordinate
    fin_cases coordinate
    · exact hfreeTokenTable
    · exact hfreeWidth
    · exact hfreeTokenCount
    all_goals simp [Rew.comp_app, Rew.subst_bvar]
  unfold compactNumericVerifierTaskListRowsTerminal
  unfold compactNumericVerifierTaskListRowsBranchTerminal
  simp only [LogicalConnective.HomClass.map_and,
    rewriting_embeddedFormulaSubstitution]
  rw [hstartTerms, hfinishTerms, hcoreTerms]

/-- Releasing the universal index exposes exactly fourteen bounded witnesses. -/
theorem compactNumericVerifierTaskListRowsUniversalBody_free_alignment
    (tokenTable width tokenCount taskBoundary valueBound : Nat) :
    Rewriting.free
        (compactNumericVerifierTaskListRowsUniversalBody
          tokenTable width tokenCount taskBoundary valueBound) =
      explicitBoundedWitnessFormula
        (shortBinaryNumeralTerm valueBound) 14
        (compactNumericVerifierTaskListRowsBranchTerminal
          tokenTable width tokenCount taskBoundary (&0 : ValuationTerm)) := by
  unfold compactNumericVerifierTaskListRowsUniversalBody
  simp only [rewriting_bexsLTSucc, Rew.q_free]
  rw [free_closedShift_shortBinaryNumeralTerm 0 valueBound,
    free_closedShift_shortBinaryNumeralTerm 1 valueBound,
    free_closedShift_shortBinaryNumeralTerm 2 valueBound,
    free_closedShift_shortBinaryNumeralTerm 3 valueBound,
    free_closedShift_shortBinaryNumeralTerm 4 valueBound,
    free_closedShift_shortBinaryNumeralTerm 5 valueBound,
    free_closedShift_shortBinaryNumeralTerm 6 valueBound,
    free_closedShift_shortBinaryNumeralTerm 7 valueBound,
    free_closedShift_shortBinaryNumeralTerm 8 valueBound,
    free_closedShift_shortBinaryNumeralTerm 9 valueBound,
    free_closedShift_shortBinaryNumeralTerm 10 valueBound,
    free_closedShift_shortBinaryNumeralTerm 11 valueBound,
    free_closedShift_shortBinaryNumeralTerm 12 valueBound,
    free_closedShift_shortBinaryNumeralTerm 13 valueBound,
    compactNumericVerifierTaskListRowsTerminal_free_alignment]
  simp only [explicitBoundedWitnessFormula]
  rfl

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
