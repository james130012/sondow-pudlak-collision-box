import integration.FoundationCompactNumericListedDirectVerifierTaskListRowsBranchFormula

/-!
# Witness-substitution alignment for verifier task-list rows

This cached syntax proof substitutes all fourteen concrete row witnesses and
checks that the remaining formula is exactly the two table endpoints conjoined
with the verifier-task core.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskLayout
open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierTaskCoreExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierParseTaskHeadExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler

private theorem taskListRowsSubstituteClosedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) =
          Rew.id := by
        apply Rew.ext
        · intro index
          exact Fin.elim0 index
        · intro freeIndex
          rfl
      rw [hrew]
      exact Rew.id_app term
  | succ k inductionHypothesis =>
      have hrew :
          (Rew.subst values).comp Rew.bShift =
            Rew.subst (fun index : Fin k => values index.succ) := by
        apply Rew.ext
        · intro index
          simp [Rew.comp_app]
        · intro freeIndex
          simp [Rew.comp_app]
      calc
        Rew.subst values (closedShift (k + 1) term) =
            ((Rew.subst values).comp Rew.bShift)
              (closedShift k term) := by
                simp [closedShift, Rew.comp_app]
        _ = Rew.subst (fun index : Fin k => values index.succ)
              (closedShift k term) := by rw [hrew]
        _ = term := inductionHypothesis _

/-- Substitution of all fourteen witnesses leaves the open row endpoints. -/
theorem compactNumericVerifierTaskListRowsBranchTerminal_substitution_alignment
    (tokenTable width tokenCount taskBoundary
      start finish tag gammaFinish gammaCount gammaBoundary
      firstFinish firstCount secondFinish secondCount
      witnessFinish witnessCount suffixCount gammaBoundarySize : Nat) :
    (compactNumericVerifierTaskListRowsBranchTerminal
        tokenTable width tokenCount taskBoundary (&0 : ValuationTerm)) ⇜
      ![shortBinaryNumeralTerm gammaBoundarySize,
        shortBinaryNumeralTerm suffixCount,
        shortBinaryNumeralTerm witnessCount,
        shortBinaryNumeralTerm witnessFinish,
        shortBinaryNumeralTerm secondCount,
        shortBinaryNumeralTerm secondFinish,
        shortBinaryNumeralTerm firstCount,
        shortBinaryNumeralTerm firstFinish,
        shortBinaryNumeralTerm gammaBoundary,
        shortBinaryNumeralTerm gammaCount,
        shortBinaryNumeralTerm gammaFinish,
        shortBinaryNumeralTerm tag,
        shortBinaryNumeralTerm finish,
        shortBinaryNumeralTerm start] =
      compactNumericVerifierTaskListRowsTerminalPartsFormula
        tokenTable width tokenCount taskBoundary
        start finish tag gammaFinish gammaCount gammaBoundary
        firstFinish firstCount secondFinish secondCount
        witnessFinish witnessCount suffixCount gammaBoundarySize := by
  let witnessTerms : Fin 14 -> ValuationTerm :=
    ![shortBinaryNumeralTerm gammaBoundarySize,
      shortBinaryNumeralTerm suffixCount,
      shortBinaryNumeralTerm witnessCount,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm secondCount,
      shortBinaryNumeralTerm secondFinish,
      shortBinaryNumeralTerm firstCount,
      shortBinaryNumeralTerm firstFinish,
      shortBinaryNumeralTerm gammaBoundary,
      shortBinaryNumeralTerm gammaCount,
      shortBinaryNumeralTerm gammaFinish,
      shortBinaryNumeralTerm tag,
      shortBinaryNumeralTerm finish,
      shortBinaryNumeralTerm start]
  have hstartTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          closedShift 14 (&0 : ValuationTerm),
          (#13 : ArithmeticSemiterm Nat 14)]) =
        ![shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm tokenCount,
          (&0 : ValuationTerm),
          shortBinaryNumeralTerm start] := by
    funext coordinate
    fin_cases coordinate
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm taskBoundary)
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (&0 : ValuationTerm)
    · simp [witnessTerms, Rew.subst_bvar]
  have hfinishTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          closedShift 14 (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm),
          (#12 : ArithmeticSemiterm Nat 14)]) =
        ![shortBinaryNumeralTerm taskBoundary,
          shortBinaryNumeralTerm tokenCount,
          (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm),
          shortBinaryNumeralTerm finish] := by
    funext coordinate
    fin_cases coordinate
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm taskBoundary)
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm)
    · simp [witnessTerms, Rew.subst_bvar]
  have hcoreTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
          closedShift 14 (shortBinaryNumeralTerm width),
          closedShift 14 (shortBinaryNumeralTerm tokenCount),
          (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8,
          #7, #6, #5, #4, #3, #2, #1, #0]) =
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm start,
          shortBinaryNumeralTerm finish,
          shortBinaryNumeralTerm tag,
          shortBinaryNumeralTerm gammaFinish,
          shortBinaryNumeralTerm gammaCount,
          shortBinaryNumeralTerm gammaBoundary,
          shortBinaryNumeralTerm firstFinish,
          shortBinaryNumeralTerm firstCount,
          shortBinaryNumeralTerm secondFinish,
          shortBinaryNumeralTerm secondCount,
          shortBinaryNumeralTerm witnessFinish,
          shortBinaryNumeralTerm witnessCount,
          shortBinaryNumeralTerm suffixCount,
          shortBinaryNumeralTerm gammaBoundarySize] := by
    funext coordinate
    fin_cases coordinate
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenTable)
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm width)
    · simpa using taskListRowsSubstituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    all_goals simp [witnessTerms, Rew.subst_bvar]
  unfold compactNumericVerifierTaskListRowsBranchTerminal
  unfold compactNumericVerifierTaskListRowsTerminalPartsFormula
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactNumericVerifierTaskCoreClosedFormula
  unfold compactNumericVerifierTaskRowCoordinatesOf
  simp only [LogicalConnective.HomClass.map_and,
    rewriting_embeddedFormulaSubstitution]
  change
    ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        (Rew.subst witnessTerms ∘
          ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
            closedShift 14 (shortBinaryNumeralTerm tokenCount),
            closedShift 14 (&0 : ValuationTerm),
            (#13 : ArithmeticSemiterm Nat 14)])) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          (Rew.subst witnessTerms ∘
            ![closedShift 14 (shortBinaryNumeralTerm taskBoundary),
              closedShift 14 (shortBinaryNumeralTerm tokenCount),
              closedShift 14
                (‘!!(&0 : ValuationTerm) + 1’ : ValuationTerm),
              (#12 : ArithmeticSemiterm Nat 14)])) ⋏
        ((Rewriting.emb (ξ := Nat)
            compactNumericVerifierTaskCoreGraphDef.val) ⇜
          (Rew.subst witnessTerms ∘
            ![closedShift 14 (shortBinaryNumeralTerm tokenTable),
              closedShift 14 (shortBinaryNumeralTerm width),
              closedShift 14 (shortBinaryNumeralTerm tokenCount),
              (#13 : ArithmeticSemiterm Nat 14), #12, #11, #10, #9, #8,
              #7, #6, #5, #4, #3, #2, #1, #0]))) = _
  rw [hstartTerms, hfinishTerms, hcoreTerms]

end FoundationCompactNumericListedDirectVerifierTaskListRowsExplicitHybridCertificate
