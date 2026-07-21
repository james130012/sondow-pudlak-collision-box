import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRows
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for bounded verifier-task row equality

The four slice endpoints are installed as bounded existential witnesses.  The
remaining fixed-width entries and slice equality are certified directly from
the semantic witnesses.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

namespace FoundationCompactNumericListedDirectVerifierTaskBoundedRowsEqExplicitHybridCertificate

open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectVerifierTaskListDropRows
open FoundationCompactNumericListedDirectTokenSliceEquality
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListListRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAEmbeddedPredicateFreeVariables

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private def closedShift :
    (k : Nat) -> ValuationTerm -> ArithmeticSemiterm Nat k
  | 0, term => term
  | k + 1, term => Rew.bShift (closedShift k term)

private theorem arithmeticAddTerm_eq_func
    {Variable : Type*} {boundArity : Nat}
    (left right : ArithmeticSemiterm Variable boundArity) :
    (‘!!left + !!right’ : ArithmeticSemiterm Variable boundArity) =
      Semiterm.func Language.Add.add ![left, right] := by
  simp [Semiterm.Operator.operator,
    Semiterm.Operator.Add.term_eq, Rew.func, Matrix.fun_eq_vec_two]

private theorem termValue_arithmeticAdd
    (valuation : Nat -> Nat) (left right : ValuationTerm) :
    termValue valuation ‘!!left + !!right’ =
      termValue valuation left + termValue valuation right := by
  rw [arithmeticAddTerm_eq_func]
  exact termValue_add valuation ![left, right]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

/-- The eight input coordinates of the row-equality predicate are closed by
short binary numerals. -/
def compactNumericVerifierTaskBoundedRowsEqClosedFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskBoundedRowsEqDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm valueBound,
      shortBinaryNumeralTerm sourceIndex,
      shortBinaryNumeralTerm targetIndex]

/-- The five checked conjuncts below the four endpoint witnesses. -/
def compactNumericVerifierTaskBoundedRowsEqTerminal
    (tokenTable width tokenCount sourceBoundary targetBoundary
      : Nat) (sourceIndex targetIndex : ValuationTerm) :
    ArithmeticSemiformula Nat 4 :=
  ((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
      ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
        closedShift 4 (shortBinaryNumeralTerm tokenCount),
        closedShift 4 sourceIndex,
        (#3 : ArithmeticSemiterm Nat 4)]) ⋏
    (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4
            (‘!!sourceIndex + 1’ : ValuationTerm),
          (#2 : ArithmeticSemiterm Nat 4)]) ⋏
      (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
          ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
            closedShift 4 (shortBinaryNumeralTerm tokenCount),
            closedShift 4 targetIndex,
            (#1 : ArithmeticSemiterm Nat 4)]) ⋏
        (((Rewriting.emb (ξ := Nat) compactFixedWidthEntryDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              closedShift 4
                (‘!!targetIndex + 1’ : ValuationTerm),
              (#0 : ArithmeticSemiterm Nat 4)]) ⋏
          ((Rewriting.emb (ξ := Nat) compactFixedWidthTokenSlicesEqDef.val) ⇜
            ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
              closedShift 4 (shortBinaryNumeralTerm width),
              closedShift 4 (shortBinaryNumeralTerm tokenCount),
              (#3 : ArithmeticSemiterm Nat 4), #2, #1, #0]))))

private def compactNumericVerifierTaskBoundedRowsEqTerminalPartsFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      sourceStart sourceFinish targetStart targetFinish : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    ValuationFormula :=
  compactFixedWidthEntryAtValuationFormula
      (shortBinaryNumeralTerm sourceBoundary)
      (shortBinaryNumeralTerm tokenCount)
      sourceIndex
      (shortBinaryNumeralTerm sourceStart) ⋏
    (compactFixedWidthEntryAtValuationFormula
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (‘!!sourceIndex + 1’ : ValuationTerm)
        (shortBinaryNumeralTerm sourceFinish) ⋏
      (compactFixedWidthEntryAtValuationFormula
          (shortBinaryNumeralTerm targetBoundary)
          (shortBinaryNumeralTerm tokenCount)
          targetIndex
          (shortBinaryNumeralTerm targetStart) ⋏
        (compactFixedWidthEntryAtValuationFormula
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (‘!!targetIndex + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm targetFinish) ⋏
          (compactFixedWidthTokenSlicesEqClosedFormula
            tokenTable width tokenCount
              sourceStart sourceFinish targetStart targetFinish))))

private theorem rewriting_embeddedFormulaSubstitution
    {sourceVariables targetVariables : Type*}
    {predicateArity sourceArity targetArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity
      targetVariables targetArity)
    (formula : ArithmeticSemiformula Empty predicateArity)
    (terms : Fin predicateArity ->
      ArithmeticSemiterm sourceVariables sourceArity) :
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
      (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
  have hcomposition :
      (rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity) =
        (Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity) := by
    ext coordinate
    · simp [Rew.comp_app]
    · exact Empty.elim coordinate
  calc
    rewriting ▹ ((Rewriting.emb (ξ := sourceVariables) formula) ⇜ terms) =
        ((rewriting.comp (Rew.subst terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            sourceVariables predicateArity)) ▹ formula := by
      rw [TransitiveRewriting.comp_app, TransitiveRewriting.comp_app]
    _ = ((Rew.subst (rewriting ∘ terms)).comp
          (Rew.emb : Rew ℒₒᵣ Empty predicateArity
            targetVariables predicateArity)) ▹ formula := by
      rw [hcomposition]
    _ = (Rewriting.emb (ξ := targetVariables) formula) ⇜
        (rewriting ∘ terms) := by
      rw [TransitiveRewriting.comp_app]

private theorem substituteClosedShift
    {k : Nat} (values : Fin k -> ValuationTerm)
    (term : ValuationTerm) :
    Rew.subst values (closedShift k term) = term := by
  induction k with
  | zero =>
      have hrew : (Rew.subst values : Rew ℒₒᵣ Nat 0 Nat 0) = Rew.id := by
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

private theorem compactNumericVerifierTaskBoundedRowsEqTerminal_substitution_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      sourceStart sourceFinish targetStart targetFinish : Nat)
    (sourceIndex targetIndex : ValuationTerm) :
    (compactNumericVerifierTaskBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndex targetIndex) ⇜
      ![shortBinaryNumeralTerm targetFinish,
        shortBinaryNumeralTerm targetStart,
        shortBinaryNumeralTerm sourceFinish,
        shortBinaryNumeralTerm sourceStart] =
      compactNumericVerifierTaskBoundedRowsEqTerminalPartsFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          sourceStart sourceFinish targetStart targetFinish
          sourceIndex targetIndex := by
  let witnessTerms : Fin 4 -> ValuationTerm :=
    ![shortBinaryNumeralTerm targetFinish,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm sourceFinish,
      shortBinaryNumeralTerm sourceStart]
  have hsourceStartTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 sourceIndex,
          (#3 : ArithmeticSemiterm Nat 4)]) =
        ![shortBinaryNumeralTerm sourceBoundary,
          shortBinaryNumeralTerm tokenCount,
          sourceIndex,
          shortBinaryNumeralTerm sourceStart] := by
    funext coordinate
    fin_cases coordinate
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm sourceBoundary)
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    · exact substituteClosedShift witnessTerms sourceIndex
    · simp [witnessTerms, Rew.subst_bvar]
  have hsourceFinishTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 4 (shortBinaryNumeralTerm sourceBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4
            (‘!!sourceIndex + 1’ : ValuationTerm),
          (#2 : ArithmeticSemiterm Nat 4)]) =
        ![shortBinaryNumeralTerm sourceBoundary,
          shortBinaryNumeralTerm tokenCount,
          (‘!!sourceIndex + 1’ : ValuationTerm),
          shortBinaryNumeralTerm sourceFinish] := by
    funext coordinate
    fin_cases coordinate
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm sourceBoundary)
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    · simpa using substituteClosedShift witnessTerms
        (‘!!sourceIndex + 1’ : ValuationTerm)
    · simp [witnessTerms, Rew.subst_bvar]
  have htargetStartTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4 targetIndex,
          (#1 : ArithmeticSemiterm Nat 4)]) =
        ![shortBinaryNumeralTerm targetBoundary,
          shortBinaryNumeralTerm tokenCount,
          targetIndex,
          shortBinaryNumeralTerm targetStart] := by
    funext coordinate
    fin_cases coordinate
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm targetBoundary)
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    · exact substituteClosedShift witnessTerms targetIndex
    · simp [witnessTerms, Rew.subst_bvar]
  have htargetFinishTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 4 (shortBinaryNumeralTerm targetBoundary),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          closedShift 4
            (‘!!targetIndex + 1’ : ValuationTerm),
          (#0 : ArithmeticSemiterm Nat 4)]) =
        ![shortBinaryNumeralTerm targetBoundary,
          shortBinaryNumeralTerm tokenCount,
          (‘!!targetIndex + 1’ : ValuationTerm),
          shortBinaryNumeralTerm targetFinish] := by
    funext coordinate
    fin_cases coordinate
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm targetBoundary)
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    · simpa using substituteClosedShift witnessTerms
        (‘!!targetIndex + 1’ : ValuationTerm)
    · simp [witnessTerms, Rew.subst_bvar]
  have hslicesTerms :
      (Rew.subst witnessTerms ∘
        ![closedShift 4 (shortBinaryNumeralTerm tokenTable),
          closedShift 4 (shortBinaryNumeralTerm width),
          closedShift 4 (shortBinaryNumeralTerm tokenCount),
          (#3 : ArithmeticSemiterm Nat 4), #2, #1, #0]) =
        ![shortBinaryNumeralTerm tokenTable,
          shortBinaryNumeralTerm width,
          shortBinaryNumeralTerm tokenCount,
          shortBinaryNumeralTerm sourceStart,
          shortBinaryNumeralTerm sourceFinish,
          shortBinaryNumeralTerm targetStart,
          shortBinaryNumeralTerm targetFinish] := by
    funext coordinate
    fin_cases coordinate
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenTable)
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm width)
    · simpa using substituteClosedShift witnessTerms
        (shortBinaryNumeralTerm tokenCount)
    all_goals simp [witnessTerms, Rew.subst_bvar]
  unfold compactNumericVerifierTaskBoundedRowsEqTerminal
  unfold compactNumericVerifierTaskBoundedRowsEqTerminalPartsFormula
  unfold compactFixedWidthEntryAtValuationFormula
  unfold compactFixedWidthTokenSlicesEqClosedFormula
  simp only [LogicalConnective.HomClass.map_and,
    rewriting_embeddedFormulaSubstitution]
  rw [hsourceStartTerms, hsourceFinishTerms,
    htargetStartTerms, htargetFinishTerms, hslicesTerms]

def compactNumericVerifierTaskBoundedRowsEqExplicitFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    ValuationFormula :=
  ((((compactNumericVerifierTaskBoundedRowsEqTerminal
        tokenTable width tokenCount sourceBoundary targetBoundary
          sourceIndex targetIndex).bexsLTSucc
      (closedShift 3 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
    (closedShift 2 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
  (closedShift 1 (shortBinaryNumeralTerm valueBound))).bexsLTSucc
    (closedShift 0 (shortBinaryNumeralTerm valueBound))

theorem compactNumericVerifierTaskBoundedRowsEqExplicitFormula_eq_generic
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndex targetIndex : ValuationTerm) :
    compactNumericVerifierTaskBoundedRowsEqExplicitFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex =
      explicitBoundedWitnessFormula (shortBinaryNumeralTerm valueBound) 4
        (compactNumericVerifierTaskBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            sourceIndex targetIndex) := by
  rfl

/-- Exact four-witness presentation of the quoted row-equality predicate. -/
theorem compactNumericVerifierTaskBoundedRowsEqClosedFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat) :
    compactNumericVerifierTaskBoundedRowsEqClosedFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex =
      compactNumericVerifierTaskBoundedRowsEqExplicitFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex) := by
  unfold compactNumericVerifierTaskBoundedRowsEqClosedFormula
  unfold compactNumericVerifierTaskBoundedRowsEqExplicitFormula
  unfold compactNumericVerifierTaskBoundedRowsEqDef
  simp [compactNumericVerifierTaskBoundedRowsEqTerminal,
    Semiformula.bexsLTSucc, Semiformula.bexsLT, closedShift,
    Rew.q, Rew.subst_bvar,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  · apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    · apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      · apply Rewriting.smul_ext'
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [Rew.comp_app, Rew.subst_bvar]
        · intro coordinate
          exact Empty.elim coordinate
      · congr 1
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate
/-- Build the row-equality certificate from all semantic endpoint witnesses. -/
noncomputable def compactNumericVerifierTaskBoundedRowsEqExplicitHybridCertificate
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (hrows : CompactNumericVerifierTaskBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    HybridCertificate
      (compactNumericVerifierTaskBoundedRowsEqClosedFormula
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound sourceIndex targetIndex) := by
  let sourceStart := Classical.choose hrows
  have hsourceStartData := Classical.choose_spec hrows
  let sourceFinish := Classical.choose hsourceStartData.2
  have hsourceFinishData := Classical.choose_spec hsourceStartData.2
  let targetStart := Classical.choose hsourceFinishData.2
  have htargetStartData := Classical.choose_spec hsourceFinishData.2
  let targetFinish := Classical.choose htargetStartData.2
  have htargetFinishData := Classical.choose_spec htargetStartData.2
  have hsourceStartBound := hsourceStartData.1
  have hsourceFinishBound := hsourceFinishData.1
  have htargetStartBound := htargetStartData.1
  have htargetFinishBound := htargetFinishData.1
  have hsourceStartEntry := htargetFinishData.2.1
  have hsourceFinishEntry := htargetFinishData.2.2.1
  have htargetStartEntry := htargetFinishData.2.2.2.1
  have htargetFinishEntry := htargetFinishData.2.2.2.2.1
  have hslices := htargetFinishData.2.2.2.2.2
  let count := Classical.choose hslices
  have hsliceData := Classical.choose_spec hslices
  have hcountBound := hsliceData.1
  have hsourceEndpoint := hsliceData.2.1
  have htargetEndpoint := hsliceData.2.2.1
  have hsourceFinishTokenBound := hsliceData.2.2.2.1
  have htargetFinishTokenBound := hsliceData.2.2.2.2.1
  have hbits := hsliceData.2.2.2.2.2
  let values : Fin 4 -> Nat :=
    ![targetFinish, targetStart, sourceFinish, sourceStart]
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        zeroValuation
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        (shortBinaryNumeralTerm sourceIndex)
        (shortBinaryNumeralTerm sourceStart) (by
          simpa [termValue_shortBinaryNumeralTerm] using hsourceStartEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          zeroValuation
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘!!(shortBinaryNumeralTerm sourceIndex) + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm sourceFinish) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne]
              using hsourceFinishEntry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            (shortBinaryNumeralTerm targetIndex)
            (shortBinaryNumeralTerm targetStart) (by
              simpa [termValue_shortBinaryNumeralTerm] using htargetStartEntry))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactFixedWidthEntryAtValuationExplicitHybridCertificate
              zeroValuation
              (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount)
              (‘!!(shortBinaryNumeralTerm targetIndex) + 1’ : ValuationTerm)
              (shortBinaryNumeralTerm targetFinish) (by
                simpa [termValue_shortBinaryNumeralTerm,
                  termValue_arithmeticAdd, termValue_arithmeticOne]
                  using htargetFinishEntry))
            (compactFixedWidthTokenSlicesEqExplicitHybridCertificate
              tokenTable width tokenCount sourceStart sourceFinish
                targetStart targetFinish count
                hcountBound hsourceEndpoint htargetEndpoint
                hsourceFinishTokenBound htargetFinishTokenBound hbits))))
  let terminal : HybridCertificate
      ((compactNumericVerifierTaskBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex)) ⇜
        ![shortBinaryNumeralTerm targetFinish,
          shortBinaryNumeralTerm targetStart,
          shortBinaryNumeralTerm sourceFinish,
          shortBinaryNumeralTerm sourceStart]) :=
    .cast
      (compactNumericVerifierTaskBoundedRowsEqTerminal_substitution_alignment
        tokenTable width tokenCount sourceBoundary targetBoundary
          sourceStart sourceFinish targetStart targetFinish
          (shortBinaryNumeralTerm sourceIndex)
          (shortBinaryNumeralTerm targetIndex)).symm terminalParts
  let terminalForBuilder : HybridCertificate
      ((compactNumericVerifierTaskBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex)) ⇜
        fun coordinate => shortBinaryNumeralTerm (values coordinate)) := by
    have hvalues :
        (fun coordinate => shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm targetFinish,
            shortBinaryNumeralTerm targetStart,
            shortBinaryNumeralTerm sourceFinish,
            shortBinaryNumeralTerm sourceStart] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [hvalues]
    exact terminal
  let installed := buildExplicitBoundedWitnessHybridCertificate
    valueBound
    (compactNumericVerifierTaskBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        (shortBinaryNumeralTerm sourceIndex)
        (shortBinaryNumeralTerm targetIndex))
    values (by
      intro coordinate
      fin_cases coordinate
      · exact htargetFinishBound
      · exact htargetStartBound
      · exact hsourceFinishBound
      · exact hsourceStartBound) terminalForBuilder
  exact .cast
    (compactNumericVerifierTaskBoundedRowsEqClosedFormula_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex).symm
    (.cast
      (compactNumericVerifierTaskBoundedRowsEqExplicitFormula_eq_generic
        tokenTable width tokenCount sourceBoundary targetBoundary
          valueBound (shortBinaryNumeralTerm sourceIndex)
            (shortBinaryNumeralTerm targetIndex)).symm installed)

/-- The row-equality predicate with its two row indices represented by
valuation terms.  This is the form needed inside an enclosing universal. -/
def compactNumericVerifierTaskBoundedRowsEqAtValuationFormula
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndexTerm targetIndexTerm : ValuationTerm) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierTaskBoundedRowsEqDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceBoundary,
      shortBinaryNumeralTerm targetBoundary,
      shortBinaryNumeralTerm valueBound,
      sourceIndexTerm,
      targetIndexTerm]

theorem compactNumericVerifierTaskBoundedRowsEqAtValuationFormula_alignment
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound : Nat) (sourceIndexTerm targetIndexTerm : ValuationTerm) :
    compactNumericVerifierTaskBoundedRowsEqAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndexTerm targetIndexTerm =
      compactNumericVerifierTaskBoundedRowsEqExplicitFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndexTerm targetIndexTerm := by
  unfold compactNumericVerifierTaskBoundedRowsEqAtValuationFormula
  unfold compactNumericVerifierTaskBoundedRowsEqExplicitFormula
  unfold compactNumericVerifierTaskBoundedRowsEqDef
  simp [compactNumericVerifierTaskBoundedRowsEqTerminal,
    Semiformula.bexsLTSucc, Semiformula.bexsLT, closedShift,
    Rew.q, Rew.subst_bvar,
    ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  congr 1
  · apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar]
    · intro coordinate
      exact Empty.elim coordinate
  · congr 1
    · apply Rewriting.smul_ext'
      apply Rew.ext
      · intro coordinate
        fin_cases coordinate <;>
          simp [Rew.comp_app, Rew.subst_bvar]
      · intro coordinate
        exact Empty.elim coordinate
    · congr 1
      · apply Rewriting.smul_ext'
        apply Rew.ext
        · intro coordinate
          fin_cases coordinate <;>
            simp [Rew.comp_app, Rew.subst_bvar]
        · intro coordinate
          exact Empty.elim coordinate
      · congr 1
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate
        · apply Rewriting.smul_ext'
          apply Rew.ext
          · intro coordinate
            fin_cases coordinate <;>
              simp [Rew.comp_app, Rew.subst_bvar]
          · intro coordinate
            exact Empty.elim coordinate

/-- Explicit row-equality certificate at an arbitrary valuation.  The two
index terms are checked against the semantic row indices; all four endpoint
witnesses and the complete token-slice certificate remain explicit. -/
noncomputable def
    compactNumericVerifierTaskBoundedRowsEqAtValuationExplicitHybridCertificate
    (valuation : Nat -> Nat)
    (tokenTable width tokenCount sourceBoundary targetBoundary
      valueBound sourceIndex targetIndex : Nat)
    (sourceIndexTerm targetIndexTerm : ValuationTerm)
    (hsourceIndex : termValue valuation sourceIndexTerm = sourceIndex)
    (htargetIndex : termValue valuation targetIndexTerm = targetIndex)
    (hrows : CompactNumericVerifierTaskBoundedRowsEq
      tokenTable width tokenCount sourceBoundary targetBoundary
        valueBound sourceIndex targetIndex) :
    CheckedHybridValuationBoundedFormulaCertificate valuation
      (compactNumericVerifierTaskBoundedRowsEqAtValuationFormula
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndexTerm targetIndexTerm) := by
  let sourceStart := Classical.choose hrows
  have hsourceStartData := Classical.choose_spec hrows
  let sourceFinish := Classical.choose hsourceStartData.2
  have hsourceFinishData := Classical.choose_spec hsourceStartData.2
  let targetStart := Classical.choose hsourceFinishData.2
  have htargetStartData := Classical.choose_spec hsourceFinishData.2
  let targetFinish := Classical.choose htargetStartData.2
  have htargetFinishData := Classical.choose_spec htargetStartData.2
  have hsourceStartBound := hsourceStartData.1
  have hsourceFinishBound := hsourceFinishData.1
  have htargetStartBound := htargetStartData.1
  have htargetFinishBound := htargetFinishData.1
  have hsourceStartEntry := htargetFinishData.2.1
  have hsourceFinishEntry := htargetFinishData.2.2.1
  have htargetStartEntry := htargetFinishData.2.2.2.1
  have htargetFinishEntry := htargetFinishData.2.2.2.2.1
  have hslices := htargetFinishData.2.2.2.2.2
  let count := Classical.choose hslices
  have hsliceData := Classical.choose_spec hslices
  have hcountBound := hsliceData.1
  have hsourceEndpoint := hsliceData.2.1
  have htargetEndpoint := hsliceData.2.2.1
  have hsourceFinishTokenBound := hsliceData.2.2.2.1
  have htargetFinishTokenBound := hsliceData.2.2.2.2.1
  have hbits := hsliceData.2.2.2.2.2
  let values : Fin 4 -> Nat :=
    ![targetFinish, targetStart, sourceFinish, sourceStart]
  let slicesAtZero :=
    compactFixedWidthTokenSlicesEqExplicitHybridCertificate
      tokenTable width tokenCount sourceStart sourceFinish
        targetStart targetFinish count
        hcountBound hsourceEndpoint htargetEndpoint
        hsourceFinishTokenBound htargetFinishTokenBound hbits
  let slicesAtValuation := revalueClosedHybridCertificate slicesAtZero (by
    unfold compactFixedWidthTokenSlicesEqClosedFormula
    apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
    intro coordinate
    fin_cases coordinate <;>
      exact shortBinaryNumeralTerm_freeVariables_eq_empty _) valuation
  let terminalParts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthEntryAtValuationExplicitHybridCertificate
        valuation
        (shortBinaryNumeralTerm sourceBoundary)
        (shortBinaryNumeralTerm tokenCount)
        sourceIndexTerm
        (shortBinaryNumeralTerm sourceStart) (by
          simpa [termValue_shortBinaryNumeralTerm, hsourceIndex]
            using hsourceStartEntry))
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactFixedWidthEntryAtValuationExplicitHybridCertificate
          valuation
          (shortBinaryNumeralTerm sourceBoundary)
          (shortBinaryNumeralTerm tokenCount)
          (‘!!sourceIndexTerm + 1’ : ValuationTerm)
          (shortBinaryNumeralTerm sourceFinish) (by
            simpa [termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne,
              hsourceIndex] using hsourceFinishEntry))
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthEntryAtValuationExplicitHybridCertificate
            valuation
            (shortBinaryNumeralTerm targetBoundary)
            (shortBinaryNumeralTerm tokenCount)
            targetIndexTerm
            (shortBinaryNumeralTerm targetStart) (by
              simpa [termValue_shortBinaryNumeralTerm, htargetIndex]
                using htargetStartEntry))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactFixedWidthEntryAtValuationExplicitHybridCertificate
              valuation
              (shortBinaryNumeralTerm targetBoundary)
              (shortBinaryNumeralTerm tokenCount)
              (‘!!targetIndexTerm + 1’ : ValuationTerm)
              (shortBinaryNumeralTerm targetFinish) (by
                simpa [termValue_shortBinaryNumeralTerm,
                  termValue_arithmeticAdd, termValue_arithmeticOne,
                  htargetIndex] using htargetFinishEntry))
            slicesAtValuation)))
  let terminal : CheckedHybridValuationBoundedFormulaCertificate valuation
      ((compactNumericVerifierTaskBoundedRowsEqTerminal
          tokenTable width tokenCount sourceBoundary targetBoundary
            sourceIndexTerm targetIndexTerm) ⇜
        ![shortBinaryNumeralTerm targetFinish,
          shortBinaryNumeralTerm targetStart,
          shortBinaryNumeralTerm sourceFinish,
          shortBinaryNumeralTerm sourceStart]) :=
    .cast
      (compactNumericVerifierTaskBoundedRowsEqTerminal_substitution_alignment
        tokenTable width tokenCount sourceBoundary targetBoundary
          sourceStart sourceFinish targetStart targetFinish
          sourceIndexTerm targetIndexTerm).symm terminalParts
  let terminalForBuilder :
      CheckedHybridValuationBoundedFormulaCertificate valuation
        ((compactNumericVerifierTaskBoundedRowsEqTerminal
            tokenTable width tokenCount sourceBoundary targetBoundary
              sourceIndexTerm targetIndexTerm) ⇜
          fun coordinate => shortBinaryNumeralTerm (values coordinate)) := by
    have hvalues :
        (fun coordinate => shortBinaryNumeralTerm (values coordinate)) =
          ![shortBinaryNumeralTerm targetFinish,
            shortBinaryNumeralTerm targetStart,
            shortBinaryNumeralTerm sourceFinish,
            shortBinaryNumeralTerm sourceStart] := by
      funext coordinate
      fin_cases coordinate <;> rfl
    rw [hvalues]
    exact terminal
  let installed := buildExplicitBoundedWitnessHybridCertificate
    valueBound
    (compactNumericVerifierTaskBoundedRowsEqTerminal
      tokenTable width tokenCount sourceBoundary targetBoundary
        sourceIndexTerm targetIndexTerm)
    values (by
      intro coordinate
      fin_cases coordinate
      · exact htargetFinishBound
      · exact htargetStartBound
      · exact hsourceFinishBound
      · exact hsourceStartBound) terminalForBuilder
  exact .cast
    (compactNumericVerifierTaskBoundedRowsEqAtValuationFormula_alignment
      tokenTable width tokenCount sourceBoundary targetBoundary valueBound
        sourceIndexTerm targetIndexTerm).symm
    (.cast
      (compactNumericVerifierTaskBoundedRowsEqExplicitFormula_eq_generic
        tokenTable width tokenCount sourceBoundary targetBoundary valueBound
          sourceIndexTerm targetIndexTerm).symm installed)

#print axioms compactNumericVerifierTaskBoundedRowsEqClosedFormula
#print axioms compactNumericVerifierTaskBoundedRowsEqClosedFormula_alignment
#print axioms compactNumericVerifierTaskBoundedRowsEqExplicitHybridCertificate
#print axioms compactNumericVerifierTaskBoundedRowsEqAtValuationFormula_alignment
#print axioms compactNumericVerifierTaskBoundedRowsEqAtValuationExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierTaskBoundedRowsEqExplicitHybridCertificate
