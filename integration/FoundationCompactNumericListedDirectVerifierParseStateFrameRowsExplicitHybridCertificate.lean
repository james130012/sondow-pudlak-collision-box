import integration.FoundationCompactNumericListedDirectVerifierParseStateFrameRows
import integration.FoundationCompactPAHybridValuationBoundedFormulaCompiler

/-!
# Explicit checked certificate for the parse-state frame

The parse-state frame has exactly three effective fields: the running-state
tag, a nonempty task stack, and the public parse-task tag.  This module closes
the original eight-coordinate formula directly from those three graph facts.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierParseStateFrameRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierTaskFormula
open FoundationCompactNumericListedDirectVerifierParseStateFrameRows
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem rewriting_embeddedClosedTerm
    {sourceVariables targetVariables : Type*}
    {sourceArity : Nat}
    (rewriting : Rew ℒₒᵣ sourceVariables sourceArity targetVariables 0)
    (term : ArithmeticSemiterm Empty 0) :
    rewriting
        ((Rew.emb : Rew ℒₒᵣ Empty sourceArity
            sourceVariables sourceArity)
          ((Rew.subst
            (![] : Fin 0 -> ArithmeticSemiterm Empty sourceArity)) term)) =
      (Rew.emb : Rew ℒₒᵣ Empty 0 targetVariables 0) term := by
  have hcomposition :
      rewriting.comp
          ((Rew.emb : Rew ℒₒᵣ Empty sourceArity
              sourceVariables sourceArity).comp
            (Rew.subst
              (![] : Fin 0 -> ArithmeticSemiterm Empty sourceArity))) =
        (Rew.emb : Rew ℒₒᵣ Empty 0 targetVariables 0) := by
    apply Rew.ext
    · intro coordinate
      exact Fin.elim0 coordinate
    · intro coordinate
      exact Empty.elim coordinate
  have happ := congrArg (fun candidate => candidate term) hcomposition
  simpa only [Rew.comp_app] using happ

private def fixedNumeralTerm (value : Nat) : ValuationTerm :=
  (Semiterm.Operator.numeral ℒₒᵣ value : Semiterm.Const ℒₒᵣ)

@[simp] private theorem termValue_fixedNumeralTerm (value : Nat) :
    termValue zeroValuation (fixedNumeralTerm value) = value := by
  unfold termValue fixedNumeralTerm
  rw [Semiterm.val_operator]
  rw [show
    (Semiterm.val ![] zeroValuation ∘
      (![] : Fin 0 -> ArithmeticSemiterm Nat 0)) = (![] : Fin 0 -> Nat) by
        funext index
        exact Fin.elim0 index]
  simpa using
    (LO.FirstOrder.Structure.numeral_eq_numeral
      (L := ℒₒᵣ) (M := Nat) value)

private def fixedNumeralEqFormula
    (left right : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm left) = !!(fixedNumeralTerm right)”

private def fixedNumeralLeFormula
    (left right : Nat) : ValuationFormula :=
  “!!(fixedNumeralTerm left) ≤ !!(shortBinaryNumeralTerm right)”

def compactNumericVerifierParseStateFrameRowsClosedFormula
    (currentTaskCount currentStatusTag : Nat)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
      compactNumericVerifierParseStateFrameRowsDef.val) ⇜
    ![shortBinaryNumeralTerm currentTaskCount,
      shortBinaryNumeralTerm currentStatusTag,
      shortBinaryNumeralTerm taskCoordinates.tag,
      shortBinaryNumeralTerm taskCoordinates.gammaCount,
      shortBinaryNumeralTerm taskCoordinates.firstCount,
      shortBinaryNumeralTerm taskCoordinates.secondCount,
      shortBinaryNumeralTerm taskCoordinates.witnessCount,
      shortBinaryNumeralTerm taskCoordinates.suffixCount]

def compactNumericVerifierParseStateFrameRowsPartsFormula
    (currentTaskCount currentStatusTag : Nat)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates) :
    ValuationFormula :=
  fixedNumeralEqFormula currentStatusTag 0 ⋏
    (fixedNumeralLeFormula 1 currentTaskCount ⋏
      fixedNumeralEqFormula taskCoordinates.tag 10)

theorem compactNumericVerifierParseStateFrameRowsClosedFormula_alignment
    (currentTaskCount currentStatusTag : Nat)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates) :
    compactNumericVerifierParseStateFrameRowsClosedFormula
        currentTaskCount currentStatusTag taskCoordinates =
      compactNumericVerifierParseStateFrameRowsPartsFormula
        currentTaskCount currentStatusTag taskCoordinates := by
  rcases taskCoordinates with
    ⟨start, finish, tag, gammaFinish, gammaCount, gammaBoundary,
      firstFinish, firstCount, secondFinish, secondCount,
      witnessFinish, witnessCount, suffixCount⟩
  unfold compactNumericVerifierParseStateFrameRowsClosedFormula
  unfold compactNumericVerifierParseStateFrameRowsPartsFormula
  unfold fixedNumeralEqFormula fixedNumeralLeFormula fixedNumeralTerm
  unfold compactNumericVerifierParseStateFrameRowsDef
  simp [Rew.comp_app, Rew.const, shortBinaryNumeralTerm,
    FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
    Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
    Semiterm.Operator.Zero.term_eq]
  constructor <;> apply rewriting_embeddedClosedTerm

private noncomputable def fixedNumeralEqCertificate
    (left right : Nat) (heq : left = right) :
    HybridCertificate (fixedNumeralEqFormula left right) := by
  apply CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm left, fixedNumeralTerm right]
  change termValue zeroValuation (shortBinaryNumeralTerm left) =
    termValue zeroValuation (fixedNumeralTerm right)
  simpa [termValue_shortBinaryNumeralTerm] using heq

private noncomputable def valuationLeCertificate
    (leftTerm rightTerm : ValuationTerm)
    (hle : termValue zeroValuation leftTerm ≤
      termValue zeroValuation rightTerm) :
    HybridCertificate “!!leftTerm ≤ !!rightTerm” := by
  if heq : termValue zeroValuation leftTerm =
      termValue zeroValuation rightTerm then
    let equality :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.Eq.eq ![leftTerm, rightTerm] heq
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionLeft equality)
  else
    have hlt : termValue zeroValuation leftTerm <
        termValue zeroValuation rightTerm := Nat.lt_of_le_of_ne hle heq
    let strict :=
      CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
        zeroValuation Language.ORing.Rel.lt ![leftTerm, rightTerm] hlt
    exact .cast (Semiformula.Operator.le_def _ _).symm
      (.disjunctionRight strict)

noncomputable def
    compactNumericVerifierParseStateFrameRowsExplicitHybridCertificateOfGraph
    (currentTaskCount currentStatusTag : Nat)
    (taskCoordinates : CompactNumericVerifierTaskRowCoordinates)
    (hframe : CompactNumericVerifierParseStateFrameRows
      currentTaskCount currentStatusTag taskCoordinates) :
    HybridCertificate
      (compactNumericVerifierParseStateFrameRowsClosedFormula
        currentTaskCount currentStatusTag taskCoordinates) := by
  rw [compactNumericVerifierParseStateFrameRowsClosedFormula_alignment]
  rcases hframe with ⟨hstatus, hcount, htag⟩
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (fixedNumeralEqCertificate currentStatusTag 0 hstatus)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (valuationLeCertificate
        (fixedNumeralTerm 1)
        (shortBinaryNumeralTerm currentTaskCount) (by
          simpa [termValue_shortBinaryNumeralTerm] using hcount))
      (fixedNumeralEqCertificate taskCoordinates.tag 10 htag))

#print axioms compactNumericVerifierParseStateFrameRowsClosedFormula_alignment
#print axioms
  compactNumericVerifierParseStateFrameRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierParseStateFrameRowsExplicitHybridCertificate
