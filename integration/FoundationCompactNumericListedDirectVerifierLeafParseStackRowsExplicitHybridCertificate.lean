import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRows
import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectChildResultListPushDropRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for leaf parse stack rows

The leaf stack transition is a closed conjunction.  Its five scalar fields are
checked as positive equality atoms; the two list transitions are delegated to
their independently explicit certificates.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierLeafParseStackRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierLeafParseStackRows
open FoundationCompactNumericListedDirectVerifierTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectChildResultListPushDropRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

/-- Close the public inputs of the leaf stack-row formula by binary numerals. -/
def compactNumericVerifierLeafParseStackRowsClosedFormula
    (tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierLeafParseStackRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm sourceTaskBoundary,
      shortBinaryNumeralTerm sourceTaskCount,
      shortBinaryNumeralTerm targetTaskBoundary,
      shortBinaryNumeralTerm targetTaskCount,
      shortBinaryNumeralTerm sourceValueBoundary,
      shortBinaryNumeralTerm sourceValueCount,
      shortBinaryNumeralTerm targetValueBoundary,
      shortBinaryNumeralTerm targetValueCount,
      shortBinaryNumeralTerm gammaBoundary,
      shortBinaryNumeralTerm gammaCount,
      shortBinaryNumeralTerm currentTaskTableWidth,
      shortBinaryNumeralTerm currentTaskValueBound,
      shortBinaryNumeralTerm currentValueTableWidth,
      shortBinaryNumeralTerm currentValueValueBound,
      shortBinaryNumeralTerm nextTaskTableWidth,
      shortBinaryNumeralTerm nextTaskValueBound,
      shortBinaryNumeralTerm nextValueTableWidth,
      shortBinaryNumeralTerm nextValueValueBound,
      shortBinaryNumeralTerm resultBool,
      shortBinaryNumeralTerm nextStatusTag]

private def compactNumericVerifierLeafParseStackRowsPartsFormula
    (tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm nextTaskTableWidth) =
      !!(shortBinaryNumeralTerm currentTaskTableWidth)” ⋏
    (“!!(shortBinaryNumeralTerm nextTaskValueBound) =
        !!(shortBinaryNumeralTerm currentTaskValueBound)” ⋏
      (“!!(shortBinaryNumeralTerm nextValueTableWidth) =
          !!(shortBinaryNumeralTerm currentValueTableWidth)” ⋏
        (“!!(shortBinaryNumeralTerm nextValueValueBound) =
            !!(shortBinaryNumeralTerm currentValueValueBound)” ⋏
          (“!!(shortBinaryNumeralTerm nextStatusTag) = 0” ⋏
            (compactNumericVerifierTaskListDropRowsAtValuationFormula
              tokenTable width tokenCount
              sourceTaskBoundary sourceTaskCount
              targetTaskBoundary targetTaskCount
              currentTaskTableWidth currentTaskValueBound
              (‘1’ : ValuationTerm) ⋏
              compactNumericChildResultListPushDropRowsClosedFormula
                tokenTable width tokenCount
                sourceValueBoundary sourceValueCount
                targetValueBoundary targetValueCount
                gammaBoundary gammaCount
                currentValueTableWidth currentValueValueBound 0 resultBool)))))

/-- The closed leaf formula decomposes into scalar checks and list certificates. -/
theorem compactNumericVerifierLeafParseStackRowsClosedFormula_alignment
    (tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag : Nat) :
    compactNumericVerifierLeafParseStackRowsClosedFormula
        tokenTable width tokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        gammaBoundary gammaCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        resultBool nextStatusTag =
      compactNumericVerifierLeafParseStackRowsPartsFormula
        tokenTable width tokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        gammaBoundary gammaCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        resultBool nextStatusTag := by
  unfold compactNumericVerifierLeafParseStackRowsClosedFormula
  unfold compactNumericVerifierLeafParseStackRowsPartsFormula
  unfold compactNumericVerifierLeafParseStackRowsDef
  simp [compactNumericVerifierTaskListDropRowsAtValuationFormula,
    compactNumericChildResultListPushDropRowsClosedFormula,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Semiterm.Operator.operator,
          Semiterm.Operator.numeral_one, Semiterm.Operator.One.term_eq,
          Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, shortBinaryNumeralTerm,
          FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
          Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
          Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate

private noncomputable def valuationEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate “!!left = !!right” := by
  exact CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq

/-- Assemble the leaf certificate from its semantic conjunction. -/
noncomputable def compactNumericVerifierLeafParseStackRowsExplicitHybridCertificate
    (tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag : Nat)
    (hrows : CompactNumericVerifierLeafParseStackRows
      tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      resultBool nextStatusTag) :
    HybridCertificate
      (compactNumericVerifierLeafParseStackRowsClosedFormula
        tokenTable width tokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        gammaBoundary gammaCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        resultBool nextStatusTag) := by
  rcases hrows with
    ⟨htaskWidth, htaskBound, hvalueWidth, hvalueBound,
      hstatus, htaskDrop, hvaluePush⟩
  rw [compactNumericVerifierLeafParseStackRowsClosedFormula_alignment]
  let taskWidth := valuationEqCertificate
    (shortBinaryNumeralTerm nextTaskTableWidth)
    (shortBinaryNumeralTerm currentTaskTableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using htaskWidth)
  let taskBound := valuationEqCertificate
    (shortBinaryNumeralTerm nextTaskValueBound)
    (shortBinaryNumeralTerm currentTaskValueBound) (by
      simpa [termValue_shortBinaryNumeralTerm] using htaskBound)
  let valueWidth := valuationEqCertificate
    (shortBinaryNumeralTerm nextValueTableWidth)
    (shortBinaryNumeralTerm currentValueTableWidth) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueWidth)
  let valueBound := valuationEqCertificate
    (shortBinaryNumeralTerm nextValueValueBound)
    (shortBinaryNumeralTerm currentValueValueBound) (by
      simpa [termValue_shortBinaryNumeralTerm] using hvalueBound)
  let status := valuationEqCertificate
    (shortBinaryNumeralTerm nextStatusTag) (‘0’ : ValuationTerm) (by
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero] using hstatus)
  let taskDrop :=
    compactNumericVerifierTaskListDropRowsAtValuationExplicitHybridCertificate
      tokenTable width tokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      currentTaskTableWidth currentTaskValueBound 1
      (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) htaskDrop
  let valuePush :=
    compactNumericChildResultListPushDropRowsExplicitHybridCertificate
      tokenTable width tokenCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      gammaBoundary gammaCount
      currentValueTableWidth currentValueValueBound 0 resultBool hvaluePush
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction taskWidth
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction taskBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction valueWidth
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction valueBound
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction status
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              taskDrop valuePush)))))

#print axioms compactNumericVerifierLeafParseStackRowsClosedFormula
#print axioms compactNumericVerifierLeafParseStackRowsClosedFormula_alignment
#print axioms compactNumericVerifierLeafParseStackRowsExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierLeafParseStackRowsExplicitHybridCertificate
