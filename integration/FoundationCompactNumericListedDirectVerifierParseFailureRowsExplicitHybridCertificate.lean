import integration.FoundationCompactNumericListedDirectVerifierParseFailureRows
import integration.FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierTaskListDropRowsExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectChildResultListDropRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for verifier parse-failure rows

The parse-failure state transition is a closed conjunction of four preserved
size fields, one token-slice equality, two prefix drops, and the failed-status
pair.  The slice witness is chosen from the original semantic graph, while the
two drops retain the PA constants appearing in the quoted row formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierParseFailureRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierParseFailureRows
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectChildResultListDropRowsExplicitHybridCertificate
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

/-- Close all twenty-five parse-failure-row coordinates by binary numerals. -/
def compactNumericVerifierParseFailureRowsClosedFormula
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool : Nat) : ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactNumericVerifierParseFailureRowsDef.val) ⇜
    ![shortBinaryNumeralTerm tokenTable,
      shortBinaryNumeralTerm width,
      shortBinaryNumeralTerm tokenCount,
      shortBinaryNumeralTerm currentStart,
      shortBinaryNumeralTerm currentCertificateFinish,
      shortBinaryNumeralTerm currentTaskBoundary,
      shortBinaryNumeralTerm currentTaskCount,
      shortBinaryNumeralTerm currentValueBoundary,
      shortBinaryNumeralTerm currentValueCount,
      shortBinaryNumeralTerm currentTaskTableWidth,
      shortBinaryNumeralTerm currentTaskValueBound,
      shortBinaryNumeralTerm currentValueTableWidth,
      shortBinaryNumeralTerm currentValueValueBound,
      shortBinaryNumeralTerm nextStart,
      shortBinaryNumeralTerm nextCertificateFinish,
      shortBinaryNumeralTerm nextTaskBoundary,
      shortBinaryNumeralTerm nextTaskCount,
      shortBinaryNumeralTerm nextValueBoundary,
      shortBinaryNumeralTerm nextValueCount,
      shortBinaryNumeralTerm nextTaskTableWidth,
      shortBinaryNumeralTerm nextTaskValueBound,
      shortBinaryNumeralTerm nextValueTableWidth,
      shortBinaryNumeralTerm nextValueValueBound,
      shortBinaryNumeralTerm nextStatusTag,
      shortBinaryNumeralTerm nextStatusBool]

private def compactNumericVerifierParseFailureRowsPartsFormula
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm nextTaskTableWidth) =
      !!(shortBinaryNumeralTerm currentTaskTableWidth)” ⋏
    (“!!(shortBinaryNumeralTerm nextTaskValueBound) =
        !!(shortBinaryNumeralTerm currentTaskValueBound)” ⋏
      (“!!(shortBinaryNumeralTerm nextValueTableWidth) =
          !!(shortBinaryNumeralTerm currentValueTableWidth)” ⋏
        (“!!(shortBinaryNumeralTerm nextValueValueBound) =
            !!(shortBinaryNumeralTerm currentValueValueBound)” ⋏
          (compactFixedWidthTokenSlicesEqClosedFormula
              tokenTable width tokenCount currentStart currentCertificateFinish
                nextStart nextCertificateFinish ⋏
            (compactNumericVerifierTaskListDropRowsAtValuationFormula
                tokenTable width tokenCount
                currentTaskBoundary currentTaskCount
                nextTaskBoundary nextTaskCount
                currentTaskTableWidth currentTaskValueBound
                (‘1’ : ValuationTerm) ⋏
              (compactNumericChildResultListDropRowsAtValuationFormula
                  tokenTable width tokenCount
                  currentValueBoundary currentValueCount
                  nextValueBoundary nextValueCount
                  currentValueTableWidth currentValueValueBound
                  (‘0’ : ValuationTerm) ⋏
                (“!!(shortBinaryNumeralTerm nextStatusTag) = 1” ⋏
                  “!!(shortBinaryNumeralTerm nextStatusBool) = 0”)))))))

/-- The closed formula matches the nine components of the semantic graph. -/
theorem compactNumericVerifierParseFailureRowsClosedFormula_alignment
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool : Nat) :
    compactNumericVerifierParseFailureRowsClosedFormula
        tokenTable width tokenCount
        currentStart currentCertificateFinish
        currentTaskBoundary currentTaskCount
        currentValueBoundary currentValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextStart nextCertificateFinish
        nextTaskBoundary nextTaskCount
        nextValueBoundary nextValueCount
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStatusTag nextStatusBool =
      compactNumericVerifierParseFailureRowsPartsFormula
        tokenTable width tokenCount
        currentStart currentCertificateFinish
        currentTaskBoundary currentTaskCount
        currentValueBoundary currentValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextStart nextCertificateFinish
        nextTaskBoundary nextTaskCount
        nextValueBoundary nextValueCount
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStatusTag nextStatusBool := by
  unfold compactNumericVerifierParseFailureRowsClosedFormula
  unfold compactNumericVerifierParseFailureRowsPartsFormula
  unfold compactNumericVerifierParseFailureRowsDef
  simp [compactFixedWidthTokenSlicesEqClosedFormula,
    compactNumericVerifierTaskListDropRowsAtValuationFormula,
    compactNumericChildResultListDropRowsAtValuationFormula,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, shortBinaryNumeralTerm,
          Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
          Semiterm.Operator.numeral_one, Semiterm.Operator.Zero.term_eq,
          Semiterm.Operator.One.term_eq, Rew.func, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate

private theorem termValue_arithmeticZero (valuation : Nat -> Nat) :
    termValue valuation (‘0’ : ValuationTerm) = 0 := by
  exact termValue_zero valuation ![]

private theorem termValue_arithmeticOne (valuation : Nat -> Nat) :
    termValue valuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one valuation ![]

private noncomputable def valuationEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate “!!left = !!right” := by
  exact CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq

/-- Assemble the parse-failure certificate from its original semantic graph. -/
noncomputable def compactNumericVerifierParseFailureRowsExplicitHybridCertificate
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool : Nat)
    (hrows : CompactNumericVerifierParseFailureRows
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool) :
    HybridCertificate
      (compactNumericVerifierParseFailureRowsClosedFormula
        tokenTable width tokenCount
        currentStart currentCertificateFinish
        currentTaskBoundary currentTaskCount
        currentValueBoundary currentValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextStart nextCertificateFinish
        nextTaskBoundary nextTaskCount
        nextValueBoundary nextValueCount
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStatusTag nextStatusBool) := by
  rcases hrows with
    ⟨htaskWidth, htaskBound, hvalueWidth, hvalueBound, hslice,
      htaskDrop, hvalueDrop, hstatusTag, hstatusBool⟩
  let sliceCount := Classical.choose hslice
  have hsliceSpec := Classical.choose_spec hslice
  rw [compactNumericVerifierParseFailureRowsClosedFormula_alignment]
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
  let slice := compactFixedWidthTokenSlicesEqExplicitHybridCertificate
    tokenTable width tokenCount currentStart currentCertificateFinish
    nextStart nextCertificateFinish sliceCount hsliceSpec.1 hsliceSpec.2.1
    hsliceSpec.2.2.1 hsliceSpec.2.2.2.1 hsliceSpec.2.2.2.2.1
    hsliceSpec.2.2.2.2.2
  let taskDrop :=
    compactNumericVerifierTaskListDropRowsAtValuationExplicitHybridCertificate
      tokenTable width tokenCount
      currentTaskBoundary currentTaskCount
      nextTaskBoundary nextTaskCount
      currentTaskTableWidth currentTaskValueBound 1
      (‘1’ : ValuationTerm) (termValue_arithmeticOne zeroValuation) htaskDrop
  let valueDrop :=
    compactNumericChildResultListDropRowsAtValuationExplicitHybridCertificate
      tokenTable width tokenCount
      currentValueBoundary currentValueCount
      nextValueBoundary nextValueCount
      currentValueTableWidth currentValueValueBound 0
      (‘0’ : ValuationTerm) (termValue_arithmeticZero zeroValuation) hvalueDrop
  let statusTag := valuationEqCertificate
    (shortBinaryNumeralTerm nextStatusTag) (‘1’ : ValuationTerm) (by
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticOne] using hstatusTag)
  let statusBool := valuationEqCertificate
    (shortBinaryNumeralTerm nextStatusBool) (‘0’ : ValuationTerm) (by
      simpa [termValue_shortBinaryNumeralTerm,
        termValue_arithmeticZero] using hstatusBool)
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction taskWidth
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction taskBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction valueWidth
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction valueBound
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction slice
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction taskDrop
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                valueDrop
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  statusTag statusBool)))))))

/-- Alias emphasizing that the certificate consumes the semantic graph itself. -/
noncomputable def compactNumericVerifierParseFailureRowsExplicitHybridCertificateOfGraph
    (tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool : Nat)
    (hrows : CompactNumericVerifierParseFailureRows
      tokenTable width tokenCount
      currentStart currentCertificateFinish
      currentTaskBoundary currentTaskCount
      currentValueBoundary currentValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextStart nextCertificateFinish
      nextTaskBoundary nextTaskCount
      nextValueBoundary nextValueCount
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStatusTag nextStatusBool) :
    HybridCertificate
      (compactNumericVerifierParseFailureRowsClosedFormula
        tokenTable width tokenCount
        currentStart currentCertificateFinish
        currentTaskBoundary currentTaskCount
        currentValueBoundary currentValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextStart nextCertificateFinish
        nextTaskBoundary nextTaskCount
        nextValueBoundary nextValueCount
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStatusTag nextStatusBool) := by
  exact compactNumericVerifierParseFailureRowsExplicitHybridCertificate
    tokenTable width tokenCount
    currentStart currentCertificateFinish
    currentTaskBoundary currentTaskCount
    currentValueBoundary currentValueCount
    currentTaskTableWidth currentTaskValueBound
    currentValueTableWidth currentValueValueBound
    nextStart nextCertificateFinish
    nextTaskBoundary nextTaskCount
    nextValueBoundary nextValueCount
    nextTaskTableWidth nextTaskValueBound
    nextValueTableWidth nextValueValueBound
    nextStatusTag nextStatusBool hrows

#print axioms compactNumericVerifierParseFailureRowsClosedFormula
#print axioms compactNumericVerifierParseFailureRowsClosedFormula_alignment
#print axioms compactNumericVerifierParseFailureRowsExplicitHybridCertificate
#print axioms
  compactNumericVerifierParseFailureRowsExplicitHybridCertificateOfGraph

end FoundationCompactNumericListedDirectVerifierParseFailureRowsExplicitHybridCertificate
