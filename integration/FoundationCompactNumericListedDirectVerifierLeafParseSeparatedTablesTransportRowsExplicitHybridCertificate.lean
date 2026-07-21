import integration.FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
import integration.FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectChildResultBoundedRowExposedExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectVerifierLeafParseStackRowsExplicitHybridCertificate

/-!
# Explicit hybrid certificate for separated leaf parse transport rows

The closed transport graph is assembled from its three closed table/row
certificates, one cross-table certificate at the original `rootStart + 1`
valuation term, the result equality, and the leaf stack certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRowsExplicitHybridCertificate

open FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRows
open FoundationCompactNumericListedDirectCrossTableSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectChildResultBoundedRowExposedExplicitHybridCertificate
open FoundationCompactNumericListedDirectVerifierLeafParseStackRowsExplicitHybridCertificate
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler

private def zeroValuation : Nat -> Nat := fun _ => 0

private abbrev HybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate zeroValuation formula

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

private noncomputable def valuationEqCertificate
    (left right : ValuationTerm)
    (heq : termValue zeroValuation left = termValue zeroValuation right) :
    HybridCertificate “!!left = !!right” := by
  exact CheckedHybridValuationBoundedFormulaCertificate.positiveAtomic
    zeroValuation Language.Eq.eq ![left, right] heq

/-- Close all forty-three transport-row coordinates by binary numerals. -/
def compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat)
    compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef.val) ⇜
    ![shortBinaryNumeralTerm stateTable,
      shortBinaryNumeralTerm stateWidth,
      shortBinaryNumeralTerm stateTokenCount,
      shortBinaryNumeralTerm sourceTaskBoundary,
      shortBinaryNumeralTerm sourceTaskCount,
      shortBinaryNumeralTerm targetTaskBoundary,
      shortBinaryNumeralTerm targetTaskCount,
      shortBinaryNumeralTerm sourceValueBoundary,
      shortBinaryNumeralTerm sourceValueCount,
      shortBinaryNumeralTerm targetValueBoundary,
      shortBinaryNumeralTerm targetValueCount,
      shortBinaryNumeralTerm currentTaskTableWidth,
      shortBinaryNumeralTerm currentTaskValueBound,
      shortBinaryNumeralTerm currentValueTableWidth,
      shortBinaryNumeralTerm currentValueValueBound,
      shortBinaryNumeralTerm nextTaskTableWidth,
      shortBinaryNumeralTerm nextTaskValueBound,
      shortBinaryNumeralTerm nextValueTableWidth,
      shortBinaryNumeralTerm nextValueValueBound,
      shortBinaryNumeralTerm nextStart,
      shortBinaryNumeralTerm nextProofFinish,
      shortBinaryNumeralTerm nextCertificateFinish,
      shortBinaryNumeralTerm nextStatusTag,
      shortBinaryNumeralTerm proofTable,
      shortBinaryNumeralTerm proofWidth,
      shortBinaryNumeralTerm proofTokenCount,
      shortBinaryNumeralTerm rootStart,
      shortBinaryNumeralTerm rootGammaFinish,
      shortBinaryNumeralTerm witnessFinish,
      shortBinaryNumeralTerm rootFinish,
      shortBinaryNumeralTerm certificateTable,
      shortBinaryNumeralTerm certificateWidth,
      shortBinaryNumeralTerm certificateTokenCount,
      shortBinaryNumeralTerm suffixStart,
      shortBinaryNumeralTerm suffixFinish,
      shortBinaryNumeralTerm targetStart,
      shortBinaryNumeralTerm targetFinish,
      shortBinaryNumeralTerm targetGammaFinish,
      shortBinaryNumeralTerm targetGammaCount,
      shortBinaryNumeralTerm targetGammaBoundary,
      shortBinaryNumeralTerm targetBool,
      shortBinaryNumeralTerm targetGammaBoundarySize,
      shortBinaryNumeralTerm resultBool]

private def compactNumericVerifierLeafParseSeparatedTablesTransportRowsPartsFormula
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) :
    ValuationFormula :=
  compactFixedWidthCrossTableSlicesEqClosedFormula
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
      stateTable stateWidth stateTokenCount nextStart nextProofFinish ⋏
    (compactFixedWidthCrossTableSlicesEqClosedFormula
        certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
        stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish ⋏
      (compactNumericChildResultBoundedRowExposedClosedFormula
          stateTable stateWidth stateTokenCount targetValueBoundary nextValueValueBound 0
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize ⋏
        (compactFixedWidthCrossTableSlicesEqAtValuationFormula
            (shortBinaryNumeralTerm proofTable)
            (shortBinaryNumeralTerm proofWidth)
            (shortBinaryNumeralTerm proofTokenCount)
            (‘!!(shortBinaryNumeralTerm rootStart) + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm rootGammaFinish)
            (shortBinaryNumeralTerm stateTable)
            (shortBinaryNumeralTerm stateWidth)
            (shortBinaryNumeralTerm stateTokenCount)
            (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm targetGammaFinish) ⋏
          (“!!(shortBinaryNumeralTerm targetBool) =
              !!(shortBinaryNumeralTerm resultBool)” ⋏
            compactNumericVerifierLeafParseStackRowsClosedFormula
              stateTable stateWidth stateTokenCount
              sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
              sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
              targetGammaBoundary targetGammaCount
              currentTaskTableWidth currentTaskValueBound
              currentValueTableWidth currentValueValueBound
              nextTaskTableWidth nextTaskValueBound
              nextValueTableWidth nextValueValueBound
              resultBool nextStatusTag))))

/-- The closed transport formula decomposes into the six explicit components. -/
theorem compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula_alignment
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat) :
    compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula
        stateTable stateWidth stateTokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        proofTable proofWidth proofTokenCount rootStart rootGammaFinish
        witnessFinish rootFinish
        certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool =
      compactNumericVerifierLeafParseSeparatedTablesTransportRowsPartsFormula
        stateTable stateWidth stateTokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        proofTable proofWidth proofTokenCount rootStart rootGammaFinish
        witnessFinish rootFinish
        certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool := by
  unfold compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula
  unfold compactNumericVerifierLeafParseSeparatedTablesTransportRowsPartsFormula
  unfold compactNumericVerifierLeafParseSeparatedTablesTransportRowsDef
  simp [compactFixedWidthCrossTableSlicesEqClosedFormula,
    compactFixedWidthCrossTableSlicesEqAtValuationFormula,
    compactNumericChildResultBoundedRowExposedClosedFormula,
    compactNumericVerifierLeafParseStackRowsClosedFormula,
    ← TransitiveRewriting.comp_app]
  repeat' apply And.intro
  all_goals
    congr 1
    congr 1
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [Rew.comp_app, Rew.subst_bvar, arithmeticZeroTerm,
          Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
          Semiterm.Operator.numeral_one, Semiterm.Operator.Zero.term_eq,
          Semiterm.Operator.One.term_eq, Semiterm.Operator.Add.term_eq,
          Rew.func, Matrix.fun_eq_vec_two, Matrix.empty_eq]
    · intro coordinate
      exact Empty.elim coordinate

/-- Assemble the transport certificate from every semantic component directly. -/
noncomputable def compactNumericVerifierLeafParseSeparatedTablesTransportRowsExplicitHybridCertificate
    (stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool : Nat)
    (htransport : CompactNumericVerifierLeafParseSeparatedTablesTransportRows
      stateTable stateWidth stateTokenCount
      sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
      sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
      currentTaskTableWidth currentTaskValueBound
      currentValueTableWidth currentValueValueBound
      nextTaskTableWidth nextTaskValueBound
      nextValueTableWidth nextValueValueBound
      nextStart nextProofFinish nextCertificateFinish nextStatusTag
      proofTable proofWidth proofTokenCount rootStart rootGammaFinish
      witnessFinish rootFinish
      certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
      targetStart targetFinish targetGammaFinish targetGammaCount
      targetGammaBoundary targetBool targetGammaBoundarySize resultBool) :
    HybridCertificate
      (compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula
        stateTable stateWidth stateTokenCount
        sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
        sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
        currentTaskTableWidth currentTaskValueBound
        currentValueTableWidth currentValueValueBound
        nextTaskTableWidth nextTaskValueBound
        nextValueTableWidth nextValueValueBound
        nextStart nextProofFinish nextCertificateFinish nextStatusTag
        proofTable proofWidth proofTokenCount rootStart rootGammaFinish
        witnessFinish rootFinish
        certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
        targetStart targetFinish targetGammaFinish targetGammaCount
        targetGammaBoundary targetBool targetGammaBoundarySize resultBool) := by
  rcases htransport with
    ⟨hproofPayload, hcertificatePayload, htargetRow, hproofGamma,
      hresult, hstackRows⟩
  let proofPayloadCount := Classical.choose hproofPayload
  have hproofPayloadFacts := Classical.choose_spec hproofPayload
  have hproofPayloadSourceCount := hproofPayloadFacts.1
  have hproofPayloadTargetCount := hproofPayloadFacts.2.1
  have hproofPayloadSourceEndpoint := hproofPayloadFacts.2.2.1
  have hproofPayloadTargetEndpoint := hproofPayloadFacts.2.2.2.1
  have hproofPayloadSourceFinish := hproofPayloadFacts.2.2.2.2.1
  have hproofPayloadTargetFinish := hproofPayloadFacts.2.2.2.2.2.1
  have hproofPayloadBits := hproofPayloadFacts.2.2.2.2.2.2
  let certificatePayloadCount := Classical.choose hcertificatePayload
  have hcertificatePayloadFacts := Classical.choose_spec hcertificatePayload
  have hcertificatePayloadSourceCount := hcertificatePayloadFacts.1
  have hcertificatePayloadTargetCount := hcertificatePayloadFacts.2.1
  have hcertificatePayloadSourceEndpoint := hcertificatePayloadFacts.2.2.1
  have hcertificatePayloadTargetEndpoint :=
    hcertificatePayloadFacts.2.2.2.1
  have hcertificatePayloadSourceFinish :=
    hcertificatePayloadFacts.2.2.2.2.1
  have hcertificatePayloadTargetFinish :=
    hcertificatePayloadFacts.2.2.2.2.2.1
  have hcertificatePayloadBits := hcertificatePayloadFacts.2.2.2.2.2.2
  let proofGammaCount := Classical.choose hproofGamma
  have hproofGammaFacts := Classical.choose_spec hproofGamma
  have hproofGammaSourceCount := hproofGammaFacts.1
  have hproofGammaTargetCount := hproofGammaFacts.2.1
  have hproofGammaSourceEndpoint := hproofGammaFacts.2.2.1
  have hproofGammaTargetEndpoint := hproofGammaFacts.2.2.2.1
  have hproofGammaSourceFinish := hproofGammaFacts.2.2.2.2.1
  have hproofGammaTargetFinish := hproofGammaFacts.2.2.2.2.2.1
  have hproofGammaBits := hproofGammaFacts.2.2.2.2.2.2
  rw [compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula_alignment]
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate
      proofTable proofWidth proofTokenCount witnessFinish rootFinish
      stateTable stateWidth stateTokenCount nextStart nextProofFinish
      proofPayloadCount hproofPayloadSourceCount hproofPayloadTargetCount
      hproofPayloadSourceEndpoint hproofPayloadTargetEndpoint
      hproofPayloadSourceFinish hproofPayloadTargetFinish hproofPayloadBits)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactFixedWidthCrossTableSlicesEqExplicitHybridCertificate
        certificateTable certificateWidth certificateTokenCount suffixStart suffixFinish
        stateTable stateWidth stateTokenCount nextProofFinish nextCertificateFinish
        certificatePayloadCount hcertificatePayloadSourceCount
        hcertificatePayloadTargetCount hcertificatePayloadSourceEndpoint
        hcertificatePayloadTargetEndpoint hcertificatePayloadSourceFinish
        hcertificatePayloadTargetFinish hcertificatePayloadBits)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactNumericChildResultBoundedRowExposedExplicitHybridCertificate
          stateTable stateWidth stateTokenCount targetValueBoundary nextValueValueBound 0
          targetStart targetFinish targetGammaFinish targetGammaCount
          targetGammaBoundary targetBool targetGammaBoundarySize htargetRow)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactFixedWidthCrossTableSlicesEqAtValuationExplicitHybridCertificate
            zeroValuation
            (shortBinaryNumeralTerm proofTable)
            (shortBinaryNumeralTerm proofWidth)
            (shortBinaryNumeralTerm proofTokenCount)
            (‘!!(shortBinaryNumeralTerm rootStart) + 1’ : ValuationTerm)
            (shortBinaryNumeralTerm rootGammaFinish)
            (shortBinaryNumeralTerm stateTable)
            (shortBinaryNumeralTerm stateWidth)
            (shortBinaryNumeralTerm stateTokenCount)
            (shortBinaryNumeralTerm targetStart)
            (shortBinaryNumeralTerm targetGammaFinish)
            proofGammaCount
            (by simpa [zeroValuation, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne] using
                hproofGammaSourceCount)
            (by simpa [zeroValuation, termValue_shortBinaryNumeralTerm] using
                hproofGammaTargetCount)
            (by simpa [zeroValuation, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne] using
                hproofGammaSourceEndpoint)
            (by simpa [zeroValuation, termValue_shortBinaryNumeralTerm] using
                hproofGammaTargetEndpoint)
            (by simpa [zeroValuation, termValue_shortBinaryNumeralTerm,
              termValue_arithmeticAdd, termValue_arithmeticOne] using
                hproofGammaSourceFinish)
            (by simpa [zeroValuation, termValue_shortBinaryNumeralTerm] using
                hproofGammaTargetFinish)
            (by
              intro offset hoffset bitIndex hbitIndex
              have hbitIndex' : bitIndex < proofWidth + stateWidth := by
                simpa [zeroValuation,
                  termValue_shortBinaryNumeralTerm] using hbitIndex
              simpa [zeroValuation, termValue_shortBinaryNumeralTerm,
                termValue_arithmeticAdd, termValue_arithmeticOne] using
                hproofGammaBits offset hoffset bitIndex hbitIndex'))
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (valuationEqCertificate
              (shortBinaryNumeralTerm targetBool)
              (shortBinaryNumeralTerm resultBool) (by
                simpa [zeroValuation, termValue_shortBinaryNumeralTerm] using hresult))
            (compactNumericVerifierLeafParseStackRowsExplicitHybridCertificate
              stateTable stateWidth stateTokenCount
              sourceTaskBoundary sourceTaskCount targetTaskBoundary targetTaskCount
              sourceValueBoundary sourceValueCount targetValueBoundary targetValueCount
              targetGammaBoundary targetGammaCount
              currentTaskTableWidth currentTaskValueBound
              currentValueTableWidth currentValueValueBound
              nextTaskTableWidth nextTaskValueBound
              nextValueTableWidth nextValueValueBound
              resultBool nextStatusTag hstackRows)))))

#print axioms compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula
#print axioms compactNumericVerifierLeafParseSeparatedTablesTransportRowsClosedFormula_alignment
#print axioms compactNumericVerifierLeafParseSeparatedTablesTransportRowsExplicitHybridCertificate

end FoundationCompactNumericListedDirectVerifierLeafParseSeparatedTablesTransportRowsExplicitHybridCertificate
