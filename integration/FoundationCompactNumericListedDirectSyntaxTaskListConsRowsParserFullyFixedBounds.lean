import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadInstalledFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalFullyFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed ConsRows certificate for the parser formula-task head -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationBoundedFormulaCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserHeadInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalFullyFixedBounds

private abbrev parserConsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

private abbrev parserFixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private theorem termValue_parserFixedNumeralTerm
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (parserFixedNumeralTerm value) = value := by
  simp [parserFixedNumeralTerm,
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm,
    termValue]

def taskConsParserAssemblySyntaxEnvelope
    (numericBound bitBound : Nat) : Nat :=
  taskConsCountFullyFixedPayloadPolynomial bitBound +
    taskConsParserHeadInstalledPayloadEnvelope numericBound bitBound +
    taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound bitBound +
    2 * (binaryNatCode 4).length + 1

def taskConsParserFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (taskConsParserAssemblySyntaxEnvelope numericBound bitBound)
    (taskConsCountFullyFixedPayloadPolynomial bitBound)
    (taskConsParserHeadInstalledPayloadEnvelope numericBound bitBound)
    (taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound bitBound)

theorem taskConsParserFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      (parserFixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (parserFixedNumeralTerm 0)).freeVariables = ∅ := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
  let tailFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  have hcountClosed : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    exact taskConsCountFormula_freeVariables_eq_empty sourceCount targetCount
  have hheadClosed : headFormula.freeVariables = ∅ := by
    dsimp only [headFormula]
    exact taskConsParserHeadBody_freeVariables_eq_empty tokenTable width
      tokenCount targetBoundary binderArity
  have htailClosed : tailFormula.freeVariables = ∅ := by
    have hraw :=
      compactAdditiveSyntaxTaskListConsRowsTailOuterFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    have halign :
        (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount))
          (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
            tokenCount sourceBoundary targetBoundary)) =
        (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
          tokenCount sourceBoundary targetBoundary).ballLT
            (shortBinaryNumeralTerm sourceCount) := by
      rw [termBoundedUniversal_eq_ball]
      rfl
    dsimp only [tailFormula]
    rw [← halign]
    exact hraw
  rw [compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment]
  unfold
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitFormula
  simp only [LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
    hheadClosed, htailClosed, countFormula, headFormula, tailFormula,
    Finset.union_empty]

theorem
    taskConsParserCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htargetCountValue : targetCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary 1 binderArity 0)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount 1 binderArity 0 (parserFixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
          (termValue_parserFixedNumeralTerm · 1)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_parserFixedNumeralTerm · 0)
          hcount headData tailRows) <=
      taskConsParserFullyFixedPayloadEnvelope numericBound bitBound := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (parserFixedNumeralTerm 1)
      (shortBinaryNumeralTerm binderArity) (parserFixedNumeralTerm 0)
  let tailFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let countCertificate :=
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
      sourceCount targetCount hcount
  let headCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
      tokenTable width tokenCount targetBoundary 1 binderArity 0
      (parserFixedNumeralTerm 1) (shortBinaryNumeralTerm binderArity)
      (parserFixedNumeralTerm 0) (termValue_parserFixedNumeralTerm · 1)
      (termValue_shortBinaryNumeralTerm · binderArity)
      (termValue_parserFixedNumeralTerm · 0) headData
  let tailCertificate :=
    compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary tailRows
  let headTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      headCertificate tailCertificate
  let parts :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      countCertificate headTailCertificate
  have hsourceCountValue : sourceCount <= numericBound := by omega
  have hsourceCountSuccessor : sourceCount + 1 <= numericBound := by
    rw [← hcount]
    exact htargetCountValue
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidthValue).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCountValue).trans hnumericSize
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCountValue).trans hnumericSize
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCountValue).trans hnumericSize
  have hcountPayload :
      hybridFormulaStructuralPayloadBound countCertificate <=
        taskConsCountFullyFixedPayloadPolynomial bitBound := by
    exact
      (consCountEqualityCertificate_structuralPayloadBound_le_public
        sourceCount targetCount hcount).trans
      (taskConsCountPayloadPolynomial_le_fullyFixed sourceCount targetCount
        bitBound hsourceCountSize htargetCountSize)
  have hheadPayload :
      hybridFormulaStructuralPayloadBound headCertificate <=
        taskConsParserHeadInstalledPayloadEnvelope numericBound bitBound := by
    simpa only [headCertificate] using
      (taskConsParserHeadCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary binderArity numericBound
        bitBound hwidthValue htokenCountValue htableSize hwidthSize
        htokenCountSize htargetBoundarySize hbinderSize headData)
  have htailPayload :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    have htransparent :=
      compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate_structuralPayloadBound_le_transparent
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        tailRows
    have hfixed :=
      compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound tailRows hwidthValue htokenCountValue
        hsourceCountSuccessor htableSize hsourceBoundarySize
        htargetBoundarySize hnumericSize
    simpa only [tailCertificate] using htransparent.trans hfixed
  have hheadTail :=
    transparentHybridConjunctionPayloadBound_le headCertificate
      tailCertificate _ _ hheadPayload htailPayload
  have hparts :=
    transparentHybridConjunctionPayloadBound_le countCertificate
      headTailCertificate _ _ hcountPayload hheadTail
  have hclosed :
      (countFormula ⋏ (headFormula ⋏ tailFormula)).freeVariables = ∅ := by
    have hcountClosed : countFormula.freeVariables = ∅ := by
      exact taskConsCountFormula_freeVariables_eq_empty sourceCount targetCount
    have hheadClosed : headFormula.freeVariables = ∅ := by
      exact taskConsParserHeadBody_freeVariables_eq_empty tokenTable width
        tokenCount targetBoundary binderArity
    have htailClosed : tailFormula.freeVariables = ∅ := by
      have hraw :=
        compactAdditiveSyntaxTaskListConsRowsTailOuterFormula_freeVariables_eq_empty_fixed
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      have halign :
          (∀⁰ termBoundedUniversalBody
            (Rew.bShift (shortBinaryNumeralTerm sourceCount))
            (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
              tokenCount sourceBoundary targetBoundary)) =
          (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
            tokenCount sourceBoundary targetBoundary).ballLT
              (shortBinaryNumeralTerm sourceCount) := by
        rw [termBoundedUniversal_eq_ball]
        rfl
      dsimp only [tailFormula]
      rw [← halign]
      exact hraw
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
      hheadClosed, htailClosed, Finset.union_empty]
  have hcountCode :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      countCertificate).trans hcountPayload
  have hheadCode :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      headCertificate).trans hheadPayload
  have htailCode :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      tailCertificate).trans htailPayload
  change (binaryFormulaCode countFormula).length <=
    taskConsCountFullyFixedPayloadPolynomial bitBound at hcountCode
  change (binaryFormulaCode headFormula).length <=
    taskConsParserHeadInstalledPayloadEnvelope numericBound bitBound at hheadCode
  change (binaryFormulaCode tailFormula).length <=
    taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound bitBound
      at htailCode
  have hcode :
      (binaryFormulaCode
        (countFormula ⋏ (headFormula ⋏ tailFormula))).length <=
          taskConsParserAssemblySyntaxEnvelope numericBound bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold taskConsParserAssemblySyntaxEnvelope
    omega
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      parserConsZeroValuation countFormula headFormula tailFormula
      (taskConsCountFullyFixedPayloadPolynomial bitBound)
      (taskConsParserHeadInstalledPayloadEnvelope numericBound bitBound)
      (taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
        bitBound)
      (taskConsParserAssemblySyntaxEnvelope numericBound bitBound)
      (by unfold taskConsParserAssemblySyntaxEnvelope; omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount (parserFixedNumeralTerm 1)
          (shortBinaryNumeralTerm binderArity)
          (parserFixedNumeralTerm 0)).symm parts) <= _
  unfold taskConsParserFullyFixedPayloadEnvelope
  exact hparts.trans hassembly

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsParserFullyFixedBounds
