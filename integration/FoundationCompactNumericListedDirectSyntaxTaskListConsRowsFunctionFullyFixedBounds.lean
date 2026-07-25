import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionHeadInstalledFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalFullyFixedBounds
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds

/-!
# Fully fixed function cons-rows certificate

The genuine count, function-head, and shifted-tail certificates are rebuilt
and assembled in their original right-associated three-leaf formula.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds

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
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionHeadInstalledFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalBodyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsTailUniversalFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate

private abbrev functionConsZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

@[simp] private theorem termValue_fixedNumeralTerm_functionCons
    (valuation : Nat -> Nat) (value : Nat) :
    termValue valuation (fixedNumeralTerm value) = value := by
  simp [fixedNumeralTerm, termValue]

def taskConsFunctionAssemblySyntaxEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  taskConsCountFullyFixedPayloadPolynomial bitBound +
    taskConsFunctionHeadInstalledPayloadEnvelope tokenCount numericBound
      bitBound +
    taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound bitBound +
    2 * (binaryNatCode 4).length + 1

def taskConsFunctionFullyFixedPayloadEnvelope
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (taskConsFunctionAssemblySyntaxEnvelope tokenCount numericBound bitBound)
    (taskConsCountFullyFixedPayloadPolynomial bitBound)
    (taskConsFunctionHeadInstalledPayloadEnvelope tokenCount numericBound
      bitBound)
    (taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound bitBound)

theorem taskConsFunctionFormula_freeVariables_eq_empty
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity functionArity : Nat) :
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula tokenTable
      width tokenCount sourceBoundary sourceCount targetBoundary targetCount
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)).freeVariables = ∅ := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
  let tailFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  have hcountClosed : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    exact taskConsCountFormula_freeVariables_eq_empty sourceCount targetCount
  have hheadClosed : headFormula.freeVariables = ∅ := by
    dsimp only [headFormula]
    exact taskConsFunctionHeadBody_freeVariables_eq_empty tokenTable width
      tokenCount targetBoundary binderArity functionArity
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
    taskConsFunctionCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount binderArity functionArity numericBound bitBound : Nat)
    (hwidthValue : width <= numericBound)
    (htokenCountValue : tokenCount <= numericBound)
    (htargetCountValue : targetCount <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hbinderSize : Nat.size binderArity <= bitBound)
    (hfunctionSize : Nat.size functionArity <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary 2 binderArity functionArity)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataExplicitHybridCertificate
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount 2 binderArity functionArity (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)
          (termValue_fixedNumeralTerm_functionCons · 2)
          (termValue_shortBinaryNumeralTerm · binderArity)
          (termValue_shortBinaryNumeralTerm · functionArity)
          hcount headData tailRows) <=
      taskConsFunctionFullyFixedPayloadEnvelope tokenCount numericBound
        bitBound := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary (fixedNumeralTerm 2)
      (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
  let tailFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let countCertificate :=
    FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.countEqualityCertificate
      sourceCount targetCount hcount
  let headCertificate :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsHeadCertificate
      tokenTable width tokenCount targetBoundary 2 binderArity functionArity
      (fixedNumeralTerm 2) (shortBinaryNumeralTerm binderArity)
      (shortBinaryNumeralTerm functionArity)
      (termValue_fixedNumeralTerm_functionCons · 2)
      (termValue_shortBinaryNumeralTerm · binderArity)
      (termValue_shortBinaryNumeralTerm · functionArity) headData
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
  have hcountPublic :=
    consCountEqualityCertificate_structuralPayloadBound_le_public
      sourceCount targetCount hcount
  have hcountFixed :=
    taskConsCountPayloadPolynomial_le_fullyFixed sourceCount targetCount
      bitBound hsourceCountSize htargetCountSize
  have hcountPayload :
      hybridFormulaStructuralPayloadBound countCertificate <=
        taskConsCountFullyFixedPayloadPolynomial bitBound := by
    simpa only [countCertificate] using hcountPublic.trans hcountFixed
  have hheadPayload :
      hybridFormulaStructuralPayloadBound headCertificate <=
        taskConsFunctionHeadInstalledPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [headCertificate] using
      (taskConsFunctionHeadCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount targetBoundary binderArity functionArity
        numericBound bitBound hwidthValue htokenCountValue htableSize
        hwidthSize htokenCountSize htargetBoundarySize hbinderSize
        hfunctionSize headData)
  have htailTransparent :=
    compactAdditiveSyntaxTaskListConsRowsTailUniversalCertificate_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      tailRows
  have htailFixed :=
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      numericBound bitBound tailRows hwidthValue htokenCountValue
      hsourceCountSuccessor htableSize hsourceBoundarySize
      htargetBoundarySize hnumericSize
  have htailPayload :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tailCertificate] using htailTransparent.trans htailFixed
  have hheadTail :=
    transparentHybridConjunctionPayloadBound_le headCertificate
      tailCertificate _ _ hheadPayload htailPayload
  have hparts :=
    transparentHybridConjunctionPayloadBound_le countCertificate
      headTailCertificate _ _ hcountPayload hheadTail
  have hcountClosed : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    exact taskConsCountFormula_freeVariables_eq_empty sourceCount targetCount
  have hheadClosed : headFormula.freeVariables = ∅ := by
    dsimp only [headFormula]
    exact taskConsFunctionHeadBody_freeVariables_eq_empty tokenTable width
      tokenCount targetBoundary binderArity functionArity
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
  have hclosed :
      (countFormula ⋏ (headFormula ⋏ tailFormula)).freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
      hheadClosed, htailClosed, Finset.union_empty]
  have hcountCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      countCertificate
  have hheadCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      headCertificate
  have htailCodeRaw :=
    CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      tailCertificate
  have hcountCode :
      (binaryFormulaCode countFormula).length <=
        taskConsCountFullyFixedPayloadPolynomial bitBound := by
    simpa only [countCertificate, countFormula] using
      hcountCodeRaw.trans hcountPayload
  have hheadCode :
      (binaryFormulaCode headFormula).length <=
        taskConsFunctionHeadInstalledPayloadEnvelope tokenCount numericBound
          bitBound := by
    simpa only [headCertificate, headFormula] using
      hheadCodeRaw.trans hheadPayload
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tailCertificate, tailFormula] using
      htailCodeRaw.trans htailPayload
  have hinnerCode :=
    binaryFormulaCode_and_length_le_local headFormula tailFormula
  have htotalCodeRaw :=
    binaryFormulaCode_and_length_le_local countFormula
      (headFormula ⋏ tailFormula)
  have hcode :
      (binaryFormulaCode
        (countFormula ⋏ (headFormula ⋏ tailFormula))).length <=
          taskConsFunctionAssemblySyntaxEnvelope tokenCount numericBound
            bitBound := by
    unfold taskConsFunctionAssemblySyntaxEnvelope
    omega
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      functionConsZeroValuation countFormula headFormula tailFormula
      (taskConsCountFullyFixedPayloadPolynomial bitBound)
      (taskConsFunctionHeadInstalledPayloadEnvelope tokenCount numericBound
        bitBound)
      (taskConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
        bitBound)
      (taskConsFunctionAssemblySyntaxEnvelope tokenCount numericBound
        bitBound)
      (by
        unfold taskConsFunctionAssemblySyntaxEnvelope
        omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFormula_alignment
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount (fixedNumeralTerm 2)
          (shortBinaryNumeralTerm binderArity)
          (shortBinaryNumeralTerm functionArity)).symm parts) <= _
  unfold taskConsFunctionFullyFixedPayloadEnvelope
  simpa only [hybridFormulaStructuralPayloadBound, countFormula, headFormula,
    tailFormula, countCertificate, headCertificate, tailCertificate,
    headTailCertificate, parts, functionConsZeroValuation] using
      hparts.trans hassembly

#print axioms
  taskConsFunctionFormula_freeVariables_eq_empty
#print axioms
  taskConsFunctionCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsFunctionFullyFixedBounds
