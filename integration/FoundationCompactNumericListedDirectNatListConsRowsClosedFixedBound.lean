import integration.FoundationCompactNumericListedDirectNatListConsRowsClosedCertificate
import integration.FoundationCompactNumericListedDirectNatListConsRowsClosedFormulaClosed
import integration.FoundationCompactNumericListedDirectNatListConsRowsHeadUniformBound
import integration.FoundationCompactNumericListedDirectNatListConsRowsTailUniversalFixedBound
import integration.FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed payload bound for the closed natural-list cons-rows formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 260000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListConsRowsClosedFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListConsRowsClosedCertificate
open FoundationCompactNumericListedDirectNatListConsRowsClosedFormulaClosed
open FoundationCompactNumericListedDirectNatListConsRowsCountCertificateFixedBound
open FoundationCompactNumericListedDirectNatListConsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadBodyClosed
open FoundationCompactNumericListedDirectNatListConsRowsHeadCertificate
open FoundationCompactNumericListedDirectNatListConsRowsHeadFixedEnvelope
open FoundationCompactNumericListedDirectNatListConsRowsHeadUniformBound
open FoundationCompactNumericListedDirectNatListConsRowsTailOuterFormulaClosed
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalCertificate
open FoundationCompactNumericListedDirectNatListConsRowsTailUniversalFixedBound
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsCountFullyFixedBounds

def natListConsRowsClosedAssemblySyntaxPolynomial
    (numericBound bitBound : Nat) : Nat :=
  taskConsCountFullyFixedPayloadPolynomial bitBound +
    natListConsHeadInstalledPayloadPolynomial numericBound bitBound +
    natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
      bitBound +
    2 * (binaryNatCode 4).length + 1

def natListConsRowsClosedFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridThreeConjunctionGeneralPayloadEnvelope
    (natListConsRowsClosedAssemblySyntaxPolynomial numericBound bitBound)
    (taskConsCountFullyFixedPayloadPolynomial bitBound)
    (natListConsHeadInstalledPayloadPolynomial numericBound bitBound)
    (natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
      bitBound)

theorem compactAdditiveNatListConsRowsClosedCertificate_payload_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount head numericBound bitBound : Nat)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htargetCount : targetCount <= numericBound)
    (hhead : head <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hcount : targetCount = sourceCount + 1)
    (headData : CompactAdditiveNatListConsHeadData tokenTable width tokenCount
      targetBoundary head)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveNatListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListConsRowsClosedCertificate tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary targetCount
          head hcount headData tailRows) <=
      natListConsRowsClosedFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula := compactAdditiveNatListConsRowsHeadBody tokenTable width
    tokenCount targetBoundary head
  let tailFormula : ValuationFormula :=
    (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let countCertificate := natListConsRowsCountEqualityCertificate sourceCount
    targetCount hcount
  let headCertificate := compactAdditiveNatListConsRowsHeadCertificate
    tokenTable width tokenCount targetBoundary head headData
  let tailCertificate := compactAdditiveNatListConsRowsTailUniversalCertificate
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    tailRows
  let headTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      headCertificate tailCertificate
  let parts := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate headTailCertificate
  have hsourceCount : sourceCount <= numericBound := by omega
  have hsourceCountSuccessor : sourceCount + 1 <= numericBound := by
    rw [← hcount]
    exact htargetCount
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hsourceCountSize : Nat.size sourceCount <= bitBound :=
    (Nat.size_le_size hsourceCount).trans hnumericSize
  have htargetCountSize : Nat.size targetCount <= bitBound :=
    (Nat.size_le_size htargetCount).trans hnumericSize
  have hheadSize : Nat.size head <= bitBound :=
    (Nat.size_le_size hhead).trans hnumericSize
  have hcountPayload :
      hybridFormulaStructuralPayloadBound countCertificate <=
        taskConsCountFullyFixedPayloadPolynomial bitBound := by
    dsimp only [countCertificate]
    exact natListConsRowsCountEqualityCertificate_payload_le_fullyFixed
      sourceCount targetCount bitBound hcount hsourceCountSize
      htargetCountSize
  have hheadPayload :
      hybridFormulaStructuralPayloadBound headCertificate <=
        natListConsHeadInstalledPayloadPolynomial numericBound bitBound := by
    dsimp only [headCertificate]
    exact compactAdditiveNatListConsRowsHeadCertificate_payloadLength_le_uniform
      tokenTable width tokenCount targetBoundary head numericBound bitBound
      hwidth htokenCount htokenTableSize hwidthSize htokenCountSize
      htargetBoundarySize hheadSize headData
  have htailPayload :
      hybridFormulaStructuralPayloadBound tailCertificate <=
        natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    dsimp only [tailCertificate]
    exact
      compactAdditiveNatListConsRowsTailUniversalCertificate_payload_le_fullyFixed
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        numericBound bitBound tailRows hwidth htokenCount
        hsourceCountSuccessor htokenTableSize hsourceBoundarySize
        htargetBoundarySize hnumericSize
  have hheadTail := transparentHybridConjunctionPayloadBound_le
    headCertificate tailCertificate _ _ hheadPayload htailPayload
  have hparts := transparentHybridConjunctionPayloadBound_le
    countCertificate headTailCertificate _ _ hcountPayload hheadTail
  have hcountClosed : countFormula.freeVariables = ∅ := by
    dsimp only [countFormula]
    exact taskConsCountFormula_freeVariables_eq_empty sourceCount targetCount
  have hheadClosed : headFormula.freeVariables = ∅ := by
    dsimp only [headFormula]
    exact compactAdditiveNatListConsRowsHeadBody_freeVariables_eq_empty
      tokenTable width tokenCount targetBoundary head
  have htailClosed : tailFormula.freeVariables = ∅ := by
    have hraw :=
      compactAdditiveNatListConsRowsTailOuterFormula_freeVariables_eq_empty
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
    have halign :
        (∀⁰ termBoundedUniversalBody
          (Rew.bShift (shortBinaryNumeralTerm sourceCount))
          (compactAdditiveNatListConsRowsTailBody tokenTable width tokenCount
            sourceBoundary targetBoundary)) = tailFormula := by
      dsimp only [tailFormula]
      rw [FoundationCompactPAValuationBoundedFormulaCompiler.termBoundedUniversal_eq_ball]
      rfl
    rw [← halign]
    exact hraw
  have hclosed :
      (countFormula ⋏ (headFormula ⋏ tailFormula)).freeVariables = ∅ := by
    simp only [LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
      hheadClosed, htailClosed, Finset.union_empty]
  have hcountCodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      countCertificate
  have hheadCodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      headCertificate
  have htailCodeRaw :=
    FoundationCompactCertifiedContextProofConclusionCodeBounds.CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      tailCertificate
  have hcountCode :
      (binaryFormulaCode countFormula).length <=
        taskConsCountFullyFixedPayloadPolynomial bitBound := by
    simpa only [countCertificate, countFormula] using
      hcountCodeRaw.trans hcountPayload
  have hheadCode :
      (binaryFormulaCode headFormula).length <=
        natListConsHeadInstalledPayloadPolynomial numericBound bitBound := by
    simpa only [headCertificate, headFormula] using
      hheadCodeRaw.trans hheadPayload
  have htailCode :
      (binaryFormulaCode tailFormula).length <=
        natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
          bitBound := by
    simpa only [tailCertificate, tailFormula] using
      htailCodeRaw.trans htailPayload
  have hinnerCode := binaryFormulaCode_and_length_le_local headFormula
    tailFormula
  have htotalCode := binaryFormulaCode_and_length_le_local countFormula
    (headFormula ⋏ tailFormula)
  have hcode :
      (binaryFormulaCode
        (countFormula ⋏ (headFormula ⋏ tailFormula))).length <=
          natListConsRowsClosedAssemblySyntaxPolynomial numericBound
            bitBound := by
    unfold natListConsRowsClosedAssemblySyntaxPolynomial
    omega
  have hassembly :=
    transparentHybridThreeConjunctionPayloadEnvelope_le_closedGeneral
      natListConsRowsTailUniversalZeroValuation countFormula headFormula
      tailFormula
      (taskConsCountFullyFixedPayloadPolynomial bitBound)
      (natListConsHeadInstalledPayloadPolynomial numericBound bitBound)
      (natListConsRowsTailUniversalFullyFixedPayloadPolynomial numericBound
        bitBound)
      (natListConsRowsClosedAssemblySyntaxPolynomial numericBound bitBound)
      (by
        unfold natListConsRowsClosedAssemblySyntaxPolynomial
        omega)
      hclosed hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactAdditiveNatListConsRowsClosedFormula_alignment tokenTable width
          tokenCount sourceBoundary sourceCount targetBoundary targetCount
          head).symm parts) <= _
  unfold natListConsRowsClosedFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, countFormula, headFormula,
    tailFormula, countCertificate, headCertificate, tailCertificate,
    headTailCertificate, parts] using hparts.trans hassembly

#print axioms
  compactAdditiveNatListConsRowsClosedCertificate_payload_le_fullyFixed

end FoundationCompactNumericListedDirectNatListConsRowsClosedFixedBound
