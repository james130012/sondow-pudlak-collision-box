import integration.FoundationCompactNumericListedDirectParserDoneWholeUniformDirectCompiler

/-! # Alignment of the direct Done proof with the original graph formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserDoneFormula
open FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserDoneWholeUniformDirectCompiler

private abbrev doneAlignedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserDoneExplicitHybridCertificate.zeroValuation

noncomputable def compileCompactUnifiedParserDoneUniformDirectOriginalContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.outputCount <= numericBound)
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
          current next witness).freeVariables doneAlignedZeroValuation)
      (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
        current next witness) := by
  let raw :=
    compileCompactUnifiedParserDoneUniformDirectExplicitContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize
  have hformula :
      compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
          current next witness =
        compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
          current next witness :=
    (compactUnifiedParserDoneClosedFormula_alignment tokenTable width
      tokenCount current next witness).symm
  let formulaCast := CertifiedPAContextProof.cast hformula raw
  have hcontext :
      valuationContext
          (compactUnifiedParserDoneExplicitFormula tokenTable width tokenCount
            current next witness).freeVariables doneAlignedZeroValuation =
        valuationContext
          (compactUnifiedParserDoneClosedFormula tokenTable width tokenCount
            current next witness).freeVariables doneAlignedZeroValuation := by
    rw [hformula]
  exact CertifiedPAContextProof.castContext hcontext formulaCast

theorem
    compileCompactUnifiedParserDoneUniformDirectOriginalContext_payloadLength_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserDoneWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserDoneGraphRows tokenTable width tokenCount
      current next witness)
    (htokenCount : tokenCount <= numericBound)
    (houtputCount : witness.outputCount <= numericBound)
    (hsourceBoundarySize :
      Nat.size witness.sourceOutputBoundary <= bitBound)
    (htargetBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactUnifiedParserDoneUniformDirectOriginalContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize).payloadLength =
    (compileCompactUnifiedParserDoneUniformDirectExplicitContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount houtputCount hsourceBoundarySize htargetBoundarySize
      hnumericSize).payloadLength := by
  unfold compileCompactUnifiedParserDoneUniformDirectOriginalContext
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]

end FoundationCompactNumericListedDirectParserDoneWholeUniformDirectAlignment
