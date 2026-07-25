import integration.FoundationCompactNumericListedDirectParserEmptyUniformDirectCompiler

/-! # Alignment of the uniform direct empty proof with the original graph formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment

open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserEmptyFormula
open FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserEmptyUniformDirectCompiler

private abbrev emptyAlignedZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserEmptyExplicitHybridCertificate.zeroValuation

noncomputable def compileCompactUnifiedParserEmptyUniformDirectOriginalContext
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentTokensCount : current.tokensCount <= numericBound)
    (houtputBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    CertifiedPAContextProof
      (valuationContext
        (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current next witness).freeVariables emptyAlignedZeroValuation)
      (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
        current next witness) := by
  let raw := compileCompactUnifiedParserEmptyUniformDirectContext tokenTable width
    tokenCount current next witness numericBound bitBound hgraph htokenCount
    hcurrentTokensCount houtputBoundarySize hnumericSize
  have hformula :
      compactUnifiedParserEmptyExplicitFormula tokenTable width tokenCount
          current next witness =
        compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
          current next witness :=
    (compactUnifiedParserEmptyClosedFormula_alignment tokenTable width
      tokenCount current next witness).symm
  let formulaCast := CertifiedPAContextProof.cast hformula raw
  have hcontext :
      valuationContext
          (compactUnifiedParserEmptyExplicitFormula tokenTable width tokenCount
            current next witness).freeVariables emptyAlignedZeroValuation =
        valuationContext
          (compactUnifiedParserEmptyClosedFormula tokenTable width tokenCount
            current next witness).freeVariables emptyAlignedZeroValuation := by
    rw [hformula]
  exact CertifiedPAContextProof.castContext hcontext formulaCast

theorem
    compileCompactUnifiedParserEmptyUniformDirectOriginalContext_payloadLength_eq
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactUnifiedParserEmptyWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserEmptyGraphRows
      tokenTable width tokenCount current next witness)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentTokensCount : current.tokensCount <= numericBound)
    (houtputBoundarySize :
      Nat.size witness.targetOutputBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    (compileCompactUnifiedParserEmptyUniformDirectOriginalContext tokenTable
      width tokenCount current next witness numericBound bitBound hgraph
      htokenCount hcurrentTokensCount houtputBoundarySize
      hnumericSize).payloadLength =
    (compileCompactUnifiedParserEmptyUniformDirectContext tokenTable width
      tokenCount current next witness numericBound bitBound hgraph htokenCount
      hcurrentTokensCount houtputBoundarySize hnumericSize).payloadLength := by
  unfold compileCompactUnifiedParserEmptyUniformDirectOriginalContext
  rw [CertifiedPAContextProof.castContext_payloadLength,
    CertifiedPAContextProof.cast_payloadLength]

end FoundationCompactNumericListedDirectParserEmptyUniformDirectAlignment
