import integration.FoundationCompactNumericListedDirectBinaryNatDefaultStatusDirectSyntax

/-! Direct compilation of the completed default branch with a nonempty suffix. -/

open LO FirstOrder LO.FirstOrder.Arithmetic
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 700000
namespace FoundationCompactNumericListedDirectBinaryNatDefaultCompletedDirectCompiler
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPADirectConnectiveTransparentBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactCertifiedContextProof
open FoundationCompactNumericListedDirectBinaryNatStatusValidity
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectBinaryNatCompletedStatusUniformDirectCompiler
open FoundationCompactNumericListedDirectBinaryNatDefaultStatusDirectSyntax

def defaultCompletedPayloadEnvelope (tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound : Nat) : Nat :=
  transparentHybridConjunctionPayloadEnvelope zeroValuation
    (compactBinaryNatCompletedStatusUniformDirectFormula tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount)
    “0 < !!(shortBinaryNumeralTerm outputCount)”
    (compactBinaryNatCompletedStatusUniformDirectPayloadEnvelope tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound)
    (closedLtStructuralPayloadPolynomial 0 outputCount)

def compileDefaultCompleted
    (tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
      (compactBinaryNatStatusValidityWitnessOf
        outputStart outputBoundary outputBoundarySize outputCount))
    (htokenCount : tokenCount ≤ numericBound)
    (houtputCount : outputCount ≤ numericBound)
    (htableSize : Nat.size outputBoundary ≤ bitBound)
    (hnumericSize : Nat.size numericBound ≤ bitBound)
    (hpositive : 0 < outputCount) :
    CertifiedPAContextProof
      (valuationContext
        (compactBinaryNatDefaultCompletedClosedFormula tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount).freeVariables
        zeroValuation)
      (compactBinaryNatDefaultCompletedClosedFormula tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount) := by
  exact compileDirectConjunction
    (compileCompactBinaryNatCompletedStatusUniformDirect tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound hcompleted htokenCount houtputCount htableSize hnumericSize)
    (closedLtCertificate 0 outputCount hpositive).compile

theorem compileDefaultCompleted_payloadLength_le
    (tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound : Nat)
    (hcompleted : CompactBinaryNatCompletedStatusValidRows
      tokenTable width tokenCount start finish
      (compactBinaryNatStatusValidityWitnessOf
        outputStart outputBoundary outputBoundarySize outputCount))
    (htokenCount : tokenCount ≤ numericBound)
    (houtputCount : outputCount ≤ numericBound)
    (htableSize : Nat.size outputBoundary ≤ bitBound)
    (hnumericSize : Nat.size numericBound ≤ bitBound)
    (hpositive : 0 < outputCount) :
    (compileDefaultCompleted tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound hcompleted htokenCount houtputCount htableSize hnumericSize hpositive).payloadLength ≤
      defaultCompletedPayloadEnvelope tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound := by
  have hcompletedBound :=
    compileCompactBinaryNatCompletedStatusUniformDirect_payloadLength_le
      tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound hcompleted htokenCount houtputCount htableSize hnumericSize
  have hpositiveBound :=
    (compile_payloadLength_le_structuralPayloadBound
      (closedLtCertificate 0 outputCount hpositive)).trans
      (closedLtCertificate_structuralPayloadBound_le_public 0 outputCount hpositive)
  exact compileDirectConjunction_payloadLength_le
    (compileCompactBinaryNatCompletedStatusUniformDirect tokenTable width tokenCount start finish outputStart outputBoundary outputBoundarySize outputCount numericBound bitBound hcompleted htokenCount houtputCount htableSize hnumericSize)
    (closedLtCertificate 0 outputCount hpositive).compile
    _ _ hcompletedBound hpositiveBound

#print axioms compileDefaultCompleted
#print axioms compileDefaultCompleted_payloadLength_le
end FoundationCompactNumericListedDirectBinaryNatDefaultCompletedDirectCompiler
