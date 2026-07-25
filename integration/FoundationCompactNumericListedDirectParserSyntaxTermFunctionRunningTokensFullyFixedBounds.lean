import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates
import integration.FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
import integration.FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds

/-!
# Fixed running and drop-three branches for function syntax terms
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 400000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxTermFunctionRunningTokensFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectAdditiveCodecGraph
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
open FoundationCompactNumericListedDirectNatListDropThreeRowsFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionBranchCertificates

theorem syntaxTermFunctionRunningCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount tasksFinish finish numericBound bitBound :
      Nat)
    (hrunning : CompactBinaryNatRunningStatusSlice tokenTable width tokenCount
      tasksFinish finish)
    (hwidth : width <= numericBound)
    (htasksFinish : tasksFinish <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (htasksFinishSize : Nat.size tasksFinish <= bitBound)
    (hfinishSize : Nat.size finish <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFunctionRunningCertificate tokenTable width tokenCount
          tasksFinish finish hrunning) <=
      compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound := by
  simpa only [syntaxTermFunctionRunningCertificate] using
    (compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
      tokenTable width tokenCount tasksFinish finish numericBound bitBound
      hwidth htasksFinish htokenTableSize hwidthSize htokenCountSize
      htasksFinishSize hfinishSize hrunning)

theorem syntaxTermFunctionTokensCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound : Nat)
    (htokens : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount 3)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hsourceCount : sourceCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hsourceBoundarySize : Nat.size sourceBoundary <= bitBound)
    (htargetBoundarySize : Nat.size targetBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermFunctionTokensCertificate tokenTable width tokenCount
          sourceBoundary sourceCount targetBoundary targetCount htokens) <=
      dropThreeRowsCompleteFullyFixedPayloadPolynomial numericBound
        bitBound := by
  have htransparent :=
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount 3 htokens
  have hfixed :=
    compactAdditiveNatListDropThreeRowsGraphPayloadEnvelope_le_fullyFixed
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount numericBound bitBound htokens hwidth htokenCount
      hsourceCount htokenTableSize hsourceBoundarySize htargetBoundarySize
      hnumericSize
  simpa only [syntaxTermFunctionTokensCertificate] using
    htransparent.trans hfixed

#print axioms
  syntaxTermFunctionRunningCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  syntaxTermFunctionTokensCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermFunctionRunningTokensFullyFixedBounds
