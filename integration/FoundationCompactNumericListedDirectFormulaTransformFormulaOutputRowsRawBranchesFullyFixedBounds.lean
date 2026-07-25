import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchAssemblyFixedBounds

/-!
# Fully fixed original raw output-row branches

The four theorems below identify the directly compiled fixed certificates with
the corresponding constructors of the project's original `FromData`
certificate.  Thus the fixed route is not a parallel replacement object.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 220000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchesFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawModeFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchAssemblyFixedBounds

private theorem mode_size_le_of_environment
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead bitBound : Nat)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound) :
    Nat.size mode <= bitBound := by
  simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
    henvironmentSize (25 : Fin 29)

theorem
    compactFormulaTransformFormulaOutputRowsRawZeroBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 0)
    (hsource : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead (.rawZero hcount hconsumed hmode hsource)) <=
      outputRowsRawBranchFixedPayloadPolynomial numericBound bitBound := by
  have hmodeSize := mode_size_le_of_environment tokenTable width tokenCount
    current next mode tag consumedCount mappedHead bitBound henvironmentSize
  have hmodeFixed :=
    rawModeZeroFixedCertificate_structuralPayloadBound_le_fixed mode bitBound
      hmodeSize hmode
  have hfixed :=
    outputRowsRawSelectedFixedCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      numericBound bitBound hcount hconsumed hsource
      (rawModeZeroFixedCertificate mode hmode) hmodeFixed henvironmentSize
      hwidthBound htokenCountBound hnumericSize
  convert hfixed using 1 <;>
    simp only [
      compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData,
      outputRowsRawSelectedFixedCertificate, rawModeZeroFixedCertificate] <;>
    (congr 1 <;> apply proof_irrel_heq)

theorem
    compactFormulaTransformFormulaOutputRowsRawOneBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 1)
    (hsource : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead (.rawOne hcount hconsumed hmode hsource)) <=
      outputRowsRawBranchFixedPayloadPolynomial numericBound bitBound := by
  have hmodeSize := mode_size_le_of_environment tokenTable width tokenCount
    current next mode tag consumedCount mappedHead bitBound henvironmentSize
  have hmodeFixed :=
    rawModeOneFixedCertificate_structuralPayloadBound_le_fixed mode bitBound
      hmodeSize hmode
  have hfixed :=
    outputRowsRawSelectedFixedCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      numericBound bitBound hcount hconsumed hsource
      (rawModeOneFixedCertificate mode hmode) hmodeFixed henvironmentSize
      hwidthBound htokenCountBound hnumericSize
  convert hfixed using 1 <;>
    simp only [
      compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData,
      outputRowsRawSelectedFixedCertificate, rawModeOneFixedCertificate] <;>
    (congr 1 <;> apply proof_irrel_heq)

theorem
    compactFormulaTransformFormulaOutputRowsRawTwoBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 2)
    (hsource : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead (.rawTwo hcount hconsumed hmode hsource)) <=
      outputRowsRawBranchFixedPayloadPolynomial numericBound bitBound := by
  have hmodeSize := mode_size_le_of_environment tokenTable width tokenCount
    current next mode tag consumedCount mappedHead bitBound henvironmentSize
  have hmodeFixed :=
    rawModeTwoFixedCertificate_structuralPayloadBound_le_fixed mode bitBound
      hmodeSize hmode
  have hfixed :=
    outputRowsRawSelectedFixedCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      numericBound bitBound hcount hconsumed hsource
      (rawModeTwoFixedCertificate mode hmode) hmodeFixed henvironmentSize
      hwidthBound htokenCountBound hnumericSize
  convert hfixed using 1 <;>
    simp only [
      compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData,
      outputRowsRawSelectedFixedCertificate, rawModeTwoFixedCertificate] <;>
    (congr 1 <;> apply proof_irrel_heq)

theorem
    compactFormulaTransformFormulaOutputRowsRawFiveBranchCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (hcount : current.parserTokensCount =
      consumedCount + next.parserTokensCount)
    (hconsumed : 1 <= consumedCount)
    (hmode : mode = 5)
    (hsource : CompactFormulaTransformOutputRawPrefixRows tokenTable width
      tokenCount current next consumedCount)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead (.rawFive hcount hconsumed hmode hsource)) <=
      outputRowsRawBranchFixedPayloadPolynomial numericBound bitBound := by
  have hmodeSize := mode_size_le_of_environment tokenTable width tokenCount
    current next mode tag consumedCount mappedHead bitBound henvironmentSize
  have hmodeFixed :=
    rawModeFiveFixedCertificate_structuralPayloadBound_le_fixed mode bitBound
      hmodeSize hmode
  have hfixed :=
    outputRowsRawSelectedFixedCertificate_structuralPayloadBound_le_fixed
      tokenTable width tokenCount current next mode tag consumedCount mappedHead
      numericBound bitBound hcount hconsumed hsource
      (rawModeFiveFixedCertificate mode hmode) hmodeFixed henvironmentSize
      hwidthBound htokenCountBound hnumericSize
  simpa only [
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData,
    outputRowsRawSelectedFixedCertificate, rawModeFiveFixedCertificate] using
    hfixed

#print axioms
  compactFormulaTransformFormulaOutputRowsRawZeroBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  compactFormulaTransformFormulaOutputRowsRawOneBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  compactFormulaTransformFormulaOutputRowsRawTwoBranchCertificate_structuralPayloadBound_le_fullyFixed
#print axioms
  compactFormulaTransformFormulaOutputRowsRawFiveBranchCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchesFullyFixedBounds
