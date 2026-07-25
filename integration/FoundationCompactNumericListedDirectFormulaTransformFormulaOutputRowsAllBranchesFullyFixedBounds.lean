import integration.FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsSameFourBranchFullyFixedBounds

/-!
# Uniform fully fixed bound for every formula-output-row branch

All seven constructors of the checked branch data are reduced to independently
verified fixed endpoints.  No branch-dependent graph envelope remains in the
result.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 240000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAllBranchesFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformOutputPrimitives
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRows
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsMappedRowsFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchAssemblyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsRawBranchesFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsZeroBranchFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsSameFourBranchFullyFixedBounds

def outputRowsAllBranchesFullyFixedPayloadPolynomial
    (currentOutputCount numericBound bitBound : Nat) : Nat :=
  outputRowsZeroBranchFixedPayloadPolynomial numericBound bitBound +
    outputRowsRawBranchFixedPayloadPolynomial numericBound bitBound +
    outputRowsSameFourBranchFixedPayloadPolynomial numericBound bitBound +
    outputRowsMappedSelectedFixedPayloadPolynomial currentOutputCount
      numericBound bitBound

theorem
    compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode tag consumedCount mappedHead numericBound bitBound : Nat)
    (data : CompactFormulaTransformFormulaOutputRowsCheckedBranchData
      tokenTable width tokenCount current next mode tag consumedCount mappedHead)
    (henvironmentSize : ∀ coordinate,
      Nat.size
        (compactFormulaTransformFormulaOutputRowsEnvironment tokenTable width
          tokenCount current next mode tag consumedCount mappedHead
          coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hcurrentOutputCountBound : current.outputCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead data) <=
      outputRowsAllBranchesFullyFixedPayloadPolynomial current.outputCount
        numericBound bitBound := by
  have htableSize : Nat.size tokenTable <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (0 : Fin 29)
  have hwidthSize : Nat.size width <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (1 : Fin 29)
  have htokenCountSize : Nat.size tokenCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (2 : Fin 29)
  have hcurrentStartSize : Nat.size current.start <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (3 : Fin 29)
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (4 : Fin 29)
  have hcurrentParserFinishSize :
      Nat.size current.parserFinish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (5 : Fin 29)
  have hcurrentParserTokensFinishSize :
      Nat.size current.parserTokensFinish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (6 : Fin 29)
  have hcurrentParserTokensCountSize :
      Nat.size current.parserTokensCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (9 : Fin 29)
  have hcurrentOutputCountSize :
      Nat.size current.outputCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (13 : Fin 29)
  have hnextFinishSize : Nat.size next.finish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (15 : Fin 29)
  have hnextParserFinishSize :
      Nat.size next.parserFinish <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (16 : Fin 29)
  have hnextOutputBoundarySize :
      Nat.size next.outputBoundary <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (23 : Fin 29)
  have hnextOutputCountSize : Nat.size next.outputCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (24 : Fin 29)
  have htagSize : Nat.size tag <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (26 : Fin 29)
  have hconsumedCountSize : Nat.size consumedCount <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (27 : Fin 29)
  have hmappedHeadSize : Nat.size mappedHead <= bitBound := by
    simpa [compactFormulaTransformFormulaOutputRowsEnvironment] using
      henvironmentSize (28 : Fin 29)
  cases data with
  | zero hcount hconsumed hsame =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsZeroBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hsame
          henvironmentSize hwidthBound htokenCountBound
          hcurrentOutputCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)
  | rawZero hcount hconsumed hmode hsource =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsRawZeroBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hmode hsource
          henvironmentSize hwidthBound htokenCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)
  | rawOne hcount hconsumed hmode hsource =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsRawOneBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hmode hsource
          henvironmentSize hwidthBound htokenCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)
  | rawTwo hcount hconsumed hmode hsource =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsRawTwoBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hmode hsource
          henvironmentSize hwidthBound htokenCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)
  | rawFive hcount hconsumed hmode hsource =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsRawFiveBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hmode hsource
          henvironmentSize hwidthBound htokenCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)
  | sameFour hcount hconsumed hmode hsame =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsSameFourBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hmode hsame
          henvironmentSize hwidthBound htokenCountBound
          hcurrentOutputCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)
  | mapped hcount hconsumed hmodeZero hmodeOne hmodeTwo hmodeFour hmodeFive
      htag hrows =>
      have hbranch :=
        compactFormulaTransformFormulaOutputRowsMappedBranchCertificate_structuralPayloadBound_le_fullyFixed
          tokenTable width tokenCount current next mode tag consumedCount
          mappedHead numericBound bitBound hcount hconsumed hmodeZero hmodeOne
          hmodeTwo hmodeFour hmodeFive htag hrows henvironmentSize htableSize
          hwidthSize htokenCountSize hcurrentParserFinishSize
          hcurrentFinishSize hcurrentOutputCountSize hcurrentStartSize
          hcurrentParserTokensFinishSize hcurrentParserTokensCountSize
          hconsumedCountSize hnextParserFinishSize hnextFinishSize
          hnextOutputBoundarySize hnextOutputCountSize htagSize hmappedHeadSize
          hwidthBound htokenCountBound hnumericSize
      exact hbranch.trans (by
        unfold outputRowsAllBranchesFullyFixedPayloadPolynomial
        omega)

#print axioms
  compactFormulaTransformFormulaOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformFormulaOutputRowsAllBranchesFullyFixedBounds
