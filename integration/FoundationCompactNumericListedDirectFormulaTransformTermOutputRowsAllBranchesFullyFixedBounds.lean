import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroLowerFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroShiftedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroRawFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneShiftedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneRawFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoLowerFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoRawFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourOneFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourSameFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveCapturedFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveResidualFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveRawFullyFixedBounds
import integration.FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOtherFullyFixedBounds

/-! # One fully fixed resource for all fourteen term-output branches -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 240000

namespace FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAllBranchesFullyFixedBounds

open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactNumericListedDirectFormulaTransformStateFormula
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRows
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsZeroFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroLowerFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroShiftedFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeZeroRawFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneShiftedFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeOneRawFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoLowerFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeTwoRawFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourOneFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFourSameFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveCapturedFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveResidualFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsModeFiveRawFullyFixedBounds
open FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsOtherFullyFixedBounds

def termRowsAllBranchesFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  termRowsZeroFixedPayloadPolynomial numericBound bitBound +
  termRowsModeZeroLowerFixedPayloadPolynomial numericBound bitBound +
  termRowsModeZeroShiftedFixedPayloadPolynomial numericBound bitBound +
  termRowsModeZeroRawFixedPayloadPolynomial numericBound bitBound +
  termRowsModeOneShiftedFixedPayloadPolynomial numericBound bitBound +
  termRowsModeOneRawFixedPayloadPolynomial numericBound bitBound +
  termRowsModeTwoLowerFixedPayloadPolynomial numericBound bitBound +
  termRowsModeTwoRawFixedPayloadPolynomial numericBound bitBound +
  termRowsModeFourOneFixedPayloadPolynomial numericBound bitBound +
  termRowsModeFourSameFixedPayloadPolynomial numericBound bitBound +
  termRowsModeFiveCapturedFixedPayloadPolynomial numericBound bitBound +
  termRowsModeFiveResidualFixedPayloadPolynomial numericBound bitBound +
  termRowsModeFiveRawFixedPayloadPolynomial numericBound bitBound +
  termRowsOtherFixedPayloadPolynomial numericBound bitBound

theorem
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (data : CompactFormulaTransformTermOutputRowsCheckedBranchData tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hcurrentOutputCountBound : current.outputCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hwitnessCountBound : witnessCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount data) <=
      termRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  cases data with
  | zero hcount hconsumed hsame =>
      refine (compactFormulaTransformTermOutputRowsZeroBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hsame henvironmentSize hwidthBound htokenCountBound
        hcurrentOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeZeroLower hcount hconsumed hmode hguard hrows =>
      refine (compactFormulaTransformTermOutputRowsModeZeroLowerBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode hguard hrows henvironmentSize hwidthBound htokenCountBound
        hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeZeroShifted hcount hconsumed hmode failure hguard hrows =>
      refine (compactFormulaTransformTermOutputRowsModeZeroShiftedBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode failure hguard hrows henvironmentSize hwidthBound
        htokenCountBound hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeZeroRaw hcount hconsumed hmode lowerFailure shiftFailure hrows =>
      refine (compactFormulaTransformTermOutputRowsModeZeroRawBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode lowerFailure shiftFailure hrows henvironmentSize hwidthBound
        htokenCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeOneShifted hcount hconsumed hmode hguard hrows =>
      refine (compactFormulaTransformTermOutputRowsModeOneShiftedBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode hguard hrows henvironmentSize hwidthBound htokenCountBound
        hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeOneRaw hcount hconsumed hmode failure hrows =>
      refine (compactFormulaTransformTermOutputRowsModeOneRawBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode failure hrows henvironmentSize hwidthBound htokenCountBound
        hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeTwoLower hcount hconsumed hmode hguard hrows =>
      refine (compactFormulaTransformTermOutputRowsModeTwoLowerBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode hguard hrows henvironmentSize hwidthBound htokenCountBound
        hwitnessCountBound hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeTwoRaw hcount hconsumed hmode failure hrows =>
      refine (compactFormulaTransformTermOutputRowsModeTwoRawBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode failure hrows henvironmentSize hwidthBound htokenCountBound
        hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeFourOne hcount hconsumed hmode hguard hrows =>
      refine (compactFormulaTransformTermOutputRowsModeFourOneBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode hguard hrows henvironmentSize hwidthBound htokenCountBound
        hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeFourSame hcount hconsumed hmode failure hrows =>
      refine (compactFormulaTransformTermOutputRowsModeFourSameBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode failure hrows henvironmentSize hwidthBound htokenCountBound
        hcurrentOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeFiveCaptured hcount hconsumed hmode hguard hrows =>
      refine (compactFormulaTransformTermOutputRowsModeFiveCapturedBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode hguard hrows henvironmentSize hwidthBound htokenCountBound
        hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeFiveResidual hcount hconsumed hmode hguard residual hresidual
      hequality hrows =>
      refine (compactFormulaTransformTermOutputRowsModeFiveResidualBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (residual := residual) (numericBound := numericBound)
        (bitBound := bitBound) hcount hconsumed hmode hguard hresidual
        hequality hrows henvironmentSize hwidthBound htokenCountBound
        hnextOutputCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | modeFiveRaw hcount hconsumed hmode failure hrows =>
      refine (compactFormulaTransformTermOutputRowsModeFiveRawBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hmode failure hrows henvironmentSize hwidthBound htokenCountBound
        hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega
  | other hcount hconsumed hzero hone htwo hfour hfive hrows =>
      refine (compactFormulaTransformTermOutputRowsOtherBranch_structuralPayloadBound_le_fullyFixed
        (tokenTable := tokenTable) (width := width) (tokenCount := tokenCount)
        (current := current) (next := next) (mode := mode)
        (binderArity := binderArity) (tag := tag) (argument := argument)
        (consumedCount := consumedCount) (witnessStart := witnessStart)
        (witnessFinish := witnessFinish) (witnessCount := witnessCount)
        (numericBound := numericBound) (bitBound := bitBound) hcount hconsumed
        hzero hone htwo hfour hfive hrows henvironmentSize hwidthBound
        htokenCountBound hnumericSize).trans ?_
      unfold termRowsAllBranchesFullyFixedPayloadPolynomial
      omega

theorem
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactFormulaTransformStateRowCoordinates)
    (mode binderArity tag argument consumedCount : Nat)
    (witnessStart witnessFinish witnessCount numericBound bitBound : Nat)
    (hgraph : CompactFormulaTransformTermOutputRows tokenTable width tokenCount
      current next mode binderArity tag argument consumedCount witnessStart
      witnessFinish witnessCount)
    (henvironmentSize : forall coordinate,
      Nat.size
        (compactFormulaTransformTermOutputRowsEnvironment tokenTable width
          tokenCount current next mode binderArity tag argument consumedCount
          witnessStart witnessFinish witnessCount coordinate) <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hcurrentOutputCountBound : current.outputCount <= numericBound)
    (hnextOutputCountBound : next.outputCount <= numericBound)
    (hwitnessCountBound : witnessCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next mode binderArity tag argument
          consumedCount witnessStart witnessFinish witnessCount hgraph) <=
      termRowsAllBranchesFullyFixedPayloadPolynomial numericBound bitBound := by
  let data :=
    compactFormulaTransformTermOutputRowsCheckedBranchDataOfGraph tokenTable
      width tokenCount current next mode binderArity tag argument consumedCount
      witnessStart witnessFinish witnessCount hgraph
  have hfixed :=
    compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next mode binderArity tag argument
      consumedCount witnessStart witnessFinish witnessCount numericBound
      bitBound data henvironmentSize hwidthBound htokenCountBound
      hcurrentOutputCountBound hnextOutputCountBound hwitnessCountBound
      hnumericSize
  unfold compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph
  simpa only [data, hybridFormulaStructuralPayloadBound] using hfixed

#print axioms
  compactFormulaTransformTermOutputRowsExplicitHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
#print axioms
  compactFormulaTransformTermOutputRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectFormulaTransformTermOutputRowsAllBranchesFullyFixedBounds
