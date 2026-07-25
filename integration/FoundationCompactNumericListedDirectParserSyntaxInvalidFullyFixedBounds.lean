import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxInvalidAtomicFixedBounds
import integration.FoundationCompactPAHybridSixConjunctionCertificateClosedGeneralBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadSizeBounds
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-!
# Fully fixed invalid syntax-task branch

The original six checked leaves are retained: running status, task uncons,
three native-tag disequalities, and the failure transition.  Their formula
codes are bounded through the actual checked certificates, avoiding reduction
of the large 25-coordinate substitution.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAEmbeddedPredicateFreeVariables
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerFixedPolynomialBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridSixConjunctionClosedGeneralBounds
open FoundationCompactPAHybridSixConjunctionCertificateClosedGeneralBounds
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidRows
open FoundationCompactNumericListedDirectParserSyntaxInvalidExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxInvalidPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectBinaryNatStatusCases
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusFixedPolynomialBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsWithSizeFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxInvalidAtomicFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsGenericHeadSizeBounds

private abbrev invalidZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate.zeroValuation

def syntaxInvalidClosedFormulaCodePolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial numericBound
      bitBound +
    unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound +
    3 * parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound +
    syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound +
    20 * (binaryNatCode 4).length + 100

def syntaxInvalidFullyFixedPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridSixConjunctionGeneralPayloadEnvelope
    (syntaxInvalidClosedFormulaCodePolynomial tokenCount numericBound bitBound)
    (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
      numericBound bitBound)
    (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
    (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
    (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
    (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)

theorem
    compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxInvalidTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hgraph : CompactUnifiedParserSyntaxInvalidRows tokenTable width tokenCount
      current next witness)
    (hwidth : width <= numericBound)
    (hwidthBit : width <= bitBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness hgraph) <=
      syntaxInvalidFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound := by
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeClosedFormula tokenTable
      width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount
  let zeroFormula := fixedNeFormula witness.kind 0
  let oneFormula := fixedNeFormula witness.kind 1
  let twoFormula := fixedNeFormula witness.kind 2
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hgraph.1
  let unconsCertificate :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount hgraph.2.1
  let zeroCertificate := fixedNeCertificate witness.kind 0 hgraph.2.2.1
  let oneCertificate := fixedNeCertificate witness.kind 1 hgraph.2.2.2.1
  let twoCertificate := fixedNeCertificate witness.kind 2 hgraph.2.2.2.2.1
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hgraph.2.2.2.2.2
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcurrentFinishSize : Nat.size current.finish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (1 : Fin 8)
  have hcurrentTasksFinish : current.tasksFinish <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (3 : Fin 8)
  have hcurrentTasksFinishSize :
      Nat.size current.tasksFinish <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (3 : Fin 8)
  have hcurrentTasksCount : current.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (7 : Fin 8)
  have hcurrentTasksBoundarySize :
      Nat.size current.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (6 : Fin 8)
  have hkindSize : Nat.size witness.kind <= bitBound := by
    rcases hgraph.2.1.2.2.2.1.2.1 with
      ⟨targetLeft, _, targetRight, _, _, _, hlayout⟩
    exact
      (compactSyntaxTaskDirectLayout_fieldSizes_le_width tokenTable width
        tokenCount targetLeft targetRight witness.kind witness.binderArity
        witness.repeatCount hlayout).1.trans hwidthBit
  have htailCount : witness.tailCount <= numericBound := by
    have hdrop := hgraph.2.1.2.1
    unfold CompactAdditiveSyntaxTaskListDropRows at hdrop
    omega
  have hrunning :
      hybridFormulaStructuralPayloadBound runningCertificate <=
        compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
          numericBound bitBound := by
    dsimp only [runningCertificate]
    exact
      compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_fullyUniform
        tokenTable width tokenCount current.tasksFinish current.finish
        numericBound bitBound hwidth hcurrentTasksFinish htokenTableSize
        hwidthSize htokenCountSize hcurrentTasksFinishSize
        hcurrentFinishSize hgraph.1
  have huncons :
      hybridFormulaStructuralPayloadBound unconsCertificate <=
        unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
          bitBound := by
    dsimp only [unconsCertificate]
    exact unconsRowsWithSizeCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      witness.kind witness.binderArity witness.repeatCount numericBound
      bitBound hgraph.2.1 hwidth htokenCount hcurrentTasksCount htailCount
      htokenTableSize hcurrentTasksBoundarySize htailBoundarySize hnumericSize
  have hzero :
      hybridFormulaStructuralPayloadBound zeroCertificate <=
        parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound := by
    dsimp only [zeroCertificate]
    exact fixedNeCertificate_structuralPayloadBound_le_fullyFixed witness.kind 0
      bitBound hgraph.2.2.1 hkindSize (by omega)
  have hone :
      hybridFormulaStructuralPayloadBound oneCertificate <=
        parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound := by
    dsimp only [oneCertificate]
    exact fixedNeCertificate_structuralPayloadBound_le_fullyFixed witness.kind 1
      bitBound hgraph.2.2.2.1 hkindSize (by omega)
  have htwo :
      hybridFormulaStructuralPayloadBound twoCertificate <=
        parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound := by
    dsimp only [twoCertificate]
    exact fixedNeCertificate_structuralPayloadBound_le_fullyFixed witness.kind 2
      bitBound hgraph.2.2.2.2.1 hkindSize (by omega)
  have hfailure :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound := by
    dsimp only [failureCertificate]
    exact
      compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hgraph.2.2.2.2.2 hwidth
        htokenCount htailCount hcurrentValue hnextValue htokenTableSize
        hwidthSize htokenCountSize hcurrentSize hnextSize htailBoundarySize
        hnumericSize hbitPositive
  have htotalClosed :
      (runningFormula ⋏
        (unconsFormula ⋏
          (zeroFormula ⋏
            (oneFormula ⋏ (twoFormula ⋏ failureFormula))))).freeVariables =
        ∅ := by
    have hraw :=
      compactUnifiedParserSyntaxInvalidClosedFormula_alignment tokenTable
        width tokenCount current next witness
    have hclosed :
        (compactUnifiedParserSyntaxInvalidClosedFormula tokenTable width
          tokenCount current next witness).freeVariables = ∅ := by
      unfold compactUnifiedParserSyntaxInvalidClosedFormula
      apply embeddedSubstitution_freeVariables_eq_empty_of_closed_terms
      intro coordinate
      fin_cases coordinate <;>
        apply shortBinaryNumeralTerm_freeVariables_eq_empty
    rw [hraw] at hclosed
    simpa only [compactUnifiedParserSyntaxInvalidExplicitFormula,
      runningFormula, unconsFormula, zeroFormula, oneFormula, twoFormula,
      failureFormula] using hclosed
  have hclosedParts :
      runningFormula.freeVariables = ∅ ∧
      unconsFormula.freeVariables = ∅ ∧
      zeroFormula.freeVariables = ∅ ∧
      oneFormula.freeVariables = ∅ ∧
      twoFormula.freeVariables = ∅ ∧
      failureFormula.freeVariables = ∅ := by
    simpa only [LO.FirstOrder.Semiformula.freeVariables_and,
      Finset.union_eq_empty] using htotalClosed
  have hcodeRunning :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      runningCertificate).trans hrunning
  have hcodeUncons :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      unconsCertificate).trans huncons
  have hcodeZero :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      zeroCertificate).trans hzero
  have hcodeOne :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      oneCertificate).trans hone
  have hcodeTwo :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      twoCertificate).trans htwo
  have hcodeFailure :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      failureCertificate).trans hfailure
  have hcode :
      (binaryFormulaCode
        (runningFormula ⋏
          (unconsFormula ⋏
            (zeroFormula ⋏
              (oneFormula ⋏ (twoFormula ⋏ failureFormula)))))).length <=
        syntaxInvalidClosedFormulaCodePolynomial tokenCount numericBound
          bitBound := by
    dsimp only [runningFormula, unconsFormula, zeroFormula, oneFormula,
      twoFormula, failureFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxInvalidClosedFormulaCodePolynomial
    omega
  have hassembly :=
    checkedHybridSixConjunctionPayloadBound_le_closedGeneral
      invalidZeroValuation runningFormula unconsFormula zeroFormula oneFormula
      twoFormula failureFormula runningCertificate unconsCertificate
      zeroCertificate oneCertificate twoCertificate failureCertificate
      (compactBinaryNatRunningStatusSliceFullyUniformPayloadPolynomial
        numericBound bitBound)
      (unconsRowsWithSizeFullyFixedPayloadPolynomial tokenCount numericBound
        bitBound)
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (parserFormulaNegativeAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
      (syntaxInvalidClosedFormulaCodePolynomial tokenCount numericBound
        bitBound)
      hrunning huncons hzero hone htwo hfailure (by
        unfold syntaxInvalidClosedFormulaCodePolynomial
        omega)
      hclosedParts.1 hclosedParts.2.1 hclosedParts.2.2.1
      hclosedParts.2.2.2.1 hclosedParts.2.2.2.2.1
      hclosedParts.2.2.2.2.2 hcode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.cast
        (compactUnifiedParserSyntaxInvalidClosedFormula_alignment tokenTable
          width tokenCount current next witness).symm
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          runningCertificate
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            unconsCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              zeroCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                oneCertificate
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  twoCertificate failureCertificate)))))) <= _
  unfold syntaxInvalidFullyFixedPayloadPolynomial
  simpa only [hybridFormulaStructuralPayloadBound, runningFormula,
    unconsFormula, zeroFormula, oneFormula, twoFormula, failureFormula,
    runningCertificate, unconsCertificate, zeroCertificate, oneCertificate,
    twoCertificate, failureCertificate] using hassembly

#print axioms
  compactUnifiedParserSyntaxInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxInvalidFullyFixedBounds
