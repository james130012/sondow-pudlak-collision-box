import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailCertificate
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds

/-! # Fully fixed bound for the clean syntax-formula parser tail -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridConjunctionStructuralPayloadTransparentEquality
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataCleanCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBounds

def cleanParserSyntaxFormulaTailCodePolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound +
    syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound +
    (binaryNatCode 4).length + 1

def cleanParserSyntaxFormulaTailPayloadPolynomial
    (tokenCount numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (cleanParserSyntaxFormulaTailCodePolynomial tokenCount numericBound bitBound)
    (parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    (syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

def cleanParserSyntaxFormulaTailTransparentEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates) : Nat :=
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
    (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        1)
      (shortBinaryNumeralTerm binderArity)
      (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
        0))
    (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness)
    (parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)
    (syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount numericBound
      bitBound)

theorem
    compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph_structuralPayloadBound_le_transparentFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxFormulaRows tokenTable width tokenCount
      current next binderArity witness)
    (hwidth : width <= numericBound)
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
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph tokenTable
          width tokenCount current next binderArity witness hgraph) <=
      cleanParserSyntaxFormulaTailTransparentEnvelope tokenTable width tokenCount
        current next binderArity numericBound bitBound witness := by
  let unconsGraph := hgraph.2.1
  let branchData :=
    compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph
  let unconsCertificate :=
    compactUnifiedParserSyntaxFormulaCleanUnconsCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  let branchCertificate :=
    compactUnifiedParserSyntaxFormulaCleanBranchCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  have hsourceCount : current.tasksCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (7 : Fin 8)
  have hsourceBoundarySize : Nat.size current.tasksBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (6 : Fin 8)
  have htailCount : witness.tailCount <= numericBound := by
    have hdrop := unconsGraph.2.1
    unfold CompactAdditiveSyntaxTaskListDropRows at hdrop
    omega
  have hunconsResource :
      hybridFormulaStructuralPayloadBound unconsCertificate <=
        parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    simpa only [unconsCertificate,
      compactUnifiedParserSyntaxFormulaCleanUnconsCertificateOfGraph] using
      parserSyntaxFormulaUnconsGraphCertificate_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        binderArity numericBound bitBound unconsGraph hwidth htokenCount
        hsourceCount htailCount htokenTableSize hsourceBoundarySize
        htailBoundarySize hbinderAritySize hnumericSize
  have hbranchResource :
      hybridFormulaStructuralPayloadBound branchCertificate <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound := by
    dsimp only [branchCertificate,
      compactUnifiedParserSyntaxFormulaCleanBranchCertificateOfGraph,
      branchData]
    exact
      compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity numericBound
        bitBound witness branchData hwidth htokenCount hcurrentValue hnextValue
        htokenTableSize hcurrentSize hnextSize htailBoundarySize
        hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
        hnumericSize hbitPositive
  have htransparent :
      hybridFormulaStructuralPayloadBound
          (compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph
            tokenTable width tokenCount current next binderArity witness
            hgraph) <=
        transparentHybridConjunctionPayloadEnvelope
          FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate.zeroValuation
          (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
            tokenTable width tokenCount current.tasksBoundary
            current.tasksCount witness.tailBoundary witness.tailCount
            witness.tailBoundarySize
            (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
              1)
            (shortBinaryNumeralTerm binderArity)
            (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
              0))
          (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness)
          (parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount
            numericBound bitBound)
          (syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
            numericBound bitBound) := by
    change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          unconsCertificate branchCertificate) <= _
    exact transparentHybridConjunctionPayloadBound_le unconsCertificate
      branchCertificate _ _ hunconsResource hbranchResource
  unfold cleanParserSyntaxFormulaTailTransparentEnvelope
  exact htransparent

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailFullyFixedBounds
