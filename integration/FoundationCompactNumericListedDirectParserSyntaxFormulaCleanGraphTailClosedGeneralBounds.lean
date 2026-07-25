import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailFullyFixedBounds

/-! # Closed-general bound for the clean syntax-formula parser tail -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailClosedGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataPayloadPolynomial
open FoundationCompactNumericListedDirectParserSyntaxFormulaCheckedDataFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBoundsDefinitions
open FoundationCompactNumericListedDirectParserSyntaxFormulaUnconsFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailFullyFixedBounds

theorem
    compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph_structuralPayloadBound_le_fullyFixed
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
      cleanParserSyntaxFormulaTailPayloadPolynomial tokenCount numericBound
        bitBound := by
  let unconsGraph := hgraph.2.1
  let unconsCertificate :=
    compactUnifiedParserSyntaxFormulaCleanUnconsCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  let branchCertificate :=
    compactUnifiedParserSyntaxFormulaCleanBranchCertificateOfGraph tokenTable
      width tokenCount current next binderArity witness hgraph
  have htransparent :=
    compactUnifiedParserSyntaxFormulaCleanTailCertificateOfGraph_structuralPayloadBound_le_transparentFixed
      tokenTable width tokenCount current next binderArity numericBound bitBound
      witness hgraph hwidth htokenCount hcurrentValue hnextValue
      htokenTableSize hcurrentSize hnextSize htailBoundarySize
      hbinderAritySize hrelationAritySize hrelationCodeSize htagSize
      hnumericSize hbitPositive
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
      compactUnifiedParserSyntaxFormulaCleanBranchCertificateOfGraph]
    exact
      compactUnifiedParserSyntaxFormulaBranchCleanHybridCertificateFromData_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next binderArity numericBound
        bitBound witness
        (compactSyntaxFormulaCheckedBranchDataOfGraph tokenTable width tokenCount
          current next binderArity witness hgraph)
        hwidth htokenCount hcurrentValue hnextValue htokenTableSize hcurrentSize
        hnextSize htailBoundarySize hbinderAritySize hrelationAritySize
        hrelationCodeSize htagSize hnumericSize hbitPositive
  have hunconsClosed :
      (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
        tokenTable width tokenCount current.tasksBoundary current.tasksCount
        witness.tailBoundary witness.tailCount witness.tailBoundarySize
        (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          1)
        (shortBinaryNumeralTerm binderArity)
        (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
          0)).freeVariables = ∅ :=
    parserSyntaxFormulaUnconsGraphFormula_freeVariables_eq_empty tokenTable width
      tokenCount current.tasksBoundary current.tasksCount witness.tailBoundary
      witness.tailCount witness.tailBoundarySize binderArity
  have hbranchClosed :
      (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness).freeVariables = ∅ :=
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  have hunconsCode :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            1)
          (shortBinaryNumeralTerm binderArity)
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            0))).length <=
        parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      unconsCertificate).trans hunconsResource
  have hbranchCode :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
          tokenCount current next binderArity witness)).length <=
        syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
          numericBound bitBound :=
    (CheckedHybridValuationBoundedFormulaCertificate.formulaCodeLength_le_structuralPayloadBound
      branchCertificate).trans hbranchResource
  have hsyntaxPositive :
      1 <= cleanParserSyntaxFormulaTailCodePolynomial tokenCount numericBound
        bitBound := by
    unfold cleanParserSyntaxFormulaTailCodePolynomial
    omega
  have hunconsCodeGlobal :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            1)
          (shortBinaryNumeralTerm binderArity)
          (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
            0))).length <=
        cleanParserSyntaxFormulaTailCodePolynomial tokenCount numericBound
          bitBound :=
    hunconsCode.trans (by
      unfold cleanParserSyntaxFormulaTailCodePolynomial
      omega)
  have hbranchCodeGlobal :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
          tokenCount current next binderArity witness)).length <=
        cleanParserSyntaxFormulaTailCodePolynomial tokenCount numericBound
          bitBound :=
    hbranchCode.trans (by
      unfold cleanParserSyntaxFormulaTailCodePolynomial
      omega)
  have htotalCode :
      (binaryFormulaCode
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
            tokenTable width tokenCount current.tasksBoundary current.tasksCount
            witness.tailBoundary witness.tailCount witness.tailBoundarySize
            (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
              1)
            (shortBinaryNumeralTerm binderArity)
            (FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
              0) ⋏
          compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness)).length <=
        cleanParserSyntaxFormulaTailCodePolynomial tokenCount numericBound
          bitBound := by
    simp only [binaryFormulaCode, List.length_append]
    unfold cleanParserSyntaxFormulaTailCodePolynomial
    omega
  have henvelope :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
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
      (parserSyntaxFormulaUnconsFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      (syntaxFormulaCheckedDataFullyFixedPayloadPolynomial tokenCount
        numericBound bitBound)
      (cleanParserSyntaxFormulaTailCodePolynomial tokenCount numericBound
        bitBound)
      hsyntaxPositive hunconsClosed hbranchClosed hunconsCodeGlobal
      hbranchCodeGlobal htotalCode
  unfold cleanParserSyntaxFormulaTailTransparentEnvelope at htransparent
  unfold cleanParserSyntaxFormulaTailPayloadPolynomial
  exact Nat.le_trans htransparent henvelope

end FoundationCompactNumericListedDirectParserSyntaxFormulaCleanGraphTailClosedGeneralBounds
