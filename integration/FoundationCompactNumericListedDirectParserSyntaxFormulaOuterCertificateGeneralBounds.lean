import integration.FoundationCompactPAHybridOuterSelectedBranchClosedGeneralBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
import integration.FoundationCompactListedProofHonestWeight

/-!
# Fixed outer-certificate assembly for syntax-formula parsing

This file closes the empty path and the common enough-path wrapper.  Concrete
tag branches discharge the remaining selected-branch premise downstream.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaOuterCertificateGeneralBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactListedProofHonestWeight
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactPAHybridOuterSelectedBranchClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaTagBranchTreeFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaOuterSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListSameRows

private theorem binaryFormulaCode_and_left_le_outerCertificate
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_and_right_le_outerCertificate
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

def syntaxFormulaOuterEmptyFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  outerSelectedEmptyPayloadEnvelope
    (syntaxFormulaOuterFullyFixedCodePolynomial bitBound)
    (hybridConjunctionGeneralPayloadEnvelope
      (syntaxFormulaOuterFullyFixedCodePolynomial bitBound)
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound))

theorem syntaxFormulaOuterEmptyCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : current.tokensCount = 0)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (hnextValue :
      CompactUnifiedParserStateCoordinateValueBound next numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (htailCountSize : Nat.size witness.tailCount <= bitBound)
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right :=
            syntaxFormulaEnoughFormula tokenTable width tokenCount current next
              binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqCertificate current.tokensCount 0 hcount)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure))) <=
      syntaxFormulaOuterEmptyFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let empty :=
    syntaxFormulaEmptyFormula tokenTable width tokenCount current next witness
  let enough :=
    syntaxFormulaEnoughFormula tokenTable width tokenCount current next
      binderArity witness
  let countCertificate := nativeEqCertificate current.tokensCount 0 hcount
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let emptyCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      failureCertificate
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have htailCount : witness.tailCount <= numericBound := by
    have hnextTasksCount : next.tasksCount <= numericBound := by
      simpa [compactUnifiedParserStateCoordinateValues] using
        hnextValue (7 : Fin 8)
    have htasks := hfailure.2.2
    unfold CompactAdditiveSyntaxTaskListSameRows at htasks
    omega
  have hcountPayload :
      hybridFormulaStructuralPayloadBound countCertificate <=
        parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound := by
    dsimp only [countCertificate]
    exact nativeEqCertificate_structuralPayloadBound_le_fixed
      current.tokensCount 0 bitBound hcount hcurrentTokensCountSize (by omega)
  have hfailurePayload :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound := by
    dsimp only [failureCertificate]
    exact
      compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hfailure hwidth htokenCount
        htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
        htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
        hbitPositive
  have houterClosed :=
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaOuterFormula_alignment] at houterClosed
  have houterCode :=
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  rw [syntaxFormulaOuterFormula_alignment] at houterCode
  have hsyntaxPositive :
      1 <= syntaxFormulaOuterFullyFixedCodePolynomial bitBound :=
    (one_le_binaryFormulaCode_length (empty ⋎ enough)).trans houterCode
  have hemptyClosed :
      empty.freeVariables = ∅ := by
    simpa only [empty] using
      syntaxFormulaEmptyFormula_freeVariables_eq_empty_fullyFixed tokenTable
        width tokenCount current next witness
  have hcountClosed :
      (nativeEqFormula current.tokensCount 0).freeVariables = ∅ :=
    nativeEqFormula_freeVariables_eq_empty_fixed _ _
  have hfailureClosed :
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary
        witness.tailCount).freeVariables = ∅ :=
    syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  have hemptyCode :
      (binaryFormulaCode empty).length <=
        syntaxFormulaOuterFullyFixedCodePolynomial bitBound := by
    have hsmall :
        (binaryFormulaCode empty).length <=
          syntaxFormulaEmptyFullyFixedCodePolynomial bitBound := by
      simpa only [empty] using
        syntaxFormulaEmptyFormula_code_length_le_fullyFixed tokenTable width
          tokenCount current next witness bitBound htokenTableSize hwidthSize
          htokenCountSize hcurrentSize hnextSize htailBoundarySize
          htailCountSize
    exact hsmall.trans (by
      unfold syntaxFormulaOuterFullyFixedCodePolynomial
      omega)
  have hcountCode :
      (binaryFormulaCode (nativeEqFormula current.tokensCount 0)).length <=
        syntaxFormulaOuterFullyFixedCodePolynomial bitBound :=
    (binaryFormulaCode_and_left_le_outerCertificate
      (nativeEqFormula current.tokensCount 0)
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)).trans
      (by simpa only [empty, syntaxFormulaEmptyFormula] using hemptyCode)
  have hfailureCode :
      (binaryFormulaCode
        (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary
          witness.tailCount)).length <=
        syntaxFormulaOuterFullyFixedCodePolynomial bitBound :=
    (binaryFormulaCode_and_right_le_outerCertificate
      (nativeEqFormula current.tokensCount 0)
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)).trans
      (by simpa only [empty, syntaxFormulaEmptyFormula] using hemptyCode)
  have hemptyPayload :
      hybridFormulaStructuralPayloadBound emptyCertificate <=
        hybridConjunctionGeneralPayloadEnvelope
          (syntaxFormulaOuterFullyFixedCodePolynomial bitBound)
          (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
          (syntaxTermFailureFullyFixedPayloadPolynomial numericBound
            bitBound) := by
    dsimp only [emptyCertificate]
    exact
      checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
        failureCertificate
        (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
        (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
        (syntaxFormulaOuterFullyFixedCodePolynomial bitBound) hcountPayload
        hfailurePayload hsyntaxPositive hcountClosed hfailureClosed hcountCode
        hfailureCode (by
          simpa only [empty, syntaxFormulaEmptyFormula] using hemptyCode)
  have hresult :=
    checkedHybridOuterEmptyPayloadBound_le_closedGeneral empty enough
      emptyCertificate
      (hybridConjunctionGeneralPayloadEnvelope
        (syntaxFormulaOuterFullyFixedCodePolynomial bitBound)
        (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
        (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound))
      (syntaxFormulaOuterFullyFixedCodePolynomial bitBound) hemptyPayload
      hsyntaxPositive houterClosed houterCode
  unfold syntaxFormulaOuterEmptyFullyFixedPayloadPolynomial
  dsimp only [empty, enough, emptyCertificate, countCertificate,
    failureCertificate] at hresult ⊢
  exact hresult

def syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial
    (numericBound bitBound branchResource : Nat) : Nat :=
  outerSelectedEnoughPayloadEnvelope
    (syntaxFormulaOuterFullyFixedCodePolynomial bitBound)
    (parserFormulaTermLeFixedPayloadPolynomial bitBound)
    (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
      numericBound bitBound)
    branchResource

theorem syntaxFormulaOuterEnoughCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound branchResource : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (branchCertificate :
      CheckedHybridValuationBoundedFormulaCertificate (fun _ => 0)
      (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness))
    (hbranch :
      hybridFormulaStructuralPayloadBound branchCertificate <= branchResource)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (htailCount : witness.tailCount <= numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
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
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left :=
            syntaxFormulaEmptyFormula tokenTable width tokenCount current next
              witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (by simp) hatTag)
              branchCertificate))) <=
      syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial numericBound bitBound
        branchResource := by
  let empty :=
    syntaxFormulaEmptyFormula tokenTable width tokenCount current next witness
  let guard := nativeShortLeFormula 1 current.tokensCount
  let lookup :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.tag
      (fixedNumeralTerm 0)
  let branch :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness
  let guardCertificate := nativeShortLeCertificate 1 current.tokensCount hcount
  let lookupCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag (fixedNumeralTerm 0) (by simp) hatTag
  have hcurrentTokensBoundary :
      current.tokensBoundary <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (4 : Fin 8)
  have hcurrentTokensCount :
      current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hcurrentTokensBoundarySize :
      Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hguard :
      hybridFormulaStructuralPayloadBound guardCertificate <=
        parserFormulaTermLeFixedPayloadPolynomial bitBound := by
    dsimp only [guardCertificate]
    exact nativeShortLeCertificate_structuralPayloadBound_le_fixed 1
      current.tokensCount bitBound hcount (by omega) hcurrentTokensCountSize
  have hlookup :
      hybridFormulaStructuralPayloadBound lookupCertificate <=
        compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
          numericBound bitBound := by
    dsimp only [lookupCertificate]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
        witness.tag numericBound bitBound hatTag hwidth htokenCount
        hcurrentTokensCount htokenTableSize hwidthSize htokenCountSize
        hcurrentTokensBoundarySize hcurrentTokensCountSize htagSize (by omega)
  have hclosed :=
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_freeVariables_eq_empty_fullyFixed
      tokenTable width tokenCount current next binderArity witness
  rw [syntaxFormulaOuterFormula_alignment] at hclosed
  change (empty ⋎ (guard ⋏ (lookup ⋏ branch))).freeVariables = ∅ at hclosed
  have hcode :=
    compactUnifiedParserSyntaxFormulaBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
      htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
      hrelationCodeSize htagSize hbitPositive
  rw [syntaxFormulaOuterFormula_alignment] at hcode
  change
    (binaryFormulaCode (empty ⋎ (guard ⋏ (lookup ⋏ branch)))).length <=
      syntaxFormulaOuterFullyFixedCodePolynomial bitBound at hcode
  have hsyntaxPositive :
      1 <= syntaxFormulaOuterFullyFixedCodePolynomial bitBound :=
    (one_le_binaryFormulaCode_length
      (empty ⋎ (guard ⋏ (lookup ⋏ branch)))).trans hcode
  unfold syntaxFormulaOuterEnoughFullyFixedPayloadPolynomial
  exact
    checkedHybridOuterEnoughPayloadBound_le_closedGeneral empty guard lookup
      branch guardCertificate lookupCertificate branchCertificate
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
        numericBound bitBound)
      branchResource (syntaxFormulaOuterFullyFixedCodePolynomial bitBound)
      hguard hlookup hbranch hsyntaxPositive hclosed hcode

end FoundationCompactNumericListedDirectParserSyntaxFormulaOuterCertificateGeneralBounds
