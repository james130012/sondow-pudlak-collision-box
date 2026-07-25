import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
import integration.FoundationCompactPAHybridConjunctionGeneralContextBounds
import integration.FoundationCompactPAHybridDisjunctionGeneralContextBounds

/-!
# Fully fixed relation-short body certificate

The genuine short-input comparison and syntax-term failure certificate are
assembled into the left branch of the original complete relation-body formula.
The unselected long branch contributes syntax only, through the fixed complete
formula bound.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 50000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaRelationShortFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactListedLocalCostPrimitives
open FoundationCompactPAExplicitBoundedWitnessDirectCompilerPolynomialBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureSubstitutionSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaRelationBodySyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private def relationShortZeroValuation : Nat -> Nat := fun _ => 0

def syntaxFormulaRelationShortPairFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridConjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (parserFormulaTermLeFixedPayloadPolynomial bitBound)
    (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)

def syntaxFormulaRelationShortBodyFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  hybridDisjunctionGeneralPayloadEnvelope
    (syntaxFormulaRelationBodyCodePolynomial bitBound)
    (syntaxFormulaRelationShortPairFullyFixedPayloadPolynomial numericBound
      bitBound)

private theorem binaryFormulaCode_or_left_le_relationShort
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_or_right_le_relationShort
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem natPreorderLE_to_legacyLE_relationShort
    {left right : Nat}
    (h : @LE.le Nat Nat.instPreorder.toLE left right) :
    @LE.le Nat instLENat left right := by
  omega

private theorem disjunctionLeftEnvelope_le_closed_relationShort
    (left right : ValuationFormula) (childResource resource : Nat)
    (hpositive : 1 <= resource)
    (hleftClosed : left.freeVariables = ∅)
    (hrightClosed : right.freeVariables = ∅)
    (hleftCode : (binaryFormulaCode left).length <= resource)
    (hrightCode : (binaryFormulaCode right).length <= resource)
    (horCode : (binaryFormulaCode (left ⋎ right)).length <= resource) :
    transparentHybridDisjunctionLeftPayloadEnvelope relationShortZeroValuation
        left right childResource <=
      hybridDisjunctionGeneralPayloadEnvelope resource childResource := by
  apply transparentHybridDisjunctionLeftPayloadEnvelope_le_general
  · exact hpositive
  · rw [LO.FirstOrder.Semiformula.freeVariables_or, hleftClosed,
      hrightClosed]
    simp [valuationContext, formulaCodeSum]
  · exact hleftCode
  · exact hrightCode
  · exact horCode

noncomputable def syntaxFormulaRelationShortBodyCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    CheckedHybridValuationBoundedFormulaCertificate relationShortZeroValuation
      (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (shortNativeLeCertificate current.tokensCount 2 hshort)
      (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount hfailure))

theorem
    syntaxFormulaRelationShortBodyCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (numericBound bitBound : Nat)
    (hshort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (htailCount : witness.tailCount <= numericBound)
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
    (hbinderAritySize : Nat.size binderArity <= bitBound)
    (hrelationAritySize : Nat.size witness.relationArity <= bitBound)
    (hrelationCodeSize : Nat.size witness.relationCode <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxFormulaRelationShortBodyCertificate tokenTable width tokenCount
          current next binderArity witness hshort hfailure) <=
      syntaxFormulaRelationShortBodyFullyFixedPayloadPolynomial numericBound
        bitBound := by
  let shortFormula := shortNativeLeFormula current.tokensCount 2
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let shortBranch := shortFormula ⋏ failureFormula
  let longBranch :=
    nativeShortLeFormula 3 current.tokensCount ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount
        witness.relationArity (fixedNumeralTerm 1) ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount
        witness.relationCode (fixedNumeralTerm 2) ⋏
      ((compactAdditiveArithmeticRelCodeValidClosedFormula
              witness.relationArity witness.relationCode ⋏
          compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount binderArity witness.relationArity) ⋎
        (compactAdditiveArithmeticRelCodeInvalidClosedFormula
                witness.relationArity witness.relationCode ⋏
          failureFormula))
  let shortCertificate :=
    shortNativeLeCertificate current.tokensCount 2 hshort
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let pairCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      shortCertificate failureCertificate
  let syntaxResource := syntaxFormulaRelationBodyCodePolynomial bitBound
  let shortResource := parserFormulaTermLeFixedPayloadPolynomial bitBound
  let failureResource :=
    syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound
  let pairResource :=
    syntaxFormulaRelationShortPairFullyFixedPayloadPolynomial numericBound
      bitBound
  have hcurrentTokensCountSize :
      Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have htailCountSize : Nat.size witness.tailCount <= bitBound :=
    (Nat.size_le_size htailCount).trans hnumericSize
  have hshortResource :
      hybridFormulaStructuralPayloadBound shortCertificate <=
        shortResource := by
    dsimp only [shortCertificate, shortResource]
    exact shortNativeLeCertificate_structuralPayloadBound_le_fixed
      current.tokensCount 2 bitBound hshort hcurrentTokensCountSize (by omega)
  have hfailureResource :
      hybridFormulaStructuralPayloadBound failureCertificate <=
        failureResource := by
    dsimp only [failureCertificate, failureResource]
    exact
      compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount numericBound bitBound hfailure hwidth htokenCount
        htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
        htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
        hbitPositive
  have hshortClosed : shortFormula.freeVariables = ∅ := by
    simp [shortFormula]
  have hfailureClosed : failureFormula.freeVariables = ∅ := by
    exact
      syntaxTermFailureClosedFormula_freeVariables_eq_empty_substitutionFixed
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount
  have hshortCodeBase :
      (binaryFormulaCode shortFormula).length <=
        parserFormulaAtomicFormulaCodePolynomial bitBound := by
    dsimp only [shortFormula]
    exact shortNativeLeFormula_code_length_le_fixed current.tokensCount 2
      bitBound hcurrentTokensCountSize (by omega)
  have hshortCode :
      (binaryFormulaCode shortFormula).length <= syntaxResource := by
    exact hshortCodeBase.trans (by
      dsimp only [syntaxResource]
      unfold syntaxFormulaRelationBodyCodePolynomial
      omega)
  have hfailureCodeBase :
      (binaryFormulaCode failureFormula).length <=
        syntaxTermFailureSubstitutionFormulaCodePolynomial bitBound := by
    dsimp only [failureFormula]
    exact syntaxTermFailureClosedFormula_code_length_le_substitutionFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount bitBound htokenTableSize hwidthSize htokenCountSize
      hcurrentSize hnextSize htailBoundarySize htailCountSize
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource := by
    exact hfailureCodeBase.trans (by
      dsimp only [syntaxResource]
      unfold syntaxFormulaRelationBodyCodePolynomial
      omega)
  have hshortBranchCode :
      (binaryFormulaCode shortBranch).length <= syntaxResource := by
    have hraw := binaryFormulaCode_and_length_le shortFormula failureFormula
    dsimp only [shortBranch, syntaxResource]
    unfold syntaxFormulaRelationBodyCodePolynomial
    omega
  have hfullCode :
      (binaryFormulaCode (shortBranch ⋎ longBranch)).length <=
        syntaxResource := by
    have hnamed :=
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_code_length_le_fixed
        tokenTable width tokenCount current next binderArity witness bitBound
        htokenTableSize hwidthSize htokenCountSize hcurrentSize hnextSize
        htailBoundarySize htailCountSize hbinderAritySize hrelationAritySize
        hrelationCodeSize
    unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula at hnamed
    simpa only [shortBranch, longBranch, shortFormula, failureFormula] using
      hnamed
  have hbodyClosed :
      (shortBranch ⋎ longBranch).freeVariables = ∅ := by
    dsimp only [shortBranch, longBranch]
    change
      (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula tokenTable
        width tokenCount current next binderArity witness).freeVariables = ∅
    exact
      compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula_freeVariables_eq_empty_fixed
        tokenTable width tokenCount current next binderArity witness
  have hbranchesClosed :
      shortBranch.freeVariables = ∅ ∧ longBranch.freeVariables = ∅ := by
    rw [LO.FirstOrder.Semiformula.freeVariables_or] at hbodyClosed
    exact Finset.union_eq_empty.mp hbodyClosed
  have hlongCode :
      (binaryFormulaCode longBranch).length <= syntaxResource :=
    (binaryFormulaCode_or_right_le_relationShort shortBranch longBranch).trans
      hfullCode
  have hpairRaw := transparentHybridConjunctionPayloadBound_le
    shortCertificate failureCertificate shortResource failureResource
    hshortResource hfailureResource
  have hpairAssembly :=
    transparentHybridConjunctionPayloadEnvelope_le_closedGeneral
      relationShortZeroValuation shortFormula failureFormula shortResource
      failureResource syntaxResource
      (by
        dsimp only [syntaxResource]
        unfold syntaxFormulaRelationBodyCodePolynomial
        omega)
      hshortClosed hfailureClosed hshortCode hfailureCode hshortBranchCode
  have hpairResource :
      hybridFormulaStructuralPayloadBound pairCertificate <= pairResource := by
    dsimp only [pairResource]
    unfold syntaxFormulaRelationShortPairFullyFixedPayloadPolynomial
    apply natPreorderLE_to_legacyLE_relationShort
    simpa only [pairCertificate, shortBranch] using
      hpairRaw.trans hpairAssembly
  have houterRaw := transparentHybridDisjunctionLeftPayloadBound_le
    (right := longBranch) pairCertificate pairResource hpairResource
  have houterAssembly :=
    disjunctionLeftEnvelope_le_closed_relationShort shortBranch longBranch
      pairResource syntaxResource
      (by
        dsimp only [syntaxResource]
        unfold syntaxFormulaRelationBodyCodePolynomial
        omega)
      hbranchesClosed.1 hbranchesClosed.2 hshortBranchCode hlongCode hfullCode
  unfold syntaxFormulaRelationShortBodyFullyFixedPayloadPolynomial
  unfold syntaxFormulaRelationShortBodyCertificate
  apply natPreorderLE_to_legacyLE_relationShort
  convert houterRaw.trans houterAssembly using 1
  dsimp only [pairCertificate, shortCertificate, failureCertificate]
  rfl

#print axioms
  syntaxFormulaRelationShortBodyCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxFormulaRelationShortFullyFixedBounds
