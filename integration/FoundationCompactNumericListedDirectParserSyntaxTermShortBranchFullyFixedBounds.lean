import integration.FoundationCompactNumericListedDirectParserSyntaxTermBranchFormulaFullyFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds

/-! # Fully fixed short-input branch of the complete Term formula -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxTermShortBranchFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridDisjunctionGeneralContextBounds
open FoundationCompactPAHybridSelectedConnectiveClosedGeneralBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserStateCoordinateUniformBounds
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermBranchFormulaFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

def syntaxTermShortBranchFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let shortResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource shortResource

private theorem binaryFormulaCode_left_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_or
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋎ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_left_length_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode left).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

private theorem binaryFormulaCode_right_length_le_and
    (left right : ValuationFormula) :
    (binaryFormulaCode right).length <=
      (binaryFormulaCode (left ⋏ right)).length := by
  simp only [binaryFormulaCode, List.length_append]
  omega

noncomputable def syntaxTermShortFullyFixedBranchCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcount : current.tokensCount <= 1)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermBranchExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (shortNativeLeCertificate current.tokensCount 1 hcount)
      (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount hfailure))

theorem
    syntaxTermShortFullyFixedBranchCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcount : current.tokensCount <= 1)
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
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (hnextSize :
      CompactUnifiedParserStateCoordinateSizeBound next bitBound)
    (htailBoundarySize : Nat.size witness.tailBoundary <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermShortFullyFixedBranchCertificate tokenTable width tokenCount
          current next binderArity witness hcount hfailure) <=
      syntaxTermShortBranchFullyFixedPayloadEnvelope numericBound bitBound := by
  let leFormula := shortNativeLeFormula current.tokensCount 1
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let shortFormula := leFormula ⋏ failureFormula
  let enoughFormula :=
    nativeShortLeFormula 2 current.tokensCount ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.tag
        (fixedNumeralTerm 0) ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.argument
        (fixedNumeralTerm 1) ⋏
      compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let leCertificate := shortNativeLeCertificate current.tokensCount 1 hcount
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let shortCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction leCertificate
      failureCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcurrentCountSize : Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hleResource :=
    syntaxTermShortNativeLeCertificate_structuralPayloadBound_le_fixed
      current.tokensCount 1 bitBound hcount hcurrentCountSize (by omega)
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hfailure hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
  have hbranchCode :=
    compactUnifiedParserSyntaxTermBranchExplicitFormula_code_length_le_fullyFixed
      tokenTable width tokenCount current next binderArity witness bitBound
      hsize
  have hbranchAlignment :
      compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
          tokenCount current next binderArity witness =
        shortFormula ⋎ enoughFormula := rfl
  rw [hbranchAlignment] at hbranchCode
  have hshortCode :
      (binaryFormulaCode shortFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_or shortFormula enoughFormula).trans
      hbranchCode
  have henoughCode :
      (binaryFormulaCode enoughFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_or shortFormula enoughFormula).trans
      hbranchCode
  have hleCode : (binaryFormulaCode leFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and leFormula
      failureFormula).trans hshortCode
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and leFormula
      failureFormula).trans hshortCode
  have hleClosed : leFormula.freeVariables = ∅ :=
    syntaxTermShortNativeLeFormula_freeVariables_eq_empty current.tokensCount 1
  have hfailureClosed : failureFormula.freeVariables = ∅ := by
    dsimp only [failureFormula]
    exact syntaxTermFailureClosedFormula_freeVariables_eq_empty tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
  have henoughClosed : enoughFormula.freeVariables = ∅ := by
    dsimp only [enoughFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermNativeShortLeFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
      LO.FirstOrder.Semiformula.freeVariables_and,
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
      compactUnifiedParserSyntaxTermDecisionExplicitFormula_freeVariables_eq_empty_fullyFixed]
    simp
  have hshort :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral leCertificate
      failureCertificate
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hleResource hfailureResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hleClosed hfailureClosed hleCode hfailureCode hshortCode
  have hbranch :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := enoughFormula) shortCertificate
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaTermLeFixedPayloadPolynomial bitBound)
        (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound))
      syntaxResource hshort
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hleClosed,
          hfailureClosed]
        simp)
      henoughClosed hshortCode henoughCode hbranchCode
  unfold syntaxTermShortFullyFixedBranchCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (right := enoughFormula) shortCertificate) <= _
  simpa only [syntaxTermShortBranchFullyFixedPayloadEnvelope,
    syntaxResource] using hbranch

#print axioms
  syntaxTermShortFullyFixedBranchCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxTermShortBranchFullyFixedBounds
