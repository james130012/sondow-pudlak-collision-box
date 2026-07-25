import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds

/-! # Fully fixed short-input endpoint inside the Term tag-two decision -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxTermTwoShortDecisionFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFormulaSyntaxFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionDecisionFixedBoundsCore
open FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermTwoDecisionPathFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionFormulaFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

def syntaxTermTwoShortSelectedFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let shortResource :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
  let choiceResource :=
    hybridDisjunctionGeneralPayloadEnvelope syntaxResource shortResource
  hybridConjunctionGeneralPayloadEnvelope syntaxResource
    (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound) choiceResource

def syntaxTermTwoShortDecisionFullyFixedPayloadEnvelope
    (numericBound bitBound : Nat) : Nat :=
  syntaxTermTwoDecisionPathFixedPayloadEnvelope
    (syntaxTermTwoShortSelectedFullyFixedPayloadEnvelope numericBound bitBound)
    bitBound

noncomputable def syntaxTermTwoShortFullyFixedDecisionCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (htooShort : current.tokensCount <= 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  let leCertificate :=
    shortNativeLeCertificate current.tokensCount 2 htooShort
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let shortCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction leCertificate
      failureCertificate
  let choiceCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := syntaxTermTwoFunctionFormula tokenTable width tokenCount current
        next binderArity witness)
      shortCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 2 htag) choiceCertificate
  exact syntaxTermTwoFixedDecisionPathCertificate tokenTable width tokenCount
    current next binderArity witness selectedCertificate

theorem
    syntaxTermTwoShortFullyFixedDecisionCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (htooShort : current.tokensCount <= 2)
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
    (htagSize : Nat.size witness.tag <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoShortFullyFixedDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag htooShort
          hfailure) <=
      syntaxTermTwoShortDecisionFullyFixedPayloadEnvelope numericBound
        bitBound := by
  let equalityFormula := nativeEqFormula witness.tag 2
  let leFormula := shortNativeLeFormula current.tokensCount 2
  let failureFormula :=
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
  let shortFormula := leFormula ⋏ failureFormula
  let functionFormula :=
    syntaxTermTwoFunctionFormula tokenTable width tokenCount current next
      binderArity witness
  let choiceFormula := shortFormula ⋎ functionFormula
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let equalityCertificate := nativeEqCertificate witness.tag 2 htag
  let leCertificate :=
    shortNativeLeCertificate current.tokensCount 2 htooShort
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let shortCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction leCertificate
      failureCertificate
  let choiceCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := functionFormula) shortCertificate
  let selectedCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      equalityCertificate choiceCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hcurrentCountSize : Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hequalityResource :=
    syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed witness.tag 2
      bitBound htag htagSize (by omega)
  have hleResource :=
    syntaxTermShortNativeLeCertificate_structuralPayloadBound_le_fixed
      current.tokensCount 2 bitBound htooShort hcurrentCountSize (by omega)
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount numericBound bitBound hfailure hwidth htokenCount
      htailCount hcurrentValue hnextValue htokenTableSize hwidthSize
      htokenCountSize hcurrentSize hnextSize htailBoundarySize hnumericSize
      hbitPositive
  have hcode (formula : ValuationFormula)
      (hsub :
        (binaryFormulaCode formula).length <=
          (binaryFormulaCode
            (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable
              width tokenCount current next binderArity witness)).length) :
      (binaryFormulaCode formula).length <= syntaxResource := by
    dsimp only [syntaxResource]
    exact syntaxTermDecisionComponent_code_length_le_fixed tokenTable width
      tokenCount current next binderArity witness bitBound formula hsub hsize
  have hequalityCode :
      (binaryFormulaCode equalityFormula).length <= syntaxResource :=
    hcode equalityFormula (by
      dsimp only [equalityFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hleCode : (binaryFormulaCode leFormula).length <= syntaxResource :=
    hcode leFormula (by
      dsimp only [leFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfailureCode :
      (binaryFormulaCode failureFormula).length <= syntaxResource :=
    hcode failureFormula (by
      dsimp only [failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hshortCode :
      (binaryFormulaCode shortFormula).length <= syntaxResource :=
    hcode shortFormula (by
      dsimp only [shortFormula, leFormula, failureFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfunctionCode :
      (binaryFormulaCode functionFormula).length <= syntaxResource :=
    hcode functionFormula (by
      dsimp only [functionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermTwoFunctionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hchoiceCode :
      (binaryFormulaCode choiceFormula).length <= syntaxResource :=
    hcode choiceFormula (by
      dsimp only [choiceFormula, shortFormula, leFormula, failureFormula,
        functionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermTwoFunctionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hselectedCode :
      (binaryFormulaCode (equalityFormula ⋏ choiceFormula)).length <=
        syntaxResource :=
    hcode (equalityFormula ⋏ choiceFormula) (by
      dsimp only [equalityFormula, choiceFormula, shortFormula, leFormula,
        failureFormula, functionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermTwoFunctionFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hequalityClosed : equalityFormula.freeVariables = ∅ :=
    syntaxTermNativeEqFormula_freeVariables_eq_empty witness.tag 2
  have hleClosed : leFormula.freeVariables = ∅ :=
    syntaxTermShortNativeLeFormula_freeVariables_eq_empty current.tokensCount 2
  have hfailureClosed : failureFormula.freeVariables = ∅ := by
    dsimp only [failureFormula]
    exact syntaxTermFailureClosedFormula_freeVariables_eq_empty tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
  have hfunctionClosed : functionFormula.freeVariables = ∅ := by
    dsimp only [functionFormula]
    unfold syntaxTermTwoFunctionFormula
    rw [compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment,
      compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment]
    simp only [LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_or,
      syntaxTermNativeShortLeFormula_freeVariables_eq_empty,
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
      compactAdditiveArithmeticFuncCodeValidExplicitFormula_freeVariables_eq_empty,
      compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_freeVariables_eq_empty,
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hshort :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral leCertificate
      failureCertificate
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)
      syntaxResource hleResource hfailureResource
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hleClosed hfailureClosed hleCode hfailureCode hshortCode
  have hchoice :=
    checkedHybridDisjunctionLeftPayloadBound_le_closedGeneral
      (right := functionFormula) shortCertificate
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaTermLeFixedPayloadPolynomial bitBound)
        (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound))
      syntaxResource hshort
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hleClosed,
          hfailureClosed]
        simp)
      hfunctionClosed hshortCode hfunctionCode hchoiceCode
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral equalityCertificate
      choiceCertificate
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (parserFormulaTermLeFixedPayloadPolynomial bitBound)
          (syntaxTermFailureFullyFixedPayloadPolynomial numericBound bitBound)))
      syntaxResource hequalityResource hchoice
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hequalityClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_or,
          LO.FirstOrder.Semiformula.freeVariables_and, hleClosed,
          hfailureClosed, hfunctionClosed]
        simp)
      hequalityCode hchoiceCode hselectedCode
  have hselectedFixed :
      hybridFormulaStructuralPayloadBound selectedCertificate <=
        syntaxTermTwoShortSelectedFullyFixedPayloadEnvelope numericBound
          bitBound := by
    dsimp only [selectedCertificate]
    simpa only [syntaxTermTwoShortSelectedFullyFixedPayloadEnvelope,
      syntaxResource] using hselected
  have hpath :=
    syntaxTermTwoFixedDecisionPathCertificate_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current next binderArity bitBound witness
      selectedCertificate
      (syntaxTermTwoShortSelectedFullyFixedPayloadEnvelope numericBound
        bitBound)
      hselectedFixed
      hsize
  simpa only [syntaxTermTwoShortFullyFixedDecisionCertificate,
    syntaxTermTwoShortDecisionFullyFixedPayloadEnvelope, equalityCertificate,
    leCertificate, failureCertificate, shortCertificate, choiceCertificate,
    selectedCertificate] using hpath

#print axioms
  syntaxTermTwoShortFullyFixedDecisionCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxTermTwoShortDecisionFullyFixedBounds
