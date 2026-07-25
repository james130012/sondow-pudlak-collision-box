import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoValidChoiceFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermTwoInvalidChoiceFixedBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds

/-! # Common fully fixed assembly of the selected Term tag-two branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermAtomicFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionEnvelopeFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

noncomputable def syntaxTermTwoFixedSelectedCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (choiceCertificate : TermHybridCertificate
      ((compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.argument) ⋎
       (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount))) :
    TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness) := by
  unfold syntaxTermTwoDecisionFormula syntaxTermTwoFunctionFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate witness.tag 2 htag)
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermTwoShortFormula tokenTable width tokenCount current
        next witness)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeShortLeCertificate 3 current.tokensCount hthree)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (by simp) hatFunction)
          choiceCertificate)))

theorem syntaxTermTwoDecisionFormula_freeVariables_eq_empty_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
      binderArity witness).freeVariables = ∅ := by
  unfold syntaxTermTwoDecisionFormula syntaxTermTwoShortFormula
    syntaxTermTwoFunctionFormula
  rw [compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment,
    compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment]
  simp only [LO.FirstOrder.Semiformula.freeVariables_and,
    LO.FirstOrder.Semiformula.freeVariables_or,
    syntaxTermNativeEqFormula_freeVariables_eq_empty,
    syntaxTermShortNativeLeFormula_freeVariables_eq_empty,
    syntaxTermNativeShortLeFormula_freeVariables_eq_empty,
    syntaxTermFailureClosedFormula_freeVariables_eq_empty,
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty,
    compactAdditiveArithmeticFuncCodeValidExplicitFormula_freeVariables_eq_empty,
    compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_freeVariables_eq_empty,
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed]
  simp

theorem syntaxTermTwoFixedSelectedCertificate_structuralPayloadBound_le_fullyFixed
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 <= current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (choiceCertificate : TermHybridCertificate
      ((compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.argument) ⋎
       (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
          witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount)))
    (choiceResource : Nat)
    (hchoice :
      hybridFormulaStructuralPayloadBound choiceCertificate <= choiceResource)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hfunctionCodeSize : Nat.size witness.functionCode <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermTwoFixedSelectedCertificate tokenTable width tokenCount
          current next binderArity witness htag hthree hatFunction
          choiceCertificate) <=
      syntaxTermTwoSelectedFixedPayloadEnvelope
        (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
          numericBound bitBound)
        choiceResource bitBound := by
  let equalityFormula := nativeEqFormula witness.tag 2
  let shortFormula := syntaxTermTwoShortFormula tokenTable width tokenCount
    current next witness
  let countFormula := nativeShortLeFormula 3 current.tokensCount
  let atFunctionFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.functionCode (fixedNumeralTerm 2)
  let choiceFormula :=
    (compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
        witness.functionCode ⋏
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount binderArity witness.argument) ⋎
    (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
        witness.functionCode ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
  let atFunctionTailFormula := atFunctionFormula ⋏ choiceFormula
  let functionFormula := countFormula ⋏ atFunctionTailFormula
  let shortFunctionFormula := shortFormula ⋎ functionFormula
  let syntaxResource := syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let equalityCertificate := nativeEqCertificate witness.tag 2 htag
  let countCertificate := nativeShortLeCertificate 3 current.tokensCount hthree
  let atFunctionCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2) (by simp) hatFunction
  let atFunctionTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atFunctionCertificate choiceCertificate
  let functionCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      atFunctionTailCertificate
  let shortFunctionCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := shortFormula) functionCertificate
  have hwidthSize : Nat.size width <= bitBound :=
    (Nat.size_le_size hwidth).trans hnumericSize
  have htokenCountSize : Nat.size tokenCount <= bitBound :=
    (Nat.size_le_size htokenCount).trans hnumericSize
  have hboundarySize : Nat.size current.tokensBoundary <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (4 : Fin 8)
  have hcountSize : Nat.size current.tokensCount <= bitBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentSize (5 : Fin 8)
  have hcountValue : current.tokensCount <= numericBound := by
    simpa [compactUnifiedParserStateCoordinateValues] using
      hcurrentValue (5 : Fin 8)
  have hequalityResource :=
    syntaxTermNativeEqCertificate_structuralPayloadBound_le_fixed witness.tag 2
      bitBound htag htagSize (by omega)
  have hcountResource :=
    syntaxTermNativeShortLeCertificate_structuralPayloadBound_le_fixed 3
      current.tokensCount bitBound hthree (by omega) hcountSize
  have hatFunctionResource :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode numericBound bitBound hatFunction hwidth
      htokenCount hcountValue htokenTableSize hwidthSize htokenCountSize
      hboundarySize hcountSize hfunctionCodeSize (by omega)
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
  have hshortCode :
      (binaryFormulaCode shortFormula).length <= syntaxResource :=
    hcode shortFormula (by
      dsimp only [shortFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermTwoShortFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hcountCode :
      (binaryFormulaCode countFormula).length <= syntaxResource :=
    hcode countFormula (by
      dsimp only [countFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hatFunctionCode :
      (binaryFormulaCode atFunctionFormula).length <= syntaxResource :=
    hcode atFunctionFormula (by
      dsimp only [atFunctionFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hchoiceCode :
      (binaryFormulaCode choiceFormula).length <= syntaxResource :=
    hcode choiceFormula (by
      dsimp only [choiceFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hatFunctionTailCode :
      (binaryFormulaCode atFunctionTailFormula).length <= syntaxResource :=
    hcode atFunctionTailFormula (by
      dsimp only [atFunctionTailFormula, atFunctionFormula, choiceFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hfunctionCode :
      (binaryFormulaCode functionFormula).length <= syntaxResource :=
    hcode functionFormula (by
      dsimp only [functionFormula, countFormula, atFunctionTailFormula,
        atFunctionFormula, choiceFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hshortFunctionCode :
      (binaryFormulaCode shortFunctionFormula).length <= syntaxResource :=
    hcode shortFunctionFormula (by
      dsimp only [shortFunctionFormula, shortFormula, functionFormula,
        countFormula, atFunctionTailFormula, atFunctionFormula, choiceFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermTwoShortFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hselectedCode :
      (binaryFormulaCode
        (equalityFormula ⋏ shortFunctionFormula)).length <= syntaxResource :=
    hcode (equalityFormula ⋏ shortFunctionFormula) (by
      dsimp only [equalityFormula, shortFunctionFormula, shortFormula,
        functionFormula, countFormula, atFunctionTailFormula,
        atFunctionFormula, choiceFormula]
      unfold compactUnifiedParserSyntaxTermDecisionExplicitFormula
        syntaxTermTwoShortFormula
      simp only [binaryFormulaCode, List.length_append]
      omega)
  have hequalityClosed : equalityFormula.freeVariables = ∅ :=
    syntaxTermNativeEqFormula_freeVariables_eq_empty witness.tag 2
  have hshortClosed : shortFormula.freeVariables = ∅ := by
    dsimp only [shortFormula]
    unfold syntaxTermTwoShortFormula
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortNativeLeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hcountClosed : countFormula.freeVariables = ∅ :=
    syntaxTermNativeShortLeFormula_freeVariables_eq_empty 3 current.tokensCount
  have hatFunctionClosed : atFunctionFormula.freeVariables = ∅ :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
      tokenTable width tokenCount current.tokensBoundary current.tokensCount
      witness.functionCode 2
  have hchoiceClosed : choiceFormula.freeVariables = ∅ := by
    dsimp only [choiceFormula]
    rw [compactAdditiveArithmeticFuncCodeValidClosedFormula_alignment,
      compactAdditiveArithmeticFuncCodeInvalidClosedFormula_alignment,
      LO.FirstOrder.Semiformula.freeVariables_or,
      LO.FirstOrder.Semiformula.freeVariables_and,
      LO.FirstOrder.Semiformula.freeVariables_and,
      compactAdditiveArithmeticFuncCodeValidExplicitFormula_freeVariables_eq_empty,
      compactAdditiveArithmeticFuncCodeInvalidExplicitFormula_freeVariables_eq_empty,
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula_freeVariables_eq_empty_fullyFixed,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hatFunctionTail :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral atFunctionCertificate
      choiceCertificate
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
        numericBound bitBound)
      choiceResource syntaxResource hatFunctionResource hchoice
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hatFunctionClosed hchoiceClosed hatFunctionCode hchoiceCode
      hatFunctionTailCode
  have hfunction :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
      atFunctionTailCertificate
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
          numericBound bitBound)
        choiceResource)
      syntaxResource hcountResource hatFunctionTail
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hcountClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hatFunctionClosed,
          hchoiceClosed]
        simp)
      hcountCode hatFunctionTailCode hfunctionCode
  have hshortFunction :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := shortFormula) functionCertificate
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaTermLeFixedPayloadPolynomial bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 2
            numericBound bitBound)
          choiceResource))
      syntaxResource hfunction
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hshortClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hatFunctionClosed,
          hchoiceClosed]
        simp)
      hshortCode hfunctionCode hshortFunctionCode
  have hselected :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral equalityCertificate
      shortFunctionCertificate
      (parserFormulaPositiveAtomicFixedPayloadPolynomial bitBound)
      (hybridDisjunctionGeneralPayloadEnvelope syntaxResource
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (parserFormulaTermLeFixedPayloadPolynomial bitBound)
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource
            (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial
              2 numericBound bitBound)
            choiceResource)))
      syntaxResource hequalityResource hshortFunction
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hequalityClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_or, hshortClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hatFunctionClosed,
          hchoiceClosed]
        simp)
      hequalityCode hshortFunctionCode hselectedCode
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        equalityCertificate shortFunctionCertificate) <= _
  simpa only [syntaxTermTwoSelectedFixedPayloadEnvelope, syntaxResource] using
    hselected

#print axioms
  syntaxTermTwoDecisionFormula_freeVariables_eq_empty_fullyFixed
#print axioms
  syntaxTermTwoFixedSelectedCertificate_structuralPayloadBound_le_fullyFixed

end FoundationCompactNumericListedDirectParserSyntaxTermTwoSelectedFixedBounds
