import integration.FoundationCompactNumericListedDirectParserSyntaxTermBranchFormulaFullyFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds

/-! # Fully fixed common assembly for every enough-input Term branch -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 600000

namespace FoundationCompactNumericListedDirectParserSyntaxTermEnoughBranchFullyFixedBounds

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
open FoundationCompactNumericListedDirectParserSyntaxTermBranchFormulaFullyFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaAtomicFixedBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureFormulaFixedBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexSyntaxFixedBounds
open FoundationCompactNumericListedDirectNatListAtRowsFixedNumeralIndexFullyFixedBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

def syntaxTermEnoughBranchFullyFixedPayloadEnvelope
    (decisionResource numericBound bitBound : Nat) : Nat :=
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let argumentDecision :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
        numericBound bitBound)
      decisionResource
  let tagTail :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
        numericBound bitBound)
      argumentDecision
  let enough :=
    hybridConjunctionGeneralPayloadEnvelope syntaxResource
      (parserFormulaTermLeFixedPayloadPolynomial bitBound) tagTail
  hybridDisjunctionGeneralPayloadEnvelope syntaxResource enough

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

noncomputable def syntaxTermEnoughFullyFixedBranchCertificate
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcount : 2 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.argument)
    (decisionCertificate : TermHybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness)) :
    TermHybridCertificate
      (compactUnifiedParserSyntaxTermBranchExplicitFormula tokenTable width
        tokenCount current next binderArity witness) := by
  unfold compactUnifiedParserSyntaxTermBranchExplicitFormula
  exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeShortLeCertificate 2 current.tokensCount hcount)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0) (by simp)
          hatTag)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
            (by simp) hatArgument)
          decisionCertificate)))

theorem
    syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity numericBound bitBound : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcount : 2 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (hatArgument : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 1 witness.argument)
    (decisionCertificate : TermHybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness))
    (decisionResource : Nat)
    (hdecision :
      hybridFormulaStructuralPayloadBound decisionCertificate <=
        decisionResource)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hcurrentValue :
      CompactUnifiedParserStateCoordinateValueBound current numericBound)
    (htokenTableSize : Nat.size tokenTable <= bitBound)
    (hcurrentSize :
      CompactUnifiedParserStateCoordinateSizeBound current bitBound)
    (htagSize : Nat.size witness.tag <= bitBound)
    (hargumentSize : Nat.size witness.argument <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hsize : forall coordinate : Fin 26,
      Nat.size
        (compactUnifiedParserSyntaxTermFormulaEnvironment tokenTable width
          tokenCount current next binderArity witness coordinate) <=
        bitBound) :
    hybridFormulaStructuralPayloadBound
        (syntaxTermEnoughFullyFixedBranchCertificate tokenTable width tokenCount
          current next binderArity witness hcount hatTag hatArgument
          decisionCertificate) <=
      syntaxTermEnoughBranchFullyFixedPayloadEnvelope decisionResource
        numericBound bitBound := by
  let shortFormula :=
    shortNativeLeFormula current.tokensCount 1 ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount
  let countFormula := nativeShortLeFormula 2 current.tokensCount
  let atTagFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.tag
      (fixedNumeralTerm 0)
  let atArgumentFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.argument
      (fixedNumeralTerm 1)
  let decisionFormula :=
    compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
      tokenCount current next binderArity witness
  let argumentDecisionFormula := atArgumentFormula ⋏ decisionFormula
  let tagTailFormula := atTagFormula ⋏ argumentDecisionFormula
  let enoughFormula := countFormula ⋏ tagTailFormula
  let syntaxResource :=
    syntaxTermFunctionDecisionFixedSyntaxPolynomial bitBound
  let countCertificate :=
    nativeShortLeCertificate 2 current.tokensCount hcount
  let atTagCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag (fixedNumeralTerm 0) (by simp) hatTag
  let atArgumentCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.argument (fixedNumeralTerm 1) (by simp) hatArgument
  let argumentDecisionCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atArgumentCertificate decisionCertificate
  let tagTailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction atTagCertificate
      argumentDecisionCertificate
  let enoughCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      tagTailCertificate
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
  have hcountResource :=
    syntaxTermNativeShortLeCertificate_structuralPayloadBound_le_fixed 2
      current.tokensCount bitBound hcount (by omega) hcountSize
  have hatTagResource :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag numericBound bitBound hatTag hwidth htokenCount hcountValue
      htokenTableSize hwidthSize htokenCountSize hboundarySize hcountSize
      htagSize (by omega)
  have hatArgumentResource :=
    compactAdditiveNatListAtRowsAtFixedNumeralIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_fullyFixed
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.argument numericBound bitBound hatArgument hwidth htokenCount
      hcountValue htokenTableSize hwidthSize htokenCountSize hboundarySize
      hcountSize hargumentSize (by omega)
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
  have hcountCode :
      (binaryFormulaCode countFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and countFormula
      tagTailFormula).trans henoughCode
  have htagTailCode :
      (binaryFormulaCode tagTailFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and countFormula
      tagTailFormula).trans henoughCode
  have hatTagCode :
      (binaryFormulaCode atTagFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and atTagFormula
      argumentDecisionFormula).trans htagTailCode
  have hargumentDecisionCode :
      (binaryFormulaCode argumentDecisionFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and atTagFormula
      argumentDecisionFormula).trans htagTailCode
  have hatArgumentCode :
      (binaryFormulaCode atArgumentFormula).length <= syntaxResource :=
    (binaryFormulaCode_left_length_le_and atArgumentFormula
      decisionFormula).trans hargumentDecisionCode
  have hdecisionCode :
      (binaryFormulaCode decisionFormula).length <= syntaxResource :=
    (binaryFormulaCode_right_length_le_and atArgumentFormula
      decisionFormula).trans hargumentDecisionCode
  have hcountClosed : countFormula.freeVariables = ∅ :=
    syntaxTermNativeShortLeFormula_freeVariables_eq_empty 2 current.tokensCount
  have hatTagClosed : atTagFormula.freeVariables = ∅ := by
    dsimp only [atTagFormula]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        witness.tag 0
  have hatArgumentClosed : atArgumentFormula.freeVariables = ∅ := by
    dsimp only [atArgumentFormula]
    exact
      compactAdditiveNatListAtRowsAtFixedNumeralIndexFormula_freeVariables_eq_empty
        tokenTable width tokenCount current.tokensBoundary current.tokensCount
        witness.argument 1
  have hdecisionClosed : decisionFormula.freeVariables = ∅ := by
    dsimp only [decisionFormula]
    exact
      compactUnifiedParserSyntaxTermDecisionExplicitFormula_freeVariables_eq_empty_fullyFixed
        tokenTable width tokenCount current next binderArity witness
  have hshortClosed : shortFormula.freeVariables = ∅ := by
    dsimp only [shortFormula]
    rw [LO.FirstOrder.Semiformula.freeVariables_and,
      syntaxTermShortNativeLeFormula_freeVariables_eq_empty,
      syntaxTermFailureClosedFormula_freeVariables_eq_empty]
    simp
  have hargumentDecision :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral
      atArgumentCertificate decisionCertificate
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
        numericBound bitBound)
      decisionResource syntaxResource hatArgumentResource hdecision
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hatArgumentClosed hdecisionClosed hatArgumentCode hdecisionCode
      hargumentDecisionCode
  have htagTail :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral atTagCertificate
      argumentDecisionCertificate
      (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
        numericBound bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
          numericBound bitBound)
        decisionResource)
      syntaxResource hatTagResource hargumentDecision
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hatTagClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hatArgumentClosed,
          hdecisionClosed]
        simp)
      hatTagCode hargumentDecisionCode htagTailCode
  have henough :=
    checkedHybridConjunctionPayloadBound_le_closedGeneral countCertificate
      tagTailCertificate
      (parserFormulaTermLeFixedPayloadPolynomial bitBound)
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
          numericBound bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 1
            numericBound bitBound)
          decisionResource))
      syntaxResource hcountResource htagTail
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hcountClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hatTagClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hatArgumentClosed,
          hdecisionClosed]
        simp)
      hcountCode htagTailCode henoughCode
  have hbranch :=
    checkedHybridDisjunctionRightPayloadBound_le_closedGeneral
      (left := shortFormula) enoughCertificate
      (hybridConjunctionGeneralPayloadEnvelope syntaxResource
        (parserFormulaTermLeFixedPayloadPolynomial bitBound)
        (hybridConjunctionGeneralPayloadEnvelope syntaxResource
          (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial 0
            numericBound bitBound)
          (hybridConjunctionGeneralPayloadEnvelope syntaxResource
            (compactAdditiveNatListAtRowsFixedNumeralFullyFixedPayloadPolynomial
              1 numericBound bitBound)
            decisionResource)))
      syntaxResource henough
      (syntaxTermFunctionDecisionFixedSyntaxPolynomial_positive bitBound)
      hshortClosed (by
        rw [LO.FirstOrder.Semiformula.freeVariables_and, hcountClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hatTagClosed,
          LO.FirstOrder.Semiformula.freeVariables_and, hatArgumentClosed,
          hdecisionClosed]
        simp)
      hshortCode henoughCode hbranchCode
  unfold syntaxTermEnoughFullyFixedBranchCertificate
  change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (left := shortFormula) enoughCertificate) <= _
  simpa only [syntaxTermEnoughBranchFullyFixedPayloadEnvelope,
    syntaxResource] using hbranch

#print axioms
  syntaxTermEnoughFullyFixedBranchCertificate_structuralPayloadBound_le

end FoundationCompactNumericListedDirectParserSyntaxTermEnoughBranchFullyFixedBounds
