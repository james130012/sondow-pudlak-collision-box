import integration.FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds

/-!
# Selected public resources for the syntax-formula transition

This layer combines the checked branch leaves with the five-way tag path and
the empty/enough outer split.  The expensive leaf proofs remain in the base
public-bounds module.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 300000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxFormulaSelectedPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaRows
open FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBranchPublicBounds
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaBinaryPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxFormulaQuantifierPublicBounds
open FoundationCompactNumericListedDirectArithmeticRelCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticRelCodeValidPublicBounds

private abbrev formulaZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxFormulaExplicitHybridCertificate.zeroValuation

private abbrev natListAtZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation

private abbrev fixedNumeralTerm (value : Nat) : ValuationTerm :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
    value

private abbrev FormulaHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate formulaZeroValuation formula

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  unfold fixedNumeralTerm
  unfold
    FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.fixedNumeralTerm
  simp [LO.FirstOrder.Semiterm.Operator.operator]

private theorem natListAtFixedNumeralTerm_value (value : Nat) :
    termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        (fixedNumeralTerm value) = value := by
  simp

noncomputable def syntaxFormulaLogicalTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 2 3)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 2 ⋎
    nativeEqFormula witness.tag 3
  let continueFormula :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 1
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula continueFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 2 3 htag)
    (compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 1
      hcontinue)
  syntaxFormulaTagLogicalPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness selectedResource

noncomputable def syntaxFormulaBinaryTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 4 5)
    (hbinary : CompactUnifiedParserSyntaxFormulaBinaryRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount
      binderArity) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 4 ⋎
    nativeEqFormula witness.tag 5
  let binaryFormula := compactUnifiedParserSyntaxFormulaBinaryClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula binaryFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 4 5 htag)
    (compactUnifiedParserSyntaxFormulaBinaryGraphPayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity hbinary)
  syntaxFormulaTagBinaryPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness selectedResource

noncomputable def syntaxFormulaQuantifierTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (htag : NativeEqEitherCheckedData witness.tag 6 7)
    (hquantifier : CompactUnifiedParserSyntaxFormulaQuantifierRows tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity) : Nat :=
  let tagFormula := nativeEqFormula witness.tag 6 ⋎
    nativeEqFormula witness.tag 7
  let quantifierFormula :=
    compactUnifiedParserSyntaxFormulaQuantifierClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation tagFormula quantifierFormula
    (syntaxFormulaNativeEqEitherPayloadEnvelope witness.tag 6 7 htag)
    (compactUnifiedParserSyntaxFormulaQuantifierGraphPayloadEnvelope tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity hquantifier)
  syntaxFormulaTagQuantifierPathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness selectedResource

noncomputable def syntaxFormulaInvalidTagBranchPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let ne7Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 7) failureFormula
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 7)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  let ne6Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 6)
    (nativeNeFormula witness.tag 7 ⋏ failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 6) ne7Tail
  let ne5Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 5)
    (nativeNeFormula witness.tag 6 ⋏ nativeNeFormula witness.tag 7 ⋏
      failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 5) ne6Tail
  let ne4Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 4)
    (nativeNeFormula witness.tag 5 ⋏ nativeNeFormula witness.tag 6 ⋏
      nativeNeFormula witness.tag 7 ⋏ failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 4) ne5Tail
  let ne3Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 3)
    (nativeNeFormula witness.tag 4 ⋏ nativeNeFormula witness.tag 5 ⋏
      nativeNeFormula witness.tag 6 ⋏ nativeNeFormula witness.tag 7 ⋏
      failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 3) ne4Tail
  let ne2Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 2)
    (nativeNeFormula witness.tag 3 ⋏ nativeNeFormula witness.tag 4 ⋏
      nativeNeFormula witness.tag 5 ⋏ nativeNeFormula witness.tag 6 ⋏
      nativeNeFormula witness.tag 7 ⋏ failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 2) ne3Tail
  let ne1Tail := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 1)
    (nativeNeFormula witness.tag 2 ⋏ nativeNeFormula witness.tag 3 ⋏
      nativeNeFormula witness.tag 4 ⋏ nativeNeFormula witness.tag 5 ⋏
      nativeNeFormula witness.tag 6 ⋏ nativeNeFormula witness.tag 7 ⋏
      failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 1) ne2Tail
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeNeFormula witness.tag 0)
    (nativeNeFormula witness.tag 1 ⋏ nativeNeFormula witness.tag 2 ⋏
      nativeNeFormula witness.tag 3 ⋏ nativeNeFormula witness.tag 4 ⋏
      nativeNeFormula witness.tag 5 ⋏ nativeNeFormula witness.tag 6 ⋏
      nativeNeFormula witness.tag 7 ⋏ failureFormula)
    (syntaxFormulaNativeNePayloadPolynomial witness.tag 0) ne1Tail
  syntaxFormulaTagInvalidPathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness selectedResource

def syntaxFormulaEmptyOuterPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (failureResource : Nat) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let emptyFormula := nativeEqFormula current.tokensCount 0 ⋏ failureFormula
  let enoughFormula := nativeShortLeFormula 1 current.tokensCount ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.tag
      (fixedNumeralTerm 0) ⋏
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation (nativeEqFormula current.tokensCount 0)
    failureFormula
    (syntaxFormulaNativeEqPayloadPolynomial current.tokensCount 0)
    failureResource
  transparentHybridDisjunctionLeftPayloadEnvelope formulaZeroValuation
    emptyFormula enoughFormula selectedResource

def syntaxFormulaEnoughOuterPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (atTagResource tagBranchResource : Nat) : Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount
  let emptyFormula := nativeEqFormula current.tokensCount 0 ⋏ failureFormula
  let countFormula := nativeShortLeFormula 1 current.tokensCount
  let atTagFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.tag
      (fixedNumeralTerm 0)
  let tagBranchFormula :=
    compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable width
      tokenCount current next binderArity witness
  let tagTailResource := transparentHybridConjunctionPayloadEnvelope
    natListAtZeroValuation atTagFormula tagBranchFormula atTagResource
      tagBranchResource
  let selectedResource := transparentHybridConjunctionPayloadEnvelope
    formulaZeroValuation countFormula (atTagFormula ⋏ tagBranchFormula)
    (syntaxFormulaNativeShortLePayloadEnvelope 1 current.tokensCount)
    tagTailResource
  transparentHybridDisjunctionRightPayloadEnvelope formulaZeroValuation
    emptyFormula (countFormula ⋏ atTagFormula ⋏ tagBranchFormula)
    selectedResource

theorem syntaxFormulaEmptyOuterPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : current.tokensCount = 0)
    (failureCertificate : FormulaHybridCertificate
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount))
    (failureResource : Nat)
    (hfailure : hybridFormulaStructuralPayloadBound failureCertificate <=
      failureResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := nativeShortLeFormula 1 current.tokensCount ⋏
            compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
              tokenCount current.tokensBoundary current.tokensCount witness.tag
              (fixedNumeralTerm 0) ⋏
            compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
              tokenTable width tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqCertificate current.tokensCount 0 hcount)
            failureCertificate)) <=
      syntaxFormulaEmptyOuterPayloadEnvelope tokenTable width tokenCount current
        next binderArity witness failureResource := by
  have hcountResource := nativeEqCertificate_structuralPayloadBound_le_public
    current.tokensCount 0 hcount
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    (nativeEqCertificate current.tokensCount 0 hcount) failureCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    (nativeEqCertificate current.tokensCount 0 hcount) failureCertificate _ _
    hcountResource hfailure
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := nativeShortLeFormula 1 current.tokensCount ⋏
      compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.tag
        (fixedNumeralTerm 0) ⋏
      compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness)
    selected _ hselected
  unfold syntaxFormulaEmptyOuterPayloadEnvelope
  simpa only [selected] using houter

theorem syntaxFormulaEnoughOuterPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (hcount : 1 <= current.tokensCount)
    (hatTag : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 0 witness.tag)
    (tagBranchCertificate : FormulaHybridCertificate
      (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
        width tokenCount current next binderArity witness))
    (tagBranchResource : Nat)
    (htagBranch : hybridFormulaStructuralPayloadBound tagBranchCertificate <=
      tagBranchResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := nativeEqFormula current.tokensCount 0 ⋏
            compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
              tokenCount current next witness.tailBoundary witness.tailCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <=
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        tagBranchResource := by
  have hindexClosed : (fixedNumeralTerm 0).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  let countCertificate := nativeShortLeCertificate 1 current.tokensCount hcount
  let atTagCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag (fixedNumeralTerm 0) (natListAtFixedNumeralTerm_value 0)
      hatTag
  have hcountResource :=
    nativeShortLeCertificate_structuralPayloadBound_le_public 1
      current.tokensCount hcount
  have hatTagResource :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag (fixedNumeralTerm 0) hindexClosed
      (natListAtFixedNumeralTerm_value 0) hatTag
  let tagTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    atTagCertificate tagBranchCertificate
  have htagTail := transparentHybridConjunctionPayloadBound_le atTagCertificate
    tagBranchCertificate _ _ hatTagResource htagBranch
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate tagTail
  have hselected := transparentHybridConjunctionPayloadBound_le countCertificate
    tagTail _ _ hcountResource htagTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := nativeEqFormula current.tokensCount 0 ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
    selected _ hselected
  unfold syntaxFormulaEnoughOuterPayloadEnvelope
  exact houter

noncomputable def compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) : Nat :=
  match data with
  | .empty _ hfailure =>
      syntaxFormulaEmptyOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable
          width tokenCount current next witness.tailBoundary witness.tailCount
          hfailure)
  | .relationShort _ hatTag htag _ hfailure =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness htag
          (syntaxFormulaRelationShortBodyPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hfailure))
  | .relationValid _ hatTag htag _ hatArity hatCode _ hfunction =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness htag
          (syntaxFormulaRelationValidBodyPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hatArity hatCode
            hfunction))
  | .relationInvalid _ hatTag htag _ hatArity hatCode _ hfailure =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness htag
          (syntaxFormulaRelationInvalidBodyPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hatArity hatCode
            hfailure))
  | .logical _ hatTag htag hcontinue =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaLogicalTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness htag hcontinue)
  | .binary _ hatTag htag hbinary =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaBinaryTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness htag hbinary)
  | .quantifier _ hatTag htag hquantifier =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaQuantifierTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness htag hquantifier)
  | .invalidTag _ hatTag _ _ _ _ _ _ _ _ hfailure =>
      syntaxFormulaEnoughOuterPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
          tokenTable width tokenCount current.tokensBoundary
          current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
          (natListAtFixedNumeralTerm_value 0) hatTag)
        (syntaxFormulaInvalidTagBranchPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)

theorem
    compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxFormulaTaskWitnessCoordinates)
    (data : CompactSyntaxFormulaCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    @hybridFormulaStructuralPayloadBound formulaZeroValuation
        (compactUnifiedParserSyntaxFormulaBranchExplicitFormula tokenTable width
          tokenCount current next binderArity witness)
        (compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness data) <=
      compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData tokenTable
        width tokenCount current next binderArity witness data := by
  cases data with
  | empty hcount hfailure =>
      let failureCertificate :=
        compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure
      have hfailureResource :=
        compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure
      have houter := syntaxFormulaEmptyOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount failureCertificate
        (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable
          width tokenCount current next witness.tailBoundary witness.tailCount
          hfailure) hfailureResource
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeEqCertificate current.tokensCount 0 hcount)
            failureCertificate)) <= _
      exact houter
  | relationShort hcount hatTag htag hshort hfailure =>
      let failureCertificate :=
        compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure
      let bodyCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            tokenTable width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortNativeLeCertificate current.tokensCount 2 hshort)
            failureCertificate)
      have hbodyRaw := syntaxFormulaRelationShortBodyPayloadBound_le_public
        tokenTable width tokenCount current next binderArity witness hshort
        hfailure
      have hbody : hybridFormulaStructuralPayloadBound bodyCertificate <=
          syntaxFormulaRelationShortBodyPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hfailure := by
        unfold bodyCertificate
        exact hbodyRaw
      let selected : FormulaHybridCertificate
          (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
            current next binderArity witness) := by
        unfold syntaxFormulaRelationSelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
          bodyCertificate
      have htagResource :=
        nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
          witness.tag 0 1 htag
      have hselected := transparentHybridConjunctionPayloadBound_le
        (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
        bodyCertificate _ _ htagResource hbody
      have hpath := syntaxFormulaTagRelationPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          selected
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness htag
            (syntaxFormulaRelationShortBodyPayloadEnvelope tokenTable width
              tokenCount current next binderArity witness hfailure) := by
        unfold tagBranchCertificate syntaxFormulaRelationTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter
  | relationValid hcount hatTag htag hthree hatArity hatCode hvalid
      hfunction =>
      let bodyCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            tokenTable width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 1 witness.relationArity
                (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                hatArity)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.relationCode
                  (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                  hatCode)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticRelCodeValidExplicitHybridCertificateOfGraph
                      witness.relationArity witness.relationCode hvalid)
                    (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount binderArity
                      witness.relationArity hfunction))))))
      have hbodyRaw := syntaxFormulaRelationValidBodyPayloadBound_le_public
        tokenTable width tokenCount current next binderArity witness hthree
        hatArity hatCode hvalid hfunction
      have hbody : hybridFormulaStructuralPayloadBound bodyCertificate <=
          syntaxFormulaRelationValidBodyPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hatArity hatCode
            hfunction := by
        unfold bodyCertificate
        exact hbodyRaw
      let selected : FormulaHybridCertificate
          (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
            current next binderArity witness) := by
        unfold syntaxFormulaRelationSelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
          bodyCertificate
      have htagResource :=
        nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
          witness.tag 0 1 htag
      have hselected := transparentHybridConjunctionPayloadBound_le
        (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
        bodyCertificate _ _ htagResource hbody
      have hpath := syntaxFormulaTagRelationPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          selected
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness htag
            (syntaxFormulaRelationValidBodyPayloadEnvelope tokenTable width
              tokenCount current next binderArity witness hatArity hatCode
              hfunction) := by
        unfold tagBranchCertificate syntaxFormulaRelationTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter
  | relationInvalid hcount hatTag htag hthree hatArity hatCode hinvalid
      hfailure =>
      let bodyCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
            tokenTable width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaRelationBodyExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 1 witness.relationArity
                (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                hatArity)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.relationCode
                  (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                  hatCode)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticRelCodeInvalidExplicitHybridCertificateOfGraph
                      witness.relationArity witness.relationCode hinvalid)
                    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount hfailure))))))
      have hbodyRaw := syntaxFormulaRelationInvalidBodyPayloadBound_le_public
        tokenTable width tokenCount current next binderArity witness hthree
        hatArity hatCode hinvalid hfailure
      have hbody : hybridFormulaStructuralPayloadBound bodyCertificate <=
          syntaxFormulaRelationInvalidBodyPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hatArity hatCode
            hfailure := by
        unfold bodyCertificate
        exact hbodyRaw
      let selected : FormulaHybridCertificate
          (syntaxFormulaRelationSelectedFormula tokenTable width tokenCount
            current next binderArity witness) := by
        unfold syntaxFormulaRelationSelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
          bodyCertificate
      have htagResource :=
        nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
          witness.tag 0 1 htag
      have hselected := transparentHybridConjunctionPayloadBound_le
        (nativeEqEitherCertificateFromData witness.tag 0 1 htag)
        bodyCertificate _ _ htagResource hbody
      have hpath := syntaxFormulaTagRelationPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          selected
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaRelationTagBranchPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness htag
            (syntaxFormulaRelationInvalidBodyPayloadEnvelope tokenTable width
              tokenCount current next binderArity witness hatArity hatCode
              hfailure) := by
        unfold tagBranchCertificate syntaxFormulaRelationTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter
  | logical hcount hatTag htag hcontinue =>
      let continueCertificate :=
        compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount 1 hcontinue
      let selected : FormulaHybridCertificate
          (syntaxFormulaLogicalSelectedFormula tokenTable width tokenCount
            current next witness) := by
        unfold syntaxFormulaLogicalSelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
          continueCertificate
      have htagResource :=
        nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
          witness.tag 2 3 htag
      have hcontinueResource :=
        compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount 1 hcontinue
      have hselected := transparentHybridConjunctionPayloadBound_le
        (nativeEqEitherCertificateFromData witness.tag 2 3 htag)
        continueCertificate _ _ htagResource hcontinueResource
      have hpath := syntaxFormulaTagLogicalPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            selected)
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaLogicalTagBranchPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness htag hcontinue := by
        unfold tagBranchCertificate syntaxFormulaLogicalTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter
  | binary hcount hatTag htag hbinary =>
      let binaryCertificate :=
        compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity hbinary
      let selected : FormulaHybridCertificate
          (syntaxFormulaBinarySelectedFormula tokenTable width tokenCount
            current next binderArity witness) := by
        unfold syntaxFormulaBinarySelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
          binaryCertificate
      have htagResource :=
        nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
          witness.tag 4 5 htag
      have hbinaryResource :=
        compactUnifiedParserSyntaxFormulaBinaryExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity hbinary
      have hselected := transparentHybridConjunctionPayloadBound_le
        (nativeEqEitherCertificateFromData witness.tag 4 5 htag)
        binaryCertificate _ _ htagResource hbinaryResource
      have hpath := syntaxFormulaTagBinaryPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              selected))
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaBinaryTagBranchPayloadEnvelope tokenTable width tokenCount
            current next binderArity witness htag hbinary := by
        unfold tagBranchCertificate syntaxFormulaBinaryTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter
  | quantifier hcount hatTag htag hquantifier =>
      let quantifierCertificate :=
        compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity hquantifier
      let selected : FormulaHybridCertificate
          (syntaxFormulaQuantifierSelectedFormula tokenTable width tokenCount
            current next binderArity witness) := by
        unfold syntaxFormulaQuantifierSelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
          quantifierCertificate
      have htagResource :=
        nativeEqEitherCertificateFromData_structuralPayloadBound_le_public
          witness.tag 6 7 htag
      have hquantifierResource :=
        compactUnifiedParserSyntaxFormulaQuantifierExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity hquantifier
      have hselected := transparentHybridConjunctionPayloadBound_le
        (nativeEqEitherCertificateFromData witness.tag 6 7 htag)
        quantifierCertificate _ _ htagResource hquantifierResource
      have hpath := syntaxFormulaTagQuantifierPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                selected)))
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaQuantifierTagBranchPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness htag hquantifier := by
        unfold tagBranchCertificate
          syntaxFormulaQuantifierTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter
  | invalidTag hcount hatTag hne0 hne1 hne2 hne3 hne4 hne5 hne6 hne7
      hfailure =>
      let ne0Certificate := nativeNeCertificate witness.tag 0 hne0
      let ne1Certificate := nativeNeCertificate witness.tag 1 hne1
      let ne2Certificate := nativeNeCertificate witness.tag 2 hne2
      let ne3Certificate := nativeNeCertificate witness.tag 3 hne3
      let ne4Certificate := nativeNeCertificate witness.tag 4 hne4
      let ne5Certificate := nativeNeCertificate witness.tag 5 hne5
      let ne6Certificate := nativeNeCertificate witness.tag 6 hne6
      let ne7Certificate := nativeNeCertificate witness.tag 7 hne7
      let failureCertificate :=
        compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure
      have hne0Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 0 hne0
      have hne1Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 1 hne1
      have hne2Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 2 hne2
      have hne3Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 3 hne3
      have hne4Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 4 hne4
      have hne5Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 5 hne5
      have hne6Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 6 hne6
      have hne7Resource := nativeNeCertificate_structuralPayloadBound_le_public
        witness.tag 7 hne7
      have hfailureResource :=
        compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure
      let ne7Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne7Certificate failureCertificate
      have hne7Tail := transparentHybridConjunctionPayloadBound_le
        ne7Certificate failureCertificate _ _ hne7Resource hfailureResource
      let ne6Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne6Certificate ne7Tail
      have hne6Tail := transparentHybridConjunctionPayloadBound_le
        ne6Certificate ne7Tail _ _ hne6Resource hne7Tail
      let ne5Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne5Certificate ne6Tail
      have hne5Tail := transparentHybridConjunctionPayloadBound_le
        ne5Certificate ne6Tail _ _ hne5Resource hne6Tail
      let ne4Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne4Certificate ne5Tail
      have hne4Tail := transparentHybridConjunctionPayloadBound_le
        ne4Certificate ne5Tail _ _ hne4Resource hne5Tail
      let ne3Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne3Certificate ne4Tail
      have hne3Tail := transparentHybridConjunctionPayloadBound_le
        ne3Certificate ne4Tail _ _ hne3Resource hne4Tail
      let ne2Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne2Certificate ne3Tail
      have hne2Tail := transparentHybridConjunctionPayloadBound_le
        ne2Certificate ne3Tail _ _ hne2Resource hne3Tail
      let ne1Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
        ne1Certificate ne2Tail
      have hne1Tail := transparentHybridConjunctionPayloadBound_le
        ne1Certificate ne2Tail _ _ hne1Resource hne2Tail
      let selected : FormulaHybridCertificate
          (syntaxFormulaInvalidTagSelectedFormula tokenTable width tokenCount
            current next witness) := by
        unfold syntaxFormulaInvalidTagSelectedFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
          ne0Certificate ne1Tail
      have hselected := transparentHybridConjunctionPayloadBound_le
        ne0Certificate ne1Tail _ _ hne0Resource hne1Tail
      have hpath := syntaxFormulaTagInvalidPathPayloadBound_le tokenTable width
        tokenCount current next binderArity witness selected _ hselected
      let tagBranchCertificate : FormulaHybridCertificate
          (compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula tokenTable
            width tokenCount current next binderArity witness) := by
        unfold compactUnifiedParserSyntaxFormulaTagBranchExplicitFormula
        exact CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                selected)))
      have htagBranch : hybridFormulaStructuralPayloadBound
            tagBranchCertificate <=
          syntaxFormulaInvalidTagBranchPayloadEnvelope tokenTable width
            tokenCount current next binderArity witness hfailure := by
        unfold tagBranchCertificate syntaxFormulaInvalidTagBranchPayloadEnvelope
        exact hpath
      have houter := syntaxFormulaEnoughOuterPayloadBound_le tokenTable width
        tokenCount current next binderArity witness hcount hatTag
        tagBranchCertificate _ htagBranch
      unfold
        compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxFormulaBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 1 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              tagBranchCertificate))) <= _
      exact houter

#print axioms syntaxFormulaEmptyOuterPayloadBound_le
#print axioms syntaxFormulaEnoughOuterPayloadBound_le
#print axioms
  compactUnifiedParserSyntaxFormulaBranchExplicitHybridCertificateFromData_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxFormulaSelectedPublicBounds
