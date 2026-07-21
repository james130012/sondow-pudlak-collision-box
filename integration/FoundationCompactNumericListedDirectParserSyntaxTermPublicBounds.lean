import integration.FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
import integration.FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
import integration.FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
import integration.FoundationCompactNumericListedDirectArithmeticFuncCodeValidPublicBounds
import integration.FoundationCompactPAValuationAtomicCompilerPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for the complete syntax-term transition

The selected semantic branch is represented by checked Type-level data.  Each
atomic comparison and child parser certificate is charged by its public
resource before the original conjunction/disjunction tree is reassembled.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactArithmeticSymbolCode
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationAtomicCompilerPublicBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactNumericListedDirectParserStateFormula
open FoundationCompactNumericListedDirectParserSyntaxTermRows
open FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermContinueExplicitHybridCertificate
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRows
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate
open FoundationCompactNumericListedDirectBinaryNatStatusPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListUnconsRowsPublicBounds
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFailureRowsPublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermContinuePublicBounds
open FoundationCompactNumericListedDirectParserSyntaxTermFunctionPublicBounds
open FoundationCompactNumericListedDirectArithmeticFuncCodeValidPublicBounds

private abbrev termZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectParserSyntaxTermExplicitHybridCertificate.zeroValuation

private abbrev TermHybridCertificate (formula : ValuationFormula) :=
  CheckedHybridValuationBoundedFormulaCertificate termZeroValuation formula

private theorem fixedNumeralTerm_freeVariables_eq_empty (value : Nat) :
    (fixedNumeralTerm value).freeVariables = ∅ := by
  simp [fixedNumeralTerm, LO.FirstOrder.Semiterm.Operator.operator]

private theorem natListAtFixedNumeralTerm_value (value : Nat) :
    termValue
        FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
        (fixedNumeralTerm value) = value := by
  simp

def syntaxTermNativeEqPayloadPolynomial (value expected : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial termZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]

theorem nativeEqCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (heq : value = expected) :
    hybridFormulaStructuralPayloadBound
        (nativeEqCertificate value expected heq) ≤
      syntaxTermNativeEqPayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (fixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    termZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] hleft hright
  change compilePositiveRelationPayloadResource termZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] ≤ _
  exact hpublic

def syntaxTermNativeNePayloadPolynomial (value expected : Nat) : Nat :=
  compileNegativeRelationPayloadPolynomial termZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected]

theorem nativeNeCertificate_structuralPayloadBound_le_public
    (value expected : Nat) (hne : value ≠ expected) :
    hybridFormulaStructuralPayloadBound
        (nativeNeCertificate value expected hne) ≤
      syntaxTermNativeNePayloadPolynomial value expected := by
  have hleft : (shortBinaryNumeralTerm value).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (fixedNumeralTerm expected).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compileNegativeRelationPayloadResource_le_publicPolynomial
    termZeroValuation Language.Eq.eq
    ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] hleft hright
  change compileNegativeRelationPayloadResource termZeroValuation
      Language.Eq.eq
      ![shortBinaryNumeralTerm value, fixedNumeralTerm expected] ≤ _
  exact hpublic

def syntaxTermShortLtPayloadPolynomial (left right : Nat) : Nat :=
  compilePositiveRelationPayloadPolynomial termZeroValuation
    Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right]

theorem shortLtCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hlt : left < right) :
    hybridFormulaStructuralPayloadBound
        (shortLtCertificate left right hlt) ≤
      syntaxTermShortLtPayloadPolynomial left right := by
  have hleft : (shortBinaryNumeralTerm left).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hright : (shortBinaryNumeralTerm right).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hpublic := compilePositiveRelationPayloadResource_le_publicPolynomial
    termZeroValuation Language.ORing.Rel.lt
    ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] hleft hright
  change compilePositiveRelationPayloadResource termZeroValuation
      Language.ORing.Rel.lt
      ![shortBinaryNumeralTerm left, shortBinaryNumeralTerm right] ≤ _
  exact hpublic

def syntaxTermLePayloadEnvelope
    (left right : Nat) (leftTerm rightTerm : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  let equalityFormula := Semiformula.rel Language.Eq.eq args
  let strictFormula := Semiformula.rel Language.LT.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables termZeroValuation
  compilePositiveRelationPayloadPolynomial termZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadPolynomial termZeroValuation
      Language.ORing.Rel.lt args +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert equalityFormula Gamma) +
    FoundationCompactCertifiedContextualModusPonens.weakeningFullAssemblyCost
      (insert strictFormula Gamma) +
    FoundationCompactCertifiedContextProof.CertifiedPAContextProof.disjunctionFullAssemblyCost
      Gamma equalityFormula strictFormula

theorem termLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (leftTerm rightTerm : ValuationTerm)
    (hleftClosed : leftTerm.freeVariables ⊆ {0})
    (hrightClosed : rightTerm.freeVariables ⊆ {0})
    (hleft : termValue termZeroValuation leftTerm = left)
    (hright : termValue termZeroValuation rightTerm = right)
    (hle : left ≤ right) :
    hybridFormulaStructuralPayloadBound
        (termLeCertificate left right leftTerm rightTerm hleft hright hle) ≤
      syntaxTermLePayloadEnvelope left right leftTerm rightTerm := by
  let args : Fin 2 -> ValuationTerm := ![leftTerm, rightTerm]
  have hequality :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      termZeroValuation Language.Eq.eq args hleftClosed hrightClosed
  have hstrict :=
    compilePositiveRelationPayloadResource_le_publicPolynomial
      termZeroValuation Language.ORing.Rel.lt args hleftClosed hrightClosed
  by_cases heq : left = right
  · simp only [termLeCertificate, termLeFormula, id_eq]
    rw [dif_pos heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold syntaxTermLePayloadEnvelope
    dsimp only [args, termZeroValuation] at hequality hstrict ⊢
    omega
  · simp only [termLeCertificate, termLeFormula, id_eq]
    rw [dif_neg heq]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold syntaxTermLePayloadEnvelope
    dsimp only [args, termZeroValuation] at hequality hstrict ⊢
    omega

def syntaxTermShortLePayloadEnvelope (left right : Nat) : Nat :=
  syntaxTermLePayloadEnvelope left right (shortBinaryNumeralTerm left)
    (shortBinaryNumeralTerm right)

theorem shortLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hle : left ≤ right) :
    hybridFormulaStructuralPayloadBound
        (shortLeCertificate left right hle) ≤
      syntaxTermShortLePayloadEnvelope left right := by
  have hleftClosed : (shortBinaryNumeralTerm left).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : (shortBinaryNumeralTerm right).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  simpa only [shortLeCertificate, shortLeFormula, id_eq,
    syntaxTermShortLePayloadEnvelope] using
    termLeCertificate_structuralPayloadBound_le_public left right
      (shortBinaryNumeralTerm left) (shortBinaryNumeralTerm right)
      hleftClosed hrightClosed (by simp [termValue_shortBinaryNumeralTerm])
      (by simp [termValue_shortBinaryNumeralTerm]) hle

def syntaxTermShortNativeLePayloadEnvelope (left right : Nat) : Nat :=
  syntaxTermLePayloadEnvelope left right (shortBinaryNumeralTerm left)
    (fixedNumeralTerm right)

theorem shortNativeLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hle : left ≤ right) :
    hybridFormulaStructuralPayloadBound
        (shortNativeLeCertificate left right hle) ≤
      syntaxTermShortNativeLePayloadEnvelope left right := by
  have hleftClosed : (shortBinaryNumeralTerm left).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : (fixedNumeralTerm right).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  simpa only [shortNativeLeCertificate, shortNativeLeFormula, id_eq,
    syntaxTermShortNativeLePayloadEnvelope] using
    termLeCertificate_structuralPayloadBound_le_public left right
      (shortBinaryNumeralTerm left) (fixedNumeralTerm right)
      hleftClosed hrightClosed (by simp [termValue_shortBinaryNumeralTerm])
      (by simp) hle

def syntaxTermNativeShortLePayloadEnvelope (left right : Nat) : Nat :=
  syntaxTermLePayloadEnvelope left right (fixedNumeralTerm left)
    (shortBinaryNumeralTerm right)

theorem nativeShortLeCertificate_structuralPayloadBound_le_public
    (left right : Nat) (hle : left ≤ right) :
    hybridFormulaStructuralPayloadBound
        (nativeShortLeCertificate left right hle) ≤
      syntaxTermNativeShortLePayloadEnvelope left right := by
  have hleftClosed : (fixedNumeralTerm left).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hrightClosed : (shortBinaryNumeralTerm right).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  simpa only [nativeShortLeCertificate, nativeShortLeFormula, id_eq,
    syntaxTermNativeShortLePayloadEnvelope] using
    termLeCertificate_structuralPayloadBound_le_public left right
      (fixedNumeralTerm left) (shortBinaryNumeralTerm right)
      hleftClosed hrightClosed (by simp)
      (by simp [termValue_shortBinaryNumeralTerm]) hle

def syntaxTermShortBranchAssemblyPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (leResource failureResource : Nat) : Nat :=
  let leFormula := shortNativeLeFormula current.tokensCount 1
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
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
  let shortResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation leFormula failureFormula leResource failureResource
  transparentHybridDisjunctionLeftPayloadEnvelope termZeroValuation
    shortFormula enoughFormula shortResource

theorem syntaxTermShortBranchAssemblyPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (tailBoundary tailCount : Nat)
    (leCertificate : TermHybridCertificate
      (shortNativeLeFormula current.tokensCount 1))
    (failureCertificate : TermHybridCertificate
      (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next tailBoundary tailCount))
    (enoughFormula : ValuationFormula)
    (leResource failureResource : Nat)
    (hle : hybridFormulaStructuralPayloadBound leCertificate ≤ leResource)
    (hfailure : hybridFormulaStructuralPayloadBound failureCertificate ≤
      failureResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := enoughFormula)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            leCertificate failureCertificate)) ≤
      transparentHybridDisjunctionLeftPayloadEnvelope termZeroValuation
        (shortNativeLeFormula current.tokensCount 1 ⋏
          compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
            tokenCount current next tailBoundary tailCount)
        enoughFormula
        (transparentHybridConjunctionPayloadEnvelope termZeroValuation
          (shortNativeLeFormula current.tokensCount 1)
          (compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
            tokenCount current next tailBoundary tailCount)
          leResource failureResource) := by
  have hshort := transparentHybridConjunctionPayloadBound_le leCertificate
    failureCertificate leResource failureResource hle hfailure
  exact transparentHybridDisjunctionLeftPayloadBound_le
    (right := enoughFormula)
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction leCertificate
      failureCertificate) _ hshort

def syntaxTermEnoughBranchAssemblyPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (countResource atTagResource atArgumentResource decisionResource : Nat) :
    Nat :=
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let shortFormula := shortNativeLeFormula current.tokensCount 1 ⋏
    failureFormula
  let countFormula := nativeShortLeFormula 2 current.tokensCount
  let atTagFormula := compactAdditiveNatListAtRowsAtValuationIndexFormula
    tokenTable width tokenCount current.tokensBoundary current.tokensCount
    witness.tag (fixedNumeralTerm 0)
  let atArgumentFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount witness.argument
      (fixedNumeralTerm 1)
  let decisionFormula := compactUnifiedParserSyntaxTermDecisionExplicitFormula
    tokenTable width tokenCount current next binderArity witness
  let argumentDecisionResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation atArgumentFormula decisionFormula atArgumentResource
    decisionResource
  let tagTailResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation atTagFormula (atArgumentFormula ⋏ decisionFormula)
    atTagResource argumentDecisionResource
  let enoughResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation countFormula
    (atTagFormula ⋏ (atArgumentFormula ⋏ decisionFormula)) countResource
    tagTailResource
  transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
    shortFormula
    (countFormula ⋏ atTagFormula ⋏ atArgumentFormula ⋏ decisionFormula)
    enoughResource

theorem syntaxTermEnoughBranchAssemblyPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (countCertificate : TermHybridCertificate
      (nativeShortLeFormula 2 current.tokensCount))
    (atTagCertificate : TermHybridCertificate
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.tag
        (fixedNumeralTerm 0)))
    (atArgumentCertificate : TermHybridCertificate
      (compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
        tokenCount current.tokensBoundary current.tokensCount witness.argument
        (fixedNumeralTerm 1)))
    (decisionCertificate : TermHybridCertificate
      (compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness))
    (countResource atTagResource atArgumentResource decisionResource : Nat)
    (hcount : hybridFormulaStructuralPayloadBound countCertificate ≤
      countResource)
    (hatTag : hybridFormulaStructuralPayloadBound atTagCertificate ≤
      atTagResource)
    (hatArgument : hybridFormulaStructuralPayloadBound atArgumentCertificate ≤
      atArgumentResource)
    (hdecision : hybridFormulaStructuralPayloadBound decisionCertificate ≤
      decisionResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := shortNativeLeFormula current.tokensCount 1 ⋏
            compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
              tokenCount current next witness.tailBoundary witness.tailCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            countCertificate
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              atTagCertificate
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                atArgumentCertificate decisionCertificate)))) ≤
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness countResource atTagResource
        atArgumentResource decisionResource := by
  let argumentDecision :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atArgumentCertificate decisionCertificate
  have hargumentDecision := transparentHybridConjunctionPayloadBound_le
    atArgumentCertificate decisionCertificate atArgumentResource
    decisionResource hatArgument hdecision
  let tagTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    atTagCertificate argumentDecision
  have htagTail := transparentHybridConjunctionPayloadBound_le atTagCertificate
    argumentDecision atTagResource _ hatTag hargumentDecision
  let enough := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate tagTail
  have henough := transparentHybridConjunctionPayloadBound_le countCertificate
    tagTail countResource _ hcount htagTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := shortNativeLeFormula current.tokensCount 1 ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
    enough _ henough
  unfold syntaxTermEnoughBranchAssemblyPayloadEnvelope
  simpa only [argumentDecision, tagTail, enough] using houter

def syntaxTermZeroSuccessDecisionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  nativeEqFormula witness.tag 0 ⋏
    shortLtFormula witness.argument binderArity ⋏
      compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2

def syntaxTermZeroFailureDecisionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  nativeEqFormula witness.tag 0 ⋏
    shortLeFormula binderArity witness.argument ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount

def syntaxTermOneDecisionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  nativeEqFormula witness.tag 1 ⋏
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 2

def syntaxTermTwoShortFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  shortNativeLeFormula current.tokensCount 2 ⋏
    compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount

def syntaxTermTwoFunctionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  nativeShortLeFormula 3 current.tokensCount ⋏
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.functionCode (fixedNumeralTerm 2) ⋏
    ((compactAdditiveArithmeticFuncCodeValidClosedFormula witness.argument
        witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.argument) ⋎
      (compactAdditiveArithmeticFuncCodeInvalidClosedFormula witness.argument
        witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount))

def syntaxTermTwoDecisionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  nativeEqFormula witness.tag 2 ⋏
    (syntaxTermTwoShortFormula tokenTable width tokenCount current next witness ⋎
      syntaxTermTwoFunctionFormula tokenTable width tokenCount current next
        binderArity witness)

def syntaxTermInvalidTagDecisionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  nativeNeFormula witness.tag 0 ⋏ nativeNeFormula witness.tag 1 ⋏
    nativeNeFormula witness.tag 2 ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount

def syntaxTermZeroPairDecisionFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount current next
      binderArity witness ⋎
    syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount current
      next binderArity witness

def syntaxTermDecisionRightTailFormula
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) : ValuationFormula :=
  syntaxTermOneDecisionFormula tokenTable width tokenCount current next witness ⋎
    syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
      binderArity witness ⋎
    syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current next
      witness

theorem syntaxTermDecisionExplicitFormula_component_alignment
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates) :
    compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable width
        tokenCount current next binderArity witness =
      syntaxTermZeroPairDecisionFormula tokenTable width tokenCount current next
          binderArity witness ⋎
        syntaxTermDecisionRightTailFormula tokenTable width tokenCount current
          next binderArity witness := by
  rfl

def syntaxTermDecisionZeroSuccessPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let successFormula := syntaxTermZeroSuccessDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let failureFormula := syntaxTermZeroFailureDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let zeroPairFormula := successFormula ⋎ failureFormula
  let rightTailFormula := syntaxTermDecisionRightTailFormula tokenTable width
    tokenCount current next binderArity witness
  let zeroPairResource := transparentHybridDisjunctionLeftPayloadEnvelope
    termZeroValuation successFormula failureFormula selectedResource
  transparentHybridDisjunctionLeftPayloadEnvelope termZeroValuation
    zeroPairFormula rightTailFormula zeroPairResource

theorem syntaxTermDecisionZeroSuccessPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount current
        next binderArity witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected ≤
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := syntaxTermDecisionRightTailFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := syntaxTermZeroFailureDecisionFormula tokenTable width
              tokenCount current next binderArity witness) selected)) ≤
      syntaxTermDecisionZeroSuccessPathPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness selectedResource := by
  let zeroPair := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount
      current next binderArity witness) selected
  have hzeroPair := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount
      current next binderArity witness) selected _ hselected
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxTermDecisionRightTailFormula tokenTable width tokenCount
      current next binderArity witness) zeroPair _ hzeroPair
  unfold syntaxTermDecisionZeroSuccessPathPayloadEnvelope
  simpa only [zeroPair] using houter

def syntaxTermDecisionZeroFailurePathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let successFormula := syntaxTermZeroSuccessDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let failureFormula := syntaxTermZeroFailureDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let zeroPairFormula := successFormula ⋎ failureFormula
  let rightTailFormula := syntaxTermDecisionRightTailFormula tokenTable width
    tokenCount current next binderArity witness
  let zeroPairResource := transparentHybridDisjunctionRightPayloadEnvelope
    termZeroValuation successFormula failureFormula selectedResource
  transparentHybridDisjunctionLeftPayloadEnvelope termZeroValuation
    zeroPairFormula rightTailFormula zeroPairResource

theorem syntaxTermDecisionZeroFailurePathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount current
        next binderArity witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected ≤
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (right := syntaxTermDecisionRightTailFormula tokenTable width
            tokenCount current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxTermZeroSuccessDecisionFormula tokenTable width
              tokenCount current next binderArity witness) selected)) ≤
      syntaxTermDecisionZeroFailurePathPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness selectedResource := by
  let zeroPair :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount
        current next binderArity witness) selected
  have hzeroPair := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount
      current next binderArity witness) selected _ hselected
  have houter := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxTermDecisionRightTailFormula tokenTable width tokenCount
      current next binderArity witness) zeroPair _ hzeroPair
  unfold syntaxTermDecisionZeroFailurePathPayloadEnvelope
  simpa only [zeroPair] using houter

def syntaxTermDecisionOnePathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let zeroPairFormula := syntaxTermZeroPairDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let oneFormula := syntaxTermOneDecisionFormula tokenTable width tokenCount
    current next witness
  let twoFormula := syntaxTermTwoDecisionFormula tokenTable width tokenCount
    current next binderArity witness
  let invalidFormula := syntaxTermInvalidTagDecisionFormula tokenTable width
    tokenCount current next witness
  let rightTailResource := transparentHybridDisjunctionLeftPayloadEnvelope
    termZeroValuation oneFormula (twoFormula ⋎ invalidFormula)
    selectedResource
  transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
    zeroPairFormula (oneFormula ⋎ twoFormula ⋎ invalidFormula)
    rightTailResource

theorem syntaxTermDecisionOnePathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermOneDecisionFormula tokenTable width tokenCount current next
        witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected ≤
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxTermZeroPairDecisionFormula tokenTable width tokenCount
            current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := syntaxTermTwoDecisionFormula tokenTable width tokenCount
                current next binderArity witness ⋎
              syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount
                current next witness) selected)) ≤
      syntaxTermDecisionOnePathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let rightTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := syntaxTermTwoDecisionFormula tokenTable width tokenCount current
          next binderArity witness ⋎
        syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
          next witness) selected
  have hrightTail := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxTermTwoDecisionFormula tokenTable width tokenCount current
        next binderArity witness ⋎
      syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
        next witness) selected _ hselected
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermZeroPairDecisionFormula tokenTable width tokenCount
      current next binderArity witness) rightTail _ hrightTail
  unfold syntaxTermDecisionOnePathPayloadEnvelope
  simpa only [rightTail] using houter

def syntaxTermDecisionTwoPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let zeroPairFormula := syntaxTermZeroPairDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let oneFormula := syntaxTermOneDecisionFormula tokenTable width tokenCount
    current next witness
  let twoFormula := syntaxTermTwoDecisionFormula tokenTable width tokenCount
    current next binderArity witness
  let invalidFormula := syntaxTermInvalidTagDecisionFormula tokenTable width
    tokenCount current next witness
  let twoTailResource := transparentHybridDisjunctionLeftPayloadEnvelope
    termZeroValuation twoFormula invalidFormula selectedResource
  let rightTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    termZeroValuation oneFormula (twoFormula ⋎ invalidFormula) twoTailResource
  transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
    zeroPairFormula (oneFormula ⋎ twoFormula ⋎ invalidFormula)
    rightTailResource

theorem syntaxTermDecisionTwoPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected ≤
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxTermZeroPairDecisionFormula tokenTable width tokenCount
            current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxTermOneDecisionFormula tokenTable width tokenCount
              current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (right := syntaxTermInvalidTagDecisionFormula tokenTable width
                tokenCount current next witness) selected))) ≤
      syntaxTermDecisionTwoPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let twoTail := CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
    (right := syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount
      current next witness) selected
  have htwoTail := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount
      current next witness) selected _ hselected
  let rightTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermOneDecisionFormula tokenTable width tokenCount current
        next witness) twoTail
  have hrightTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermOneDecisionFormula tokenTable width tokenCount current
      next witness) twoTail _ htwoTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermZeroPairDecisionFormula tokenTable width tokenCount
      current next binderArity witness) rightTail _ hrightTail
  unfold syntaxTermDecisionTwoPathPayloadEnvelope
  simpa only [twoTail, rightTail] using houter

def syntaxTermDecisionInvalidTagPathPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selectedResource : Nat) : Nat :=
  let zeroPairFormula := syntaxTermZeroPairDecisionFormula tokenTable width
    tokenCount current next binderArity witness
  let oneFormula := syntaxTermOneDecisionFormula tokenTable width tokenCount
    current next witness
  let twoFormula := syntaxTermTwoDecisionFormula tokenTable width tokenCount
    current next binderArity witness
  let invalidFormula := syntaxTermInvalidTagDecisionFormula tokenTable width
    tokenCount current next witness
  let twoTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    termZeroValuation twoFormula invalidFormula selectedResource
  let rightTailResource := transparentHybridDisjunctionRightPayloadEnvelope
    termZeroValuation oneFormula (twoFormula ⋎ invalidFormula) twoTailResource
  transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
    zeroPairFormula (oneFormula ⋎ twoFormula ⋎ invalidFormula)
    rightTailResource

theorem syntaxTermDecisionInvalidTagPathPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (selected : TermHybridCertificate
      (syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
        next witness))
    (selectedResource : Nat)
    (hselected : hybridFormulaStructuralPayloadBound selected ≤
      selectedResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := syntaxTermZeroPairDecisionFormula tokenTable width tokenCount
            current next binderArity witness)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxTermOneDecisionFormula tokenTable width tokenCount
              current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (left := syntaxTermTwoDecisionFormula tokenTable width tokenCount
                current next binderArity witness) selected))) ≤
      syntaxTermDecisionInvalidTagPathPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness selectedResource := by
  let twoTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermTwoDecisionFormula tokenTable width tokenCount current
        next binderArity witness) selected
  have htwoTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermTwoDecisionFormula tokenTable width tokenCount current
      next binderArity witness) selected _ hselected
  let rightTail :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermOneDecisionFormula tokenTable width tokenCount current
        next witness) twoTail
  have hrightTail := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermOneDecisionFormula tokenTable width tokenCount current
      next witness) twoTail _ htwoTail
  have houter := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermZeroPairDecisionFormula tokenTable width tokenCount
      current next binderArity witness) rightTail _ hrightTail
  unfold syntaxTermDecisionInvalidTagPathPayloadEnvelope
  simpa only [twoTail, rightTail] using houter

noncomputable def syntaxTermZeroSuccessSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) : Nat :=
  let equalityFormula := nativeEqFormula witness.tag 0
  let strictFormula := shortLtFormula witness.argument binderArity
  let continueFormula :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 2
  let strictContinueResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation strictFormula continueFormula
    (syntaxTermShortLtPayloadPolynomial witness.argument binderArity)
    (compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2
      hcontinue)
  transparentHybridConjunctionPayloadEnvelope termZeroValuation equalityFormula
    (strictFormula ⋏ continueFormula)
    (syntaxTermNativeEqPayloadPolynomial witness.tag 0)
    strictContinueResource

theorem syntaxTermZeroSuccessSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : witness.argument < binderArity)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate witness.tag 0 htag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortLtCertificate witness.argument binderArity hargument)
            (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount 2 hcontinue))) ≤
      syntaxTermZeroSuccessSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hcontinue := by
  let equalityCertificate := nativeEqCertificate witness.tag 0 htag
  let strictCertificate := shortLtCertificate witness.argument binderArity
    hargument
  let continueCertificate :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue
  have hequality := nativeEqCertificate_structuralPayloadBound_le_public
    witness.tag 0 htag
  have hstrict := shortLtCertificate_structuralPayloadBound_le_public
    witness.argument binderArity hargument
  have hcontinueResource :=
    compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue
  let strictContinue :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      strictCertificate continueCertificate
  have hstrictContinue := transparentHybridConjunctionPayloadBound_le
    strictCertificate continueCertificate _ _ hstrict hcontinueResource
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    equalityCertificate strictContinue
  have hselected := transparentHybridConjunctionPayloadBound_le
    equalityCertificate strictContinue _ _ hequality hstrictContinue
  unfold syntaxTermZeroSuccessSelectedPayloadEnvelope
  simpa only [equalityCertificate, strictCertificate, continueCertificate,
    strictContinue, selected] using hselected

noncomputable def syntaxTermZeroFailureSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let equalityFormula := nativeEqFormula witness.tag 0
  let leFormula := shortLeFormula binderArity witness.argument
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let leFailureResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation leFormula failureFormula
    (syntaxTermShortLePayloadEnvelope binderArity witness.argument)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  transparentHybridConjunctionPayloadEnvelope termZeroValuation equalityFormula
    (leFormula ⋏ failureFormula)
    (syntaxTermNativeEqPayloadPolynomial witness.tag 0) leFailureResource

theorem syntaxTermZeroFailureSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : binderArity ≤ witness.argument)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate witness.tag 0 htag)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortLeCertificate binderArity witness.argument hargument)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure))) ≤
      syntaxTermZeroFailureSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hfailure := by
  let equalityCertificate := nativeEqCertificate witness.tag 0 htag
  let leCertificate := shortLeCertificate binderArity witness.argument
    hargument
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  have hequality := nativeEqCertificate_structuralPayloadBound_le_public
    witness.tag 0 htag
  have hle := shortLeCertificate_structuralPayloadBound_le_public binderArity
    witness.argument hargument
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let leFailure := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leCertificate failureCertificate
  have hleFailure := transparentHybridConjunctionPayloadBound_le leCertificate
    failureCertificate _ _ hle hfailureResource
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    equalityCertificate leFailure
  have hselected := transparentHybridConjunctionPayloadBound_le
    equalityCertificate leFailure _ _ hequality hleFailure
  unfold syntaxTermZeroFailureSelectedPayloadEnvelope
  simpa only [equalityCertificate, leCertificate, failureCertificate,
    leFailure, selected] using hselected

noncomputable def syntaxTermOneSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) : Nat :=
  transparentHybridConjunctionPayloadEnvelope termZeroValuation
    (nativeEqFormula witness.tag 1)
    (compactUnifiedParserSyntaxTermContinueFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount 2)
    (syntaxTermNativeEqPayloadPolynomial witness.tag 1)
    (compactUnifiedParserSyntaxTermContinueGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2
      hcontinue)

theorem syntaxTermOneSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 1)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate witness.tag 1 htag)
          (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount 2 hcontinue)) ≤
      syntaxTermOneSelectedPayloadEnvelope tokenTable width tokenCount current
        next witness hcontinue := by
  exact transparentHybridConjunctionPayloadBound_le
    (nativeEqCertificate witness.tag 1 htag)
    (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue) _ _
    (nativeEqCertificate_structuralPayloadBound_le_public witness.tag 1 htag)
    (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount 2 hcontinue)

noncomputable def syntaxTermTwoShortSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let equalityFormula := nativeEqFormula witness.tag 2
  let shortFormula := syntaxTermTwoShortFormula tokenTable width tokenCount
    current next witness
  let functionFormula := syntaxTermTwoFunctionFormula tokenTable width
    tokenCount current next binderArity witness
  let leFormula := shortNativeLeFormula current.tokensCount 2
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let shortResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation leFormula failureFormula
    (syntaxTermShortNativeLePayloadEnvelope current.tokensCount 2)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  let choiceResource := transparentHybridDisjunctionLeftPayloadEnvelope
    termZeroValuation shortFormula functionFormula shortResource
  transparentHybridConjunctionPayloadEnvelope termZeroValuation equalityFormula
    (shortFormula ⋎ functionFormula)
    (syntaxTermNativeEqPayloadPolynomial witness.tag 2) choiceResource

theorem syntaxTermTwoShortSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (htooShort : current.tokensCount ≤ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate witness.tag 2 htag)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
            (right := syntaxTermTwoFunctionFormula tokenTable width tokenCount
              current next binderArity witness)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (shortNativeLeCertificate current.tokensCount 2 htooShort)
              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount hfailure)))) ≤
      syntaxTermTwoShortSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hfailure := by
  let equalityCertificate := nativeEqCertificate witness.tag 2 htag
  let leCertificate := shortNativeLeCertificate current.tokensCount 2
    htooShort
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  have hequality := nativeEqCertificate_structuralPayloadBound_le_public
    witness.tag 2 htag
  have hle := shortNativeLeCertificate_structuralPayloadBound_le_public
    current.tokensCount 2 htooShort
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let shortCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction leCertificate
      failureCertificate
  have hshort := transparentHybridConjunctionPayloadBound_le leCertificate
    failureCertificate _ _ hle hfailureResource
  let choiceCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := syntaxTermTwoFunctionFormula tokenTable width tokenCount current
        next binderArity witness) shortCertificate
  have hchoice := transparentHybridDisjunctionLeftPayloadBound_le
    (right := syntaxTermTwoFunctionFormula tokenTable width tokenCount current
      next binderArity witness) shortCertificate _ hshort
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    equalityCertificate choiceCertificate
  have hselected := transparentHybridConjunctionPayloadBound_le
    equalityCertificate choiceCertificate _ _ hequality hchoice
  unfold syntaxTermTwoShortSelectedPayloadEnvelope
  simpa only [syntaxTermTwoShortFormula, equalityCertificate, leCertificate,
    failureCertificate, shortCertificate, choiceCertificate, selected] using
    hselected

noncomputable def syntaxTermTwoValidSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (atFunctionResource : Nat)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) : Nat :=
  let equalityFormula := nativeEqFormula witness.tag 2
  let shortFormula := syntaxTermTwoShortFormula tokenTable width tokenCount
    current next witness
  let functionFormula := syntaxTermTwoFunctionFormula tokenTable width
    tokenCount current next binderArity witness
  let countFormula := nativeShortLeFormula 3 current.tokensCount
  let atFunctionFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.functionCode (fixedNumeralTerm 2)
  let validFormula := compactAdditiveArithmeticFuncCodeValidClosedFormula
    witness.argument witness.functionCode
  let functionTransitionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.argument
  let invalidFormula := compactAdditiveArithmeticFuncCodeInvalidClosedFormula
    witness.argument witness.functionCode
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let validBranchFormula := validFormula ⋏ functionTransitionFormula
  let invalidBranchFormula := invalidFormula ⋏ failureFormula
  let validBranchResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation validFormula functionTransitionFormula
    (compactAdditiveArithmeticFuncCodeValidPayloadEnvelope witness.argument
      witness.functionCode)
    (compactUnifiedParserSyntaxTermFunctionGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument hfunction)
  let validityChoiceResource := transparentHybridDisjunctionLeftPayloadEnvelope
    termZeroValuation validBranchFormula invalidBranchFormula
    validBranchResource
  let atFunctionTailResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation atFunctionFormula
    (validBranchFormula ⋎ invalidBranchFormula)
    atFunctionResource
    validityChoiceResource
  let functionResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation countFormula
    (atFunctionFormula ⋏ (validBranchFormula ⋎ invalidBranchFormula))
    (syntaxTermNativeShortLePayloadEnvelope 3 current.tokensCount)
    atFunctionTailResource
  let shortFunctionChoiceResource :=
    transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
      shortFormula functionFormula functionResource
  transparentHybridConjunctionPayloadEnvelope termZeroValuation equalityFormula
    (shortFormula ⋎ functionFormula)
    (syntaxTermNativeEqPayloadPolynomial witness.tag 2)
    shortFunctionChoiceResource

theorem syntaxTermTwoValidSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 ≤ current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument)
    (atFunctionResource : Nat)
    (hatFunctionResource :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (natListAtFixedNumeralTerm_value 2) hatFunction) ≤
        atFunctionResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate witness.tag 2 htag)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxTermTwoShortFormula tokenTable width tokenCount
              current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeShortLeCertificate 3 current.tokensCount hthree)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.functionCode
                  (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                  hatFunction)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                  (right :=
                    compactAdditiveArithmeticFuncCodeInvalidClosedFormula
                        witness.argument witness.functionCode ⋏
                      compactUnifiedParserSyntaxTermFailureClosedFormula
                        tokenTable width tokenCount current next
                        witness.tailBoundary witness.tailCount)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
                      witness.argument witness.functionCode hvalid)
                    (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount binderArity
                      witness.argument hfunction))))))) ≤
      syntaxTermTwoValidSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness atFunctionResource hfunction := by
  let equalityCertificate := nativeEqCertificate witness.tag 2 htag
  let countCertificate := nativeShortLeCertificate 3 current.tokensCount hthree
  let atFunctionCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatFunction
  let validCertificate :=
    compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
      witness.argument witness.functionCode hvalid
  let functionCertificate :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity witness.argument hfunction
  have hequality := nativeEqCertificate_structuralPayloadBound_le_public
    witness.tag 2 htag
  have hcount := nativeShortLeCertificate_structuralPayloadBound_le_public 3
    current.tokensCount hthree
  have hvalidResource :=
    compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      witness.argument witness.functionCode hvalid
  have hfunctionResource :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount binderArity witness.argument hfunction
  let validBranch := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    validCertificate functionCertificate
  have hvalidBranch := transparentHybridConjunctionPayloadBound_le
    validCertificate functionCertificate _ _ hvalidResource hfunctionResource
  let validityChoice :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (right := compactAdditiveArithmeticFuncCodeInvalidClosedFormula
          witness.argument witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
          tokenCount current next witness.tailBoundary witness.tailCount)
      validBranch
  have hvalidityChoice := transparentHybridDisjunctionLeftPayloadBound_le
    (right := compactAdditiveArithmeticFuncCodeInvalidClosedFormula
        witness.argument witness.functionCode ⋏
      compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
        tokenCount current next witness.tailBoundary witness.tailCount)
    validBranch _ hvalidBranch
  let atFunctionTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atFunctionCertificate validityChoice
  have hatFunctionTail := transparentHybridConjunctionPayloadBound_le
    atFunctionCertificate validityChoice _ _ hatFunctionResource
    hvalidityChoice
  let functionSelected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      atFunctionTail
  have hfunctionSelected := transparentHybridConjunctionPayloadBound_le
    countCertificate atFunctionTail _ _ hcount hatFunctionTail
  let shortFunctionChoice :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermTwoShortFormula tokenTable width tokenCount current next
        witness) functionSelected
  have hshortFunctionChoice := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermTwoShortFormula tokenTable width tokenCount current next
      witness) functionSelected _ hfunctionSelected
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    equalityCertificate shortFunctionChoice
  have hselected := transparentHybridConjunctionPayloadBound_le
    equalityCertificate shortFunctionChoice _ _ hequality hshortFunctionChoice
  have hnatListZero :
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation =
        termZeroValuation := rfl
  have hfuncCodeZero :
      FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation =
        termZeroValuation := rfl
  rw [hnatListZero, hfuncCodeZero] at hselected
  change hybridFormulaStructuralPayloadBound selected ≤ _
  exact hselected

noncomputable def syntaxTermTwoInvalidSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (atFunctionResource : Nat)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let equalityFormula := nativeEqFormula witness.tag 2
  let shortFormula := syntaxTermTwoShortFormula tokenTable width tokenCount
    current next witness
  let functionFormula := syntaxTermTwoFunctionFormula tokenTable width
    tokenCount current next binderArity witness
  let countFormula := nativeShortLeFormula 3 current.tokensCount
  let atFunctionFormula :=
    compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
      tokenCount current.tokensBoundary current.tokensCount
      witness.functionCode (fixedNumeralTerm 2)
  let validFormula := compactAdditiveArithmeticFuncCodeValidClosedFormula
    witness.argument witness.functionCode
  let functionTransitionFormula :=
    compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
      width tokenCount current next witness.tailBoundary witness.tailCount
      binderArity witness.argument
  let invalidFormula := compactAdditiveArithmeticFuncCodeInvalidClosedFormula
    witness.argument witness.functionCode
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let validBranchFormula := validFormula ⋏ functionTransitionFormula
  let invalidBranchFormula := invalidFormula ⋏ failureFormula
  let invalidBranchResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation invalidFormula failureFormula
    (compactAdditiveArithmeticFuncCodeInvalidPayloadEnvelope witness.argument
      witness.functionCode)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  let validityChoiceResource :=
    transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
      validBranchFormula invalidBranchFormula invalidBranchResource
  let atFunctionTailResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation atFunctionFormula
    (validBranchFormula ⋎ invalidBranchFormula)
    atFunctionResource
    validityChoiceResource
  let functionResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation countFormula
    (atFunctionFormula ⋏ (validBranchFormula ⋎ invalidBranchFormula))
    (syntaxTermNativeShortLePayloadEnvelope 3 current.tokensCount)
    atFunctionTailResource
  let shortFunctionChoiceResource :=
    transparentHybridDisjunctionRightPayloadEnvelope termZeroValuation
      shortFormula functionFormula functionResource
  transparentHybridConjunctionPayloadEnvelope termZeroValuation equalityFormula
    (shortFormula ⋎ functionFormula)
    (syntaxTermNativeEqPayloadPolynomial witness.tag 2)
    shortFunctionChoiceResource

theorem syntaxTermTwoInvalidSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 ≤ current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount)
    (atFunctionResource : Nat)
    (hatFunctionResource :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (natListAtFixedNumeralTerm_value 2) hatFunction) ≤
        atFunctionResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeEqCertificate witness.tag 2 htag)
          (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
            (left := syntaxTermTwoShortFormula tokenTable width tokenCount
              current next witness)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeShortLeCertificate 3 current.tokensCount hthree)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 2 witness.functionCode
                  (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                  hatFunction)
                (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                  (left :=
                    compactAdditiveArithmeticFuncCodeValidClosedFormula
                        witness.argument witness.functionCode ⋏
                      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
                        tokenTable width tokenCount current next
                        witness.tailBoundary witness.tailCount binderArity
                        witness.argument)
                  (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                    (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
                      witness.argument witness.functionCode hinvalid)
                    (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                      tokenTable width tokenCount current next
                      witness.tailBoundary witness.tailCount hfailure))))))) ≤
      syntaxTermTwoInvalidSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness atFunctionResource hfailure := by
  let equalityCertificate := nativeEqCertificate witness.tag 2 htag
  let countCertificate := nativeShortLeCertificate 3 current.tokensCount hthree
  let atFunctionCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatFunction
  let invalidCertificate :=
    compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
      witness.argument witness.functionCode hinvalid
  let failureCertificate :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  have hequality := nativeEqCertificate_structuralPayloadBound_le_public
    witness.tag 2 htag
  have hcount := nativeShortLeCertificate_structuralPayloadBound_le_public 3
    current.tokensCount hthree
  have hinvalidResource :=
    compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      witness.argument witness.functionCode hinvalid
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let invalidBranch :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      invalidCertificate failureCertificate
  have hinvalidBranch := transparentHybridConjunctionPayloadBound_le
    invalidCertificate failureCertificate _ _ hinvalidResource hfailureResource
  let validityChoice :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := compactAdditiveArithmeticFuncCodeValidClosedFormula
          witness.argument witness.functionCode ⋏
        compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount binderArity witness.argument) invalidBranch
  have hvalidityChoice := transparentHybridDisjunctionRightPayloadBound_le
    (left := compactAdditiveArithmeticFuncCodeValidClosedFormula
        witness.argument witness.functionCode ⋏
      compactUnifiedParserSyntaxTermFunctionFixedNumeralClosedFormula tokenTable
        width tokenCount current next witness.tailBoundary witness.tailCount
        binderArity witness.argument) invalidBranch _ hinvalidBranch
  let atFunctionTail :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      atFunctionCertificate validityChoice
  have hatFunctionTail := transparentHybridConjunctionPayloadBound_le
    atFunctionCertificate validityChoice _ _ hatFunctionResource
    hvalidityChoice
  let functionSelected :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction countCertificate
      atFunctionTail
  have hfunctionSelected := transparentHybridConjunctionPayloadBound_le
    countCertificate atFunctionTail _ _ hcount hatFunctionTail
  let shortFunctionChoice :=
    CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (left := syntaxTermTwoShortFormula tokenTable width tokenCount current next
        witness) functionSelected
  have hshortFunctionChoice := transparentHybridDisjunctionRightPayloadBound_le
    (left := syntaxTermTwoShortFormula tokenTable width tokenCount current next
      witness) functionSelected _ hfunctionSelected
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    equalityCertificate shortFunctionChoice
  have hselected := transparentHybridConjunctionPayloadBound_le
    equalityCertificate shortFunctionChoice _ _ hequality hshortFunctionChoice
  have hnatListZero :
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation =
        termZeroValuation := rfl
  have hfuncCodeZero :
      FoundationCompactNumericListedDirectArithmeticFuncCodeValidExplicitHybridCertificate.zeroValuation =
        termZeroValuation := rfl
  rw [hnatListZero, hfuncCodeZero] at hselected
  change hybridFormulaStructuralPayloadBound selected ≤ _
  exact hselected

noncomputable def syntaxTermInvalidTagSelectedPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let ne0Formula := nativeNeFormula witness.tag 0
  let ne1Formula := nativeNeFormula witness.tag 1
  let ne2Formula := nativeNeFormula witness.tag 2
  let failureFormula := compactUnifiedParserSyntaxTermFailureClosedFormula
    tokenTable width tokenCount current next witness.tailBoundary
    witness.tailCount
  let ne2FailureResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation ne2Formula failureFormula
    (syntaxTermNativeNePayloadPolynomial witness.tag 2)
    (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount hfailure)
  let ne1TailResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation ne1Formula (ne2Formula ⋏ failureFormula)
    (syntaxTermNativeNePayloadPolynomial witness.tag 1) ne2FailureResource
  transparentHybridConjunctionPayloadEnvelope termZeroValuation ne0Formula
    (ne1Formula ⋏ ne2Formula ⋏ failureFormula)
    (syntaxTermNativeNePayloadPolynomial witness.tag 0) ne1TailResource

theorem syntaxTermInvalidTagSelectedPayloadBound_le
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hne0 : witness.tag ≠ 0)
    (hne1 : witness.tag ≠ 1)
    (hne2 : witness.tag ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 0 hne0)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeNeCertificate witness.tag 1 hne1)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (nativeNeCertificate witness.tag 2 hne2)
              (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current next witness.tailBoundary
                witness.tailCount hfailure)))) ≤
      syntaxTermInvalidTagSelectedPayloadEnvelope tokenTable width tokenCount
        current next witness hfailure := by
  let ne0Certificate := nativeNeCertificate witness.tag 0 hne0
  let ne1Certificate := nativeNeCertificate witness.tag 1 hne1
  let ne2Certificate := nativeNeCertificate witness.tag 2 hne2
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
  have hfailureResource :=
    compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current next witness.tailBoundary
      witness.tailCount hfailure
  let ne2Failure := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    ne2Certificate failureCertificate
  have hne2Failure := transparentHybridConjunctionPayloadBound_le ne2Certificate
    failureCertificate _ _ hne2Resource hfailureResource
  let ne1Tail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    ne1Certificate ne2Failure
  have hne1Tail := transparentHybridConjunctionPayloadBound_le ne1Certificate
    ne2Failure _ _ hne1Resource hne2Failure
  let selected := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    ne0Certificate ne1Tail
  have hselected := transparentHybridConjunctionPayloadBound_le ne0Certificate
    ne1Tail _ _ hne0Resource hne1Tail
  unfold syntaxTermInvalidTagSelectedPayloadEnvelope
  simpa only [ne0Certificate, ne1Certificate, ne2Certificate,
    failureCertificate, ne2Failure, ne1Tail, selected] using hselected

noncomputable def compactSyntaxTermZeroSuccessDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) : Nat :=
  syntaxTermDecisionZeroSuccessPathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness
    (syntaxTermZeroSuccessSelectedPayloadEnvelope tokenTable width tokenCount
      current next binderArity witness hcontinue)

theorem compactSyntaxTermZeroSuccessDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : witness.argument < binderArity)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermZeroSuccessDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument
          hcontinue) ≤
      compactSyntaxTermZeroSuccessDecisionPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hcontinue := by
  let selected : TermHybridCertificate
      (syntaxTermZeroSuccessDecisionFormula tokenTable width tokenCount current
        next binderArity witness) := by
    unfold syntaxTermZeroSuccessDecisionFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 0 htag)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (shortLtCertificate witness.argument binderArity hargument)
        (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount 2 hcontinue))
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermZeroSuccessSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hcontinue := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate witness.tag 0 htag)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (shortLtCertificate witness.argument binderArity hargument)
          (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount 2 hcontinue))) ≤ _
    exact syntaxTermZeroSuccessSelectedPayloadBound_le tokenTable width
      tokenCount current next binderArity witness htag hargument hcontinue
  have hpath := syntaxTermDecisionZeroSuccessPathPayloadBound_le tokenTable
    width tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermZeroSuccessDecisionCertificate
    compactSyntaxTermZeroSuccessDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        selected)) ≤ _
  exact hpath

noncomputable def compactSyntaxTermZeroFailureDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  syntaxTermDecisionZeroFailurePathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness
    (syntaxTermZeroFailureSelectedPayloadEnvelope tokenTable width tokenCount
      current next binderArity witness hfailure)

theorem compactSyntaxTermZeroFailureDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 0)
    (hargument : binderArity ≤ witness.argument)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermZeroFailureDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument
          hfailure) ≤
      compactSyntaxTermZeroFailureDecisionPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hfailure := by
  let selected : TermHybridCertificate
      (syntaxTermZeroFailureDecisionFormula tokenTable width tokenCount current
        next binderArity witness) := by
    unfold syntaxTermZeroFailureDecisionFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 0 htag)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (shortLeCertificate binderArity witness.argument hargument)
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure))
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermZeroFailureSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hfailure := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate witness.tag 0 htag)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (shortLeCertificate binderArity witness.argument hargument)
          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount hfailure))) ≤ _
    exact syntaxTermZeroFailureSelectedPayloadBound_le tokenTable width
      tokenCount current next binderArity witness htag hargument hfailure
  have hpath := syntaxTermDecisionZeroFailurePathPayloadBound_le tokenTable
    width tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermZeroFailureDecisionCertificate
    compactSyntaxTermZeroFailureDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        selected)) ≤ _
  exact hpath

noncomputable def compactSyntaxTermOneDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) : Nat :=
  syntaxTermDecisionOnePathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness
    (syntaxTermOneSelectedPayloadEnvelope tokenTable width tokenCount current
      next witness hcontinue)

theorem compactSyntaxTermOneDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 1)
    (hcontinue : CompactUnifiedParserSyntaxTermContinueRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount 2) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermOneDecisionCertificate tokenTable width tokenCount
          current next binderArity witness htag hcontinue) ≤
      compactSyntaxTermOneDecisionPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hcontinue := by
  let selected : TermHybridCertificate
      (syntaxTermOneDecisionFormula tokenTable width tokenCount current next
        witness) :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 1 htag)
      (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current next witness.tailBoundary
        witness.tailCount 2 hcontinue)
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermOneSelectedPayloadEnvelope tokenTable width tokenCount current
        next witness hcontinue := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate witness.tag 1 htag)
        (compactUnifiedParserSyntaxTermContinueFixedNumeralExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount 2 hcontinue)) ≤ _
    exact syntaxTermOneSelectedPayloadBound_le tokenTable width tokenCount
      current next witness htag hcontinue
  have hpath := syntaxTermDecisionOnePathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermOneDecisionCertificate
    compactSyntaxTermOneDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        selected)) ≤ _
  exact hpath

noncomputable def compactSyntaxTermTwoShortDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  syntaxTermDecisionTwoPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness
    (syntaxTermTwoShortSelectedPayloadEnvelope tokenTable width tokenCount
      current next binderArity witness hfailure)

theorem compactSyntaxTermTwoShortDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (htooShort : current.tokensCount ≤ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermTwoShortDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag htooShort
          hfailure) ≤
      compactSyntaxTermTwoShortDecisionPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hfailure := by
  let selected : TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness) := by
    unfold syntaxTermTwoDecisionFormula syntaxTermTwoShortFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 2 htag)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (shortNativeLeCertificate current.tokensCount 2 htooShort)
          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount hfailure)))
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermTwoShortSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness hfailure := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate witness.tag 2 htag)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortNativeLeCertificate current.tokensCount 2 htooShort)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure)))) ≤ _
    exact syntaxTermTwoShortSelectedPayloadBound_le tokenTable width tokenCount
      current next binderArity witness htag htooShort hfailure
  have hpath := syntaxTermDecisionTwoPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermTwoShortDecisionCertificate
    compactSyntaxTermTwoShortDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          selected))) ≤ _
  exact hpath

noncomputable def compactSyntaxTermTwoValidDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) : Nat :=
  let atFunctionResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatFunction
  syntaxTermDecisionTwoPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness
    (syntaxTermTwoValidSelectedPayloadEnvelope tokenTable width tokenCount
      current next binderArity witness atFunctionResource hfunction)

theorem compactSyntaxTermTwoValidDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 ≤ current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hvalid : ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfunction : CompactUnifiedParserSyntaxTermFunctionRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount binderArity
      witness.argument) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermTwoValidDecisionCertificate tokenTable width tokenCount
          current next binderArity witness htag hthree hatFunction hvalid
          hfunction) ≤
      compactSyntaxTermTwoValidDecisionPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hatFunction hfunction := by
  let atFunctionResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatFunction
  have hindexClosed : (fixedNumeralTerm 2).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hatFunctionResource :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (natListAtFixedNumeralTerm_value 2) hatFunction) ≤
        atFunctionResource := by
    exact
      compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
        tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
        witness.functionCode (fixedNumeralTerm 2) hindexClosed
        (natListAtFixedNumeralTerm_value 2) hatFunction
  let selected : TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness) := by
    unfold syntaxTermTwoDecisionFormula syntaxTermTwoFunctionFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 2 htag)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 3 current.tokensCount hthree)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
              (natListAtFixedNumeralTerm_value 2) hatFunction)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
                  witness.argument witness.functionCode hvalid)
                (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current next witness.tailBoundary
                  witness.tailCount binderArity witness.argument hfunction))))))
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermTwoValidSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness atFunctionResource hfunction := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate witness.tag 2 htag)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 2 witness.functionCode
                (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                hatFunction)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactAdditiveArithmeticFuncCodeValidExplicitHybridCertificateOfGraph
                    witness.argument witness.functionCode hvalid)
                  (compactUnifiedParserSyntaxTermFunctionFixedNumeralExplicitHybridCertificateOfGraph
                    tokenTable width tokenCount current next
                    witness.tailBoundary witness.tailCount binderArity
                    witness.argument hfunction))))))) ≤ _
    exact syntaxTermTwoValidSelectedPayloadBound_le tokenTable width tokenCount
      current next binderArity witness htag hthree hatFunction hvalid hfunction
      atFunctionResource hatFunctionResource
  have hpath := syntaxTermDecisionTwoPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermTwoValidDecisionCertificate
    compactSyntaxTermTwoValidDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          selected))) ≤ _
  exact hpath

noncomputable def compactSyntaxTermTwoInvalidDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  let atFunctionResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatFunction
  syntaxTermDecisionTwoPathPayloadEnvelope tokenTable width tokenCount current
    next binderArity witness
    (syntaxTermTwoInvalidSelectedPayloadEnvelope tokenTable width tokenCount
      current next binderArity witness atFunctionResource hfailure)

theorem compactSyntaxTermTwoInvalidDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (htag : witness.tag = 2)
    (hthree : 3 ≤ current.tokensCount)
    (hatFunction : CompactAdditiveNatListAtRows tokenTable width tokenCount
      current.tokensBoundary current.tokensCount 2 witness.functionCode)
    (hinvalid : ¬ArithmeticFuncCodeValid witness.argument witness.functionCode)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermTwoInvalidDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hinvalid hfailure) ≤
      compactSyntaxTermTwoInvalidDecisionPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hatFunction hfailure := by
  let atFunctionResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
      width tokenCount current.tokensBoundary current.tokensCount 2
      witness.functionCode (fixedNumeralTerm 2)
      (natListAtFixedNumeralTerm_value 2) hatFunction
  have hindexClosed : (fixedNumeralTerm 2).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hatFunctionResource :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tokensBoundary
            current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
            (natListAtFixedNumeralTerm_value 2) hatFunction) ≤
        atFunctionResource := by
    exact
      compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
        tokenTable width tokenCount current.tokensBoundary current.tokensCount 2
        witness.functionCode (fixedNumeralTerm 2) hindexClosed
        (natListAtFixedNumeralTerm_value 2) hatFunction
  let selected : TermHybridCertificate
      (syntaxTermTwoDecisionFormula tokenTable width tokenCount current next
        binderArity witness) := by
    unfold syntaxTermTwoDecisionFormula syntaxTermTwoFunctionFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeEqCertificate witness.tag 2 htag)
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeShortLeCertificate 3 current.tokensCount hthree)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tokensBoundary
              current.tokensCount 2 witness.functionCode (fixedNumeralTerm 2)
              (natListAtFixedNumeralTerm_value 2) hatFunction)
            (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
                  witness.argument witness.functionCode hinvalid)
                (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current next witness.tailBoundary
                  witness.tailCount hfailure))))))
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermTwoInvalidSelectedPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness atFunctionResource hfailure := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeEqCertificate witness.tag 2 htag)
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 3 current.tokensCount hthree)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 2 witness.functionCode
                (fixedNumeralTerm 2) (natListAtFixedNumeralTerm_value 2)
                hatFunction)
              (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
                (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                  (compactAdditiveArithmeticFuncCodeInvalidExplicitHybridCertificateOfGraph
                    witness.argument witness.functionCode hinvalid)
                  (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
                    tokenTable width tokenCount current next
                    witness.tailBoundary witness.tailCount hfailure))))))) ≤ _
    exact syntaxTermTwoInvalidSelectedPayloadBound_le tokenTable width
      tokenCount current next binderArity witness htag hthree hatFunction
      hinvalid hfailure atFunctionResource hatFunctionResource
  have hpath := syntaxTermDecisionTwoPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermTwoInvalidDecisionCertificate
    compactSyntaxTermTwoInvalidDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          selected))) ≤ _
  exact hpath

noncomputable def compactSyntaxTermInvalidTagDecisionPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) : Nat :=
  syntaxTermDecisionInvalidTagPathPayloadEnvelope tokenTable width tokenCount
    current next binderArity witness
    (syntaxTermInvalidTagSelectedPayloadEnvelope tokenTable width tokenCount
      current next witness hfailure)

theorem compactSyntaxTermInvalidTagDecisionCertificate_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hne0 : witness.tag ≠ 0)
    (hne1 : witness.tag ≠ 1)
    (hne2 : witness.tag ≠ 2)
    (hfailure : CompactUnifiedParserSyntaxTermFailureRows tokenTable width
      tokenCount current next witness.tailBoundary witness.tailCount) :
    hybridFormulaStructuralPayloadBound
        (compactSyntaxTermInvalidTagDecisionCertificate tokenTable width
          tokenCount current next binderArity witness hne0 hne1 hne2
          hfailure) ≤
      compactSyntaxTermInvalidTagDecisionPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hfailure := by
  let selected : TermHybridCertificate
      (syntaxTermInvalidTagDecisionFormula tokenTable width tokenCount current
        next witness) := by
    unfold syntaxTermInvalidTagDecisionFormula
    exact CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (nativeNeCertificate witness.tag 0 hne0)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeNeCertificate witness.tag 1 hne1)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 2 hne2)
          (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current next witness.tailBoundary
            witness.tailCount hfailure)))
  have hselected : hybridFormulaStructuralPayloadBound selected ≤
      syntaxTermInvalidTagSelectedPayloadEnvelope tokenTable width tokenCount
        current next witness hfailure := by
    change hybridFormulaStructuralPayloadBound
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (nativeNeCertificate witness.tag 0 hne0)
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (nativeNeCertificate witness.tag 1 hne1)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeNeCertificate witness.tag 2 hne2)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure)))) ≤ _
    exact syntaxTermInvalidTagSelectedPayloadBound_le tokenTable width
      tokenCount current next witness hne0 hne1 hne2 hfailure
  have hpath := syntaxTermDecisionInvalidTagPathPayloadBound_le tokenTable width
    tokenCount current next binderArity witness selected _ hselected
  unfold compactSyntaxTermInvalidTagDecisionCertificate
    compactSyntaxTermInvalidTagDecisionPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
      (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          selected))) ≤ _
  exact hpath

noncomputable def syntaxTermNatListAtFixedIndexGraphPayloadEnvelope
    (tokenTable width tokenCount boundaryTable count index value : Nat)
    (hrows : CompactAdditiveNatListAtRows tokenTable width tokenCount
      boundaryTable count index value) : Nat :=
  compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope tokenTable
    width tokenCount boundaryTable count index value (fixedNumeralTerm index)
    (natListAtFixedNumeralTerm_value index) hrows

theorem syntaxTermEnoughBranchFromRowsPayloadBound_le
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
        tokenCount current next binderArity witness))
    (decisionResource : Nat)
    (hdecision : hybridFormulaStructuralPayloadBound decisionCertificate <=
      decisionResource) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (left := shortNativeLeFormula current.tokensCount 1 ⋏
            compactUnifiedParserSyntaxTermFailureClosedFormula tokenTable width
              tokenCount current next witness.tailBoundary witness.tailCount)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument (fixedNumeralTerm 1)
                  (natListAtFixedNumeralTerm_value 1) hatArgument)
                decisionCertificate)))) <=
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        decisionResource := by
  have hindexClosed (index : Nat) :
      (fixedNumeralTerm index).freeVariables ⊆ {0} := by
    rw [fixedNumeralTerm_freeVariables_eq_empty]
    simp
  have hcountResource :=
    nativeShortLeCertificate_structuralPayloadBound_le_public 2
      current.tokensCount hcount
  have hatTagResource :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag (fixedNumeralTerm 0) (hindexClosed 0)
      (natListAtFixedNumeralTerm_value 0) hatTag
  have hatArgumentResource :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.argument (fixedNumeralTerm 1) (hindexClosed 1)
      (natListAtFixedNumeralTerm_value 1) hatArgument
  exact syntaxTermEnoughBranchAssemblyPayloadBound_le tokenTable width tokenCount
    current next binderArity witness
    (nativeShortLeCertificate 2 current.tokensCount hcount)
    (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 0
      witness.tag (fixedNumeralTerm 0) (natListAtFixedNumeralTerm_value 0)
      hatTag)
    (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tokensBoundary current.tokensCount 1
      witness.argument (fixedNumeralTerm 1)
      (natListAtFixedNumeralTerm_value 1) hatArgument)
    decisionCertificate
    (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
    (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
      tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
      hatTag)
    (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
      tokenCount current.tokensBoundary current.tokensCount 1 witness.argument
      hatArgument)
    decisionResource hcountResource hatTagResource hatArgumentResource
    hdecision

noncomputable def compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) : Nat :=
  match data with
  | .short _ hfailure =>
      syntaxTermShortBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermShortNativeLePayloadEnvelope current.tokensCount 1)
        (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable
          width tokenCount current next witness.tailBoundary witness.tailCount
          hfailure)
  | .zeroSuccess _ hatTag hatArgument _ _ hcontinue =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermZeroSuccessDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hcontinue)
  | .zeroFailure _ hatTag hatArgument _ _ hfailure =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermZeroFailureDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)
  | .one _ hatTag hatArgument _ hcontinue =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermOneDecisionPayloadEnvelope tokenTable width tokenCount
          current next binderArity witness hcontinue)
  | .twoShort _ hatTag hatArgument _ _ hfailure =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermTwoShortDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)
  | .twoValid _ hatTag hatArgument _ _ hatFunction _ hfunction =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermTwoValidDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hatFunction hfunction)
  | .twoInvalid _ hatTag hatArgument _ _ hatFunction _ hfailure =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermTwoInvalidDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hatFunction hfailure)
  | .invalidTag _ hatTag hatArgument _ _ _ hfailure =>
      syntaxTermEnoughBranchAssemblyPayloadEnvelope tokenTable width tokenCount
        current next binderArity witness
        (syntaxTermNativeShortLePayloadEnvelope 2 current.tokensCount)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 0 witness.tag
          hatTag)
        (syntaxTermNatListAtFixedIndexGraphPayloadEnvelope tokenTable width
          tokenCount current.tokensBoundary current.tokensCount 1
          witness.argument hatArgument)
        (compactSyntaxTermInvalidTagDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)

theorem
    compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness data) <=
      compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData tokenTable
        width tokenCount current next binderArity witness data := by
  cases data with
  | short hcount hfailure =>
      have hle := shortNativeLeCertificate_structuralPayloadBound_le_public
        current.tokensCount 1 hcount
      have hfailureResource :=
        compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure
      have hbranch := syntaxTermShortBranchAssemblyPayloadBound_le tokenTable
        width tokenCount current next witness.tailBoundary witness.tailCount
        (shortNativeLeCertificate current.tokensCount 1 hcount)
        (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next witness.tailBoundary
          witness.tailCount hfailure)
        (nativeShortLeFormula 2 current.tokensCount ⋏
          compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
            tokenCount current.tokensBoundary current.tokensCount witness.tag
            (fixedNumeralTerm 0) ⋏
          compactAdditiveNatListAtRowsAtValuationIndexFormula tokenTable width
            tokenCount current.tokensBoundary current.tokensCount
            witness.argument (fixedNumeralTerm 1) ⋏
          compactUnifiedParserSyntaxTermDecisionExplicitFormula tokenTable
            width tokenCount current next binderArity witness)
        (syntaxTermShortNativeLePayloadEnvelope current.tokensCount 1)
        (compactUnifiedParserSyntaxTermFailureGraphPayloadEnvelope tokenTable
          width tokenCount current next witness.tailBoundary witness.tailCount
          hfailure)
        hle hfailureResource
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionLeft
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (shortNativeLeCertificate current.tokensCount 1 hcount)
            (compactUnifiedParserSyntaxTermFailureExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current next witness.tailBoundary
              witness.tailCount hfailure))) <= _
      unfold syntaxTermShortBranchAssemblyPayloadEnvelope
      exact hbranch
  | zeroSuccess hcount hatTag hatArgument htag hargument hcontinue =>
      have hdecision :=
        compactSyntaxTermZeroSuccessDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness htag
          hargument hcontinue
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermZeroSuccessDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument hcontinue)
        (compactSyntaxTermZeroSuccessDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hcontinue)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermZeroSuccessDecisionCertificate tokenTable
                  width tokenCount current next binderArity witness htag
                  hargument hcontinue))))) <= _
      exact hbranch
  | zeroFailure hcount hatTag hatArgument htag hargument hfailure =>
      have hdecision :=
        compactSyntaxTermZeroFailureDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness htag
          hargument hfailure
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermZeroFailureDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hargument hfailure)
        (compactSyntaxTermZeroFailureDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermZeroFailureDecisionCertificate tokenTable
                  width tokenCount current next binderArity witness htag
                  hargument hfailure))))) <= _
      exact hbranch
  | one hcount hatTag hatArgument htag hcontinue =>
      have hdecision :=
        compactSyntaxTermOneDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness htag
          hcontinue
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermOneDecisionCertificate tokenTable width tokenCount
          current next binderArity witness htag hcontinue)
        (compactSyntaxTermOneDecisionPayloadEnvelope tokenTable width tokenCount
          current next binderArity witness hcontinue)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermOneDecisionCertificate tokenTable width
                  tokenCount current next binderArity witness htag
                  hcontinue))))) <= _
      exact hbranch
  | twoShort hcount hatTag hatArgument htag htooShort hfailure =>
      have hdecision :=
        compactSyntaxTermTwoShortDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness htag
          htooShort hfailure
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermTwoShortDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag htooShort hfailure)
        (compactSyntaxTermTwoShortDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermTwoShortDecisionCertificate tokenTable width
                  tokenCount current next binderArity witness htag htooShort
                  hfailure))))) <= _
      exact hbranch
  | twoValid hcount hatTag hatArgument htag hthree hatFunction hvalid hfunction =>
      have hdecision :=
        compactSyntaxTermTwoValidDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness htag
          hthree hatFunction hvalid hfunction
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermTwoValidDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hvalid hfunction)
        (compactSyntaxTermTwoValidDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hatFunction hfunction)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermTwoValidDecisionCertificate tokenTable width
                  tokenCount current next binderArity witness htag hthree
                  hatFunction hvalid hfunction))))) <= _
      exact hbranch
  | twoInvalid hcount hatTag hatArgument htag hthree hatFunction hinvalid
      hfailure =>
      have hdecision :=
        compactSyntaxTermTwoInvalidDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness htag
          hthree hatFunction hinvalid hfailure
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermTwoInvalidDecisionCertificate tokenTable width
          tokenCount current next binderArity witness htag hthree hatFunction
          hinvalid hfailure)
        (compactSyntaxTermTwoInvalidDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hatFunction hfailure)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermTwoInvalidDecisionCertificate tokenTable
                  width tokenCount current next binderArity witness htag hthree
                  hatFunction hinvalid hfailure))))) <= _
      exact hbranch
  | invalidTag hcount hatTag hatArgument hne0 hne1 hne2 hfailure =>
      have hdecision :=
        compactSyntaxTermInvalidTagDecisionCertificate_structuralPayloadBound_le_public
          tokenTable width tokenCount current next binderArity witness hne0
          hne1 hne2 hfailure
      have hbranch := syntaxTermEnoughBranchFromRowsPayloadBound_le tokenTable
        width tokenCount current next binderArity witness hcount hatTag
        hatArgument
        (compactSyntaxTermInvalidTagDecisionCertificate tokenTable width
          tokenCount current next binderArity witness hne0 hne1 hne2 hfailure)
        (compactSyntaxTermInvalidTagDecisionPayloadEnvelope tokenTable width
          tokenCount current next binderArity witness hfailure)
        hdecision
      unfold
        compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
        compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData
      change hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.disjunctionRight
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (nativeShortLeCertificate 2 current.tokensCount hcount)
            (CheckedHybridValuationBoundedFormulaCertificate.conjunction
              (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                tokenTable width tokenCount current.tokensBoundary
                current.tokensCount 0 witness.tag (fixedNumeralTerm 0)
                (natListAtFixedNumeralTerm_value 0) hatTag)
              (CheckedHybridValuationBoundedFormulaCertificate.conjunction
                (compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
                  tokenTable width tokenCount current.tokensBoundary
                  current.tokensCount 1 witness.argument
                  (fixedNumeralTerm 1) (natListAtFixedNumeralTerm_value 1)
                  hatArgument)
                (compactSyntaxTermInvalidTagDecisionCertificate tokenTable
                  width tokenCount current next binderArity witness hne0 hne1
                  hne2 hfailure))))) <= _
      exact hbranch

noncomputable def
    compactUnifiedParserSyntaxTermExplicitPartsPayloadEnvelopeFromData
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) : Nat :=
  let runningFormula := compactBinaryNatRunningStatusSliceClosedFormula
    tokenTable width tokenCount current.tasksFinish current.finish
  let unconsFormula :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsFormula
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize
      (fixedNumeralTerm 0) (shortBinaryNumeralTerm binderArity)
      (fixedNumeralTerm 0)
  let branchFormula := compactUnifiedParserSyntaxTermBranchExplicitFormula
    tokenTable width tokenCount current next binderArity witness
  let unconsResource :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsGraphPayloadEnvelope
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
      binderArity 0 (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0) hgraph.2.1
  let branchResource :=
    compactUnifiedParserSyntaxTermBranchPayloadEnvelopeFromData tokenTable width
      tokenCount current next binderArity witness data
  let tailResource := transparentHybridConjunctionPayloadEnvelope
    termZeroValuation unconsFormula branchFormula unconsResource branchResource
  transparentHybridConjunctionPayloadEnvelope termZeroValuation runningFormula
    (unconsFormula ⋏ branchFormula)
    (compactBinaryNatRunningStatusSliceStructuralPayloadPolynomial tokenTable
      width tokenCount current.tasksFinish current.finish)
    tailResource

theorem
    compactUnifiedParserSyntaxTermExplicitParts_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness)
    (data : CompactSyntaxTermCheckedBranchData tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (CheckedHybridValuationBoundedFormulaCertificate.conjunction
          (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
            tokenTable width tokenCount current.tasksFinish current.finish
            hgraph.1)
          (CheckedHybridValuationBoundedFormulaCertificate.conjunction
            (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
              tokenTable width tokenCount current.tasksBoundary
              current.tasksCount witness.tailBoundary witness.tailCount
              witness.tailBoundarySize 0 binderArity 0 (fixedNumeralTerm 0)
              (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
              (fun valuation => by simp)
              (fun valuation => by
                simp [termValue_shortBinaryNumeralTerm])
              (fun valuation => by simp) hgraph.2.1)
            (compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
              tokenTable width tokenCount current next binderArity witness
              data))) <=
      compactUnifiedParserSyntaxTermExplicitPartsPayloadEnvelopeFromData
        tokenTable width tokenCount current next binderArity witness hgraph
        data := by
  let runningCertificate :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksFinish current.finish hgraph.1
  let unconsCertificate :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
      binderArity 0 (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      (fun valuation => by simp)
      (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
      (fun valuation => by simp) hgraph.2.1
  let branchCertificate :=
    compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
      tokenTable width tokenCount current next binderArity witness data
  have hrunning :=
    compactBinaryNatRunningStatusSliceExplicitHybridCertificate_structuralPayloadBound_le_public
      tokenTable width tokenCount current.tasksFinish current.finish hgraph.1
  have hheadKindClosed : (fixedNumeralTerm 0).freeVariables = ∅ :=
    fixedNumeralTerm_freeVariables_eq_empty 0
  have hheadBinderArityClosed :
      (shortBinaryNumeralTerm binderArity).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty binderArity
  have hheadRepeatCountClosed : (fixedNumeralTerm 0).freeVariables = ∅ :=
    fixedNumeralTerm_freeVariables_eq_empty 0
  have hheadKindValue : forall valuation,
      termValue valuation (fixedNumeralTerm 0) = 0 := by
    intro valuation
    simp
  have hheadBinderArityValue : forall valuation,
      termValue valuation (shortBinaryNumeralTerm binderArity) = binderArity := by
    intro valuation
    simp [termValue_shortBinaryNumeralTerm]
  have hheadRepeatCountValue : forall valuation,
      termValue valuation (fixedNumeralTerm 0) = 0 := by
    intro valuation
    simp
  have huncons :=
    compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount current.tasksBoundary current.tasksCount
      witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
      binderArity 0 (fixedNumeralTerm 0)
      (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
      hheadKindClosed hheadBinderArityClosed hheadRepeatCountClosed
      hheadKindValue hheadBinderArityValue hheadRepeatCountValue hgraph.2.1
  have hbranch :=
    compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity witness data
  let tailCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      unconsCertificate branchCertificate
  have htail := transparentHybridConjunctionPayloadBound_le unconsCertificate
    branchCertificate _ _ huncons hbranch
  let partsCertificate :=
    CheckedHybridValuationBoundedFormulaCertificate.conjunction
      runningCertificate tailCertificate
  have hparts := transparentHybridConjunctionPayloadBound_le runningCertificate
    tailCertificate _ _ hrunning htail
  unfold compactUnifiedParserSyntaxTermExplicitPartsPayloadEnvelopeFromData
  change hybridFormulaStructuralPayloadBound partsCertificate <= _
  exact hparts

noncomputable def compactUnifiedParserSyntaxTermGraphPayloadEnvelope
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) : Nat :=
  compactUnifiedParserSyntaxTermExplicitPartsPayloadEnvelopeFromData tokenTable
    width tokenCount current next binderArity witness hgraph
    (compactSyntaxTermCheckedBranchDataOfGraph tokenTable width tokenCount
      current next binderArity witness hgraph)

theorem
    compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
    (tokenTable width tokenCount : Nat)
    (current next : CompactUnifiedParserStateRowCoordinates)
    (binderArity : Nat)
    (witness : CompactSyntaxTermTaskWitnessCoordinates)
    (hgraph : CompactUnifiedParserSyntaxTermRows tokenTable width tokenCount
      current next binderArity witness) :
    hybridFormulaStructuralPayloadBound
        (compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current next binderArity witness hgraph) <=
      compactUnifiedParserSyntaxTermGraphPayloadEnvelope tokenTable width
        tokenCount current next binderArity witness hgraph := by
  let data := compactSyntaxTermCheckedBranchDataOfGraph tokenTable width
    tokenCount current next binderArity witness hgraph
  have hparts :=
    compactUnifiedParserSyntaxTermExplicitParts_structuralPayloadBound_le_public
      tokenTable width tokenCount current next binderArity witness hgraph data
  unfold compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph
  simp only [hybridFormulaStructuralPayloadBound]
  unfold compactUnifiedParserSyntaxTermGraphPayloadEnvelope
  change hybridFormulaStructuralPayloadBound
    (CheckedHybridValuationBoundedFormulaCertificate.conjunction
      (compactBinaryNatRunningStatusSliceExplicitHybridCertificateOfGraph
        tokenTable width tokenCount current.tasksFinish current.finish hgraph.1)
      (CheckedHybridValuationBoundedFormulaCertificate.conjunction
        (compactAdditiveSyntaxTaskListUnconsRowsWithSizeAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount current.tasksBoundary current.tasksCount
          witness.tailBoundary witness.tailCount witness.tailBoundarySize 0
          binderArity 0 (fixedNumeralTerm 0)
          (shortBinaryNumeralTerm binderArity) (fixedNumeralTerm 0)
          (fun valuation => by simp)
          (fun valuation => by simp [termValue_shortBinaryNumeralTerm])
          (fun valuation => by simp) hgraph.2.1)
        (compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData
          tokenTable width tokenCount current next binderArity witness data))) <=
    compactUnifiedParserSyntaxTermExplicitPartsPayloadEnvelopeFromData
      tokenTable width tokenCount current next binderArity witness hgraph data
  exact hparts

#print axioms nativeEqCertificate_structuralPayloadBound_le_public
#print axioms nativeNeCertificate_structuralPayloadBound_le_public
#print axioms shortLtCertificate_structuralPayloadBound_le_public
#print axioms termLeCertificate_structuralPayloadBound_le_public
#print axioms shortLeCertificate_structuralPayloadBound_le_public
#print axioms shortNativeLeCertificate_structuralPayloadBound_le_public
#print axioms nativeShortLeCertificate_structuralPayloadBound_le_public
#print axioms syntaxTermShortBranchAssemblyPayloadBound_le
#print axioms syntaxTermEnoughBranchAssemblyPayloadBound_le
#print axioms syntaxTermDecisionExplicitFormula_component_alignment
#print axioms syntaxTermDecisionZeroSuccessPathPayloadBound_le
#print axioms syntaxTermDecisionZeroFailurePathPayloadBound_le
#print axioms syntaxTermDecisionOnePathPayloadBound_le
#print axioms syntaxTermDecisionTwoPathPayloadBound_le
#print axioms syntaxTermDecisionInvalidTagPathPayloadBound_le
#print axioms syntaxTermZeroSuccessSelectedPayloadBound_le
#print axioms syntaxTermZeroFailureSelectedPayloadBound_le
#print axioms syntaxTermOneSelectedPayloadBound_le
#print axioms syntaxTermTwoShortSelectedPayloadBound_le
#print axioms syntaxTermTwoValidSelectedPayloadBound_le
#print axioms syntaxTermTwoInvalidSelectedPayloadBound_le
#print axioms syntaxTermInvalidTagSelectedPayloadBound_le
#print axioms
  compactSyntaxTermZeroSuccessDecisionCertificate_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTermZeroFailureDecisionCertificate_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTermOneDecisionCertificate_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTermTwoShortDecisionCertificate_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTermTwoValidDecisionCertificate_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTermTwoInvalidDecisionCertificate_structuralPayloadBound_le_public
#print axioms
  compactSyntaxTermInvalidTagDecisionCertificate_structuralPayloadBound_le_public
#print axioms syntaxTermEnoughBranchFromRowsPayloadBound_le
#print axioms
  compactUnifiedParserSyntaxTermBranchExplicitHybridCertificateFromData_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxTermExplicitParts_structuralPayloadBound_le_public
#print axioms
  compactUnifiedParserSyntaxTermExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public

end FoundationCompactNumericListedDirectParserSyntaxTermPublicBounds
