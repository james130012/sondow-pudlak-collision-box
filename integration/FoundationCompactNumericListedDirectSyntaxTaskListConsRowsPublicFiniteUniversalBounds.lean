import integration.FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicFiniteBounds

/-! Lifting finite syntax-task cons resources through the tail universal. -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactNumericListedDirectSyntaxTaskListConsRows
open FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate

private abbrev consFiniteZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListConsRowsExplicitHybridCertificate.zeroValuation

private theorem consHybridBranchesUniformEnvelope_mono_leaf
    (totalBound : Nat) (outerVariables : Finset Nat)
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    {small large : Nat} (hresource : small <= large) :
    forall bound,
      hybridBranchesUniformStructuralPayloadEnvelope totalBound outerVariables
          valuation body small bound <=
        hybridBranchesUniformStructuralPayloadEnvelope totalBound
          outerVariables valuation body large bound
  | 0 => by rfl
  | bound + 1 => by
      simp only [hybridBranchesUniformStructuralPayloadEnvelope]
      have hinduction := consHybridBranchesUniformEnvelope_mono_leaf totalBound
        outerVariables valuation body hresource bound
      omega

def compactAdditiveSyntaxTaskListConsRowsTailBranchesPublicFiniteEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat) : Nat :=
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm sourceCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue consFiniteZeroValuation
    (shortBinaryNumeralTerm sourceCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    consFiniteZeroValuation body
    (compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteLeafPayloadResourceSum
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary)
    bound

theorem
    compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        rows <=
      compactAdditiveSyntaxTaskListConsRowsTailBranchesPublicFiniteEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary := by
  unfold compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
    compactAdditiveSyntaxTaskListConsRowsTailBranchesPublicFiniteEnvelope
  exact consHybridBranchesUniformEnvelope_mono_leaf
    (termValue consFiniteZeroValuation
      (shortBinaryNumeralTerm sourceCount))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm sourceCount))
      (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
        tokenCount sourceBoundary targetBoundary)).freeVariables
    consFiniteZeroValuation
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary)
    (compactAdditiveSyntaxTaskListConsRowsTailBranchPayloadResourceSum_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      rows)
    (termValue consFiniteZeroValuation
      (shortBinaryNumeralTerm sourceCount))

def compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat) : Nat :=
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables consFiniteZeroValuation
  let bound := termValue consFiniteZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveSyntaxTaskListConsRowsTailBranchesPublicFiniteEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource consFiniteZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary :
      Nat)
    (rows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary rows <=
      compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount
        targetBoundary := by
  let body := compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width
    tokenCount sourceBoundary targetBoundary
  let boundTerm := shortBinaryNumeralTerm sourceCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables consFiniteZeroValuation
  let bound := termValue consFiniteZeroValuation boundTerm
  let oldCore := compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary rows
  let newCore := compactAdditiveSyntaxTaskListConsRowsTailBranchesPublicFiniteEnvelope
    tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    consFiniteZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore := by
    exact
      compactAdditiveSyntaxTaskListConsRowsTailBranchesTransparentEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        rows
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body boundResource oldBranchResource
    boundResource newBranchResource le_rfl hbranch
  simpa only [
    compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope,
    compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

def compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm) :
    Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(shortBinaryNumeralTerm sourceCount) + 1”
  let headFormula :=
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsBody tokenTable
      width tokenCount targetBoundary headKindTerm headBinderArityTerm
      headRepeatCountTerm
  let tailFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListConsRowsTailBody tokenTable width tokenCount
      sourceBoundary targetBoundary).ballLT
        (shortBinaryNumeralTerm sourceCount)
  let headTailResource := transparentHybridConjunctionPayloadEnvelope
    consFiniteZeroValuation headFormula tailFormula
    (compactAdditiveSyntaxTaskListConsRowsHeadPublicFinitePayloadEnvelope
      tokenTable width tokenCount targetBoundary headKind headBinderArity
      headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm)
    (compactAdditiveSyntaxTaskListConsRowsTailPublicFiniteUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary)
  transparentHybridConjunctionPayloadEnvelope consFiniteZeroValuation
    countFormula (headFormula ⋏ tailFormula)
    (compactAdditiveSyntaxTaskListConsRowsCountEqualityPayloadPolynomial
      sourceCount targetCount)
    headTailResource

theorem
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (headData : CompactAdditiveSyntaxTaskListConsHeadData tokenTable width
      tokenCount targetBoundary headKind headBinderArity headRepeatCount)
    (tailRows : (index : Fin sourceCount) ->
      CompactAdditiveSyntaxTaskListConsTailRowData tokenTable width tokenCount
        sourceBoundary targetBoundary index) :
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm headData tailRows <=
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm := by
  unfold
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
      (compactAdditiveSyntaxTaskListConsRowsHeadPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount targetBoundary headKind headBinderArity
        headRepeatCount headKindTerm headBinderArityTerm headRepeatCountTerm
        headData)
      (compactAdditiveSyntaxTaskListConsRowsTailUniversalPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        tailRows))

theorem
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount) :
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm hgraph <=
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm := by
  unfold
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsGraphPayloadEnvelope
  exact
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm
      (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headKind headBinderArity headRepeatCount hgraph)
      (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headKind headBinderArity headRepeatCount hgraph)

theorem
    compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount : Nat)
    (headKindTerm headBinderArityTerm headRepeatCountTerm : ValuationTerm)
    (hheadKindClosed : headKindTerm.freeVariables = ∅)
    (hheadBinderArityClosed : headBinderArityTerm.freeVariables = ∅)
    (hheadRepeatCountClosed : headRepeatCountTerm.freeVariables = ∅)
    (hheadKindValue : ∀ valuation, termValue valuation headKindTerm = headKind)
    (hheadBinderArityValue : ∀ valuation,
      termValue valuation headBinderArityTerm = headBinderArity)
    (hheadRepeatCountValue : ∀ valuation,
      termValue valuation headRepeatCountTerm = headRepeatCount)
    (hgraph : CompactAdditiveSyntaxTaskListConsRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount headKind
      headBinderArity headRepeatCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount headKind headBinderArity headRepeatCount headKindTerm
          headBinderArityTerm headRepeatCountTerm hheadKindValue
          hheadBinderArityValue hheadRepeatCountValue hgraph) <=
      compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount headKind headBinderArity headRepeatCount headKindTerm
        headBinderArityTerm headRepeatCountTerm := by
  exact
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm hheadKindClosed
      hheadBinderArityClosed hheadRepeatCountClosed hheadKindValue
      hheadBinderArityValue hheadRepeatCountValue hgraph).trans
    (compactAdditiveSyntaxTaskListConsRowsAtValuationHeadTermsFromDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount headKind headBinderArity headRepeatCount headKindTerm
      headBinderArityTerm headRepeatCountTerm
      (compactAdditiveSyntaxTaskListConsRowsHeadDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headKind headBinderArity headRepeatCount hgraph)
      (compactAdditiveSyntaxTaskListConsRowsTailRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        headKind headBinderArity headRepeatCount hgraph))

end FoundationCompactNumericListedDirectSyntaxTaskListConsRowsPublicBounds
