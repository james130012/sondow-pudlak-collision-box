import integration.FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicFiniteBounds

/-! Lifting the finite row envelope through the row universal. -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds

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
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerOpenIndexTransparentBounds
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerUniversalPublicBounds
open FoundationCompactPAExplicitHybridUniversalBranchesPolynomialBounds
open FoundationCompactPAContextualTermBoundedUniversalCompiler
open FoundationCompactPAContextualTermBoundedUniversalCompilerBounds
open FoundationCompactPAValuationShiftedBoundCompilerBounds
open FoundationCompactPAExplicitBoundedWitnessHybridTransparentBounds
open FoundationCompactNumericListedDirectAtomicRowEquality
open FoundationCompactNumericListedDirectAtomicRowEqualityPublicBounds
open FoundationCompactNumericListedDirectSyntaxTaskListDropRows
open FoundationCompactNumericListedDirectSyntaxTaskListDropRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev dropFiniteZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation


private theorem dropHybridBranchesUniformEnvelope_mono_leaf
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
      have hinduction := dropHybridBranchesUniformEnvelope_mono_leaf totalBound
        outerVariables valuation body hresource bound
      omega

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat) : Nat :=
  let body := compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable
    width tokenCount sourceBoundary targetBoundary consumed
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue dropFiniteZeroValuation
    (shortBinaryNumeralTerm targetCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    dropFiniteZeroValuation body
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFiniteLeafPayloadResourceSum
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed)
    bound

theorem
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary consumed index) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows <=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
  exact dropHybridBranchesUniformEnvelope_mono_leaf
    (termValue dropFiniteZeroValuation
      (shortBinaryNumeralTerm targetCount))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary consumed)).freeVariables
    dropFiniteZeroValuation
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary consumed)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchPayloadResourceSum_le_publicFinite
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
    (termValue dropFiniteZeroValuation
      (shortBinaryNumeralTerm targetCount))

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat) : Nat :=
  let body := compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable
    width tokenCount sourceBoundary targetBoundary consumed
  let boundTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables dropFiniteZeroValuation
  let bound := termValue dropFiniteZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource dropFiniteZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary consumed index) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows <=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed := by
  let body := compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable
    width tokenCount sourceBoundary targetBoundary consumed
  let boundTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables dropFiniteZeroValuation
  let bound := termValue dropFiniteZeroValuation boundTerm
  let oldCore :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows
  let newCore :=
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed
  let oldBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) oldCore
  let newBranchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body) newCore
  let boundResource := compileShiftedBoundEqualityPayloadResource
    dropFiniteZeroValuation outerVariables boundTerm
  have hcore : oldCore <= newCore := by
    exact
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsBranchesTransparentEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows
  have hbranch : oldBranchResource <= newBranchResource :=
    contextualBranchesUnderBoundPayloadEnvelope_mono
      (Gamma.image Rewriting.shift) bound (Rewriting.free body)
      oldCore newCore hcore
  have htotal := compileContextualTermBoundedUniversalPayloadEnvelope_mono
    Gamma bound (Rew.bShift boundTerm) body boundResource oldBranchResource
    boundResource newBranchResource le_rfl hbranch
  simpa only [
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope,
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

def compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat) : Nat :=
  let countBoundFormula : ValuationFormula :=
    “!!(fixedNumeralTerm consumed) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let countEqualityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm sourceCount) =
      !!(fixedNumeralTerm consumed) +
        !!(shortBinaryNumeralTerm targetCount)”
  let universalFormula : ValuationFormula :=
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary consumed).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityUniversalResource := transparentHybridConjunctionPayloadEnvelope
    dropFiniteZeroValuation countEqualityFormula universalFormula
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount consumed targetCount)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed)
  transparentHybridConjunctionPayloadEnvelope dropFiniteZeroValuation
    countBoundFormula (countEqualityFormula ⋏ universalFormula)
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsCountBoundPayloadPolynomial
      consumed sourceCount)
    equalityUniversalResource

theorem
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (rows : (index : Fin targetCount) ->
      CompactAdditiveSyntaxTaskListDropRowData tokenTable width tokenCount
        sourceBoundary targetBoundary consumed index) :
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed rows <=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed := by
  unfold compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataPayloadEnvelope
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowsUniversalPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows))

theorem
    compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hgraph : CompactAdditiveSyntaxTaskListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount
          targetBoundary targetCount consumed hgraph) <=
      compactAdditiveSyntaxTaskListDropFixedNumeralRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed := by
  exact
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed hgraph).trans
    (compactAdditiveSyntaxTaskListDropFixedNumeralRowsFromRowDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed
      (compactAdditiveSyntaxTaskListDropFixedNumeralRowDataOfGraph tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        consumed hgraph))

end FoundationCompactNumericListedDirectSyntaxTaskListDropFixedNumeralRowsPublicBounds
