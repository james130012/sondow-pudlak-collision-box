import integration.FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicFiniteBounds

/-! Lift the finite natural-list drop envelope through the row universal. -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds

open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
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
open FoundationCompactNumericListedDirectNatListDropRows
open FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate

private abbrev dropFiniteZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsExplicitHybridCertificate.zeroValuation

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

def compactAdditiveNatListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat) : Nat :=
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift (shortBinaryNumeralTerm targetCount)) body
  let outerVariables := outerFormula.freeVariables
  let bound := termValue dropFiniteZeroValuation
    (shortBinaryNumeralTerm targetCount)
  hybridBranchesUniformStructuralPayloadEnvelope bound outerVariables
    dropFiniteZeroValuation body
    (compactAdditiveNatListDropFixedNumeralRowsPublicFiniteLeafPayloadResourceSum
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed)
    bound

theorem
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows <=
      compactAdditiveNatListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed := by
  unfold compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
    compactAdditiveNatListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
  exact dropHybridBranchesUniformEnvelope_mono_leaf
    (termValue dropFiniteZeroValuation
      (shortBinaryNumeralTerm targetCount))
    (∀⁰ termBoundedUniversalBody
      (Rew.bShift (shortBinaryNumeralTerm targetCount))
      (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
        tokenCount sourceBoundary targetBoundary consumed)).freeVariables
    dropFiniteZeroValuation
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width tokenCount
      sourceBoundary targetBoundary consumed)
    (compactAdditiveNatListDropFixedNumeralRowsBranchPayloadResourceSum_le_publicFinite
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows)
    (termValue dropFiniteZeroValuation
      (shortBinaryNumeralTerm targetCount))

def compactAdditiveNatListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat) : Nat :=
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let boundTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables dropFiniteZeroValuation
  let bound := termValue dropFiniteZeroValuation boundTerm
  let branchResource := contextualBranchesUnderBoundPayloadEnvelope
    (Gamma.image Rewriting.shift) bound (Rewriting.free body)
    (compactAdditiveNatListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed)
  compileContextualTermBoundedUniversalPayloadEnvelope
    Gamma bound (Rew.bShift boundTerm) body
    (compileShiftedBoundEqualityPayloadResource dropFiniteZeroValuation
      outerVariables boundTerm)
    branchResource

theorem
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows <=
      compactAdditiveNatListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed := by
  let body := compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
    tokenCount sourceBoundary targetBoundary consumed
  let boundTerm := shortBinaryNumeralTerm targetCount
  let outerFormula := ∀⁰ termBoundedUniversalBody
    (Rew.bShift boundTerm) body
  let outerVariables := outerFormula.freeVariables
  let Gamma := valuationContext outerVariables dropFiniteZeroValuation
  let bound := termValue dropFiniteZeroValuation boundTerm
  let oldCore :=
    compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed rows
  let newCore :=
    compactAdditiveNatListDropFixedNumeralRowsBranchesPublicFiniteEnvelope
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
      compactAdditiveNatListDropFixedNumeralRowsBranchesTransparentEnvelope_le_publicFinite
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
    compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope,
    compactAdditiveNatListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope,
    body, boundTerm, outerFormula, outerVariables, Gamma, bound, oldCore,
    newCore, oldBranchResource, newBranchResource, boundResource] using htotal

def compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
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
    (compactAdditiveNatListDropFixedNumeralRowsBody tokenTable width
      tokenCount sourceBoundary targetBoundary consumed).ballLT
        (shortBinaryNumeralTerm targetCount)
  let equalityUniversalResource := transparentHybridConjunctionPayloadEnvelope
    dropFiniteZeroValuation countEqualityFormula universalFormula
    (compactAdditiveNatListDropFixedNumeralRowsCountEqualityPayloadPolynomial
      sourceCount consumed targetCount)
    (compactAdditiveNatListDropFixedNumeralRowsPublicFiniteUniversalPayloadEnvelope
      tokenTable width tokenCount sourceBoundary targetBoundary targetCount
      consumed)
  transparentHybridConjunctionPayloadEnvelope dropFiniteZeroValuation
    countBoundFormula (countEqualityFormula ⋏ universalFormula)
    (compactAdditiveNatListDropFixedNumeralRowsCountBoundPayloadPolynomial
      consumed sourceCount)
    equalityUniversalResource

theorem
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (rows : (index : Fin targetCount) -> CompactAdditiveNatListDropRowData
      tokenTable width tokenCount sourceBoundary targetBoundary consumed index) :
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed rows <=
      compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed := by
  unfold compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope
    compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (compactAdditiveNatListDropFixedNumeralRowsUniversalPayloadEnvelope_le_publicFinite
        tokenTable width tokenCount sourceBoundary targetBoundary targetCount
        consumed rows))

theorem
    compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed) :
    compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope tokenTable
        width tokenCount sourceBoundary sourceCount targetBoundary targetCount
        consumed hgraph <=
      compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed := by
  unfold compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope
  exact
    compactAdditiveNatListDropFixedNumeralRowsFromRowDataPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed
      (compactAdditiveNatListDropFixedNumeralRowDataOfGraph tokenTable width
        tokenCount sourceBoundary sourceCount targetBoundary targetCount
        consumed hgraph)

theorem
    compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed : Nat)
    (hgraph : CompactAdditiveNatListDropRows tokenTable width tokenCount
      sourceBoundary sourceCount targetBoundary targetCount consumed) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph
          tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
          targetCount consumed hgraph) <=
      compactAdditiveNatListDropFixedNumeralRowsPublicFinitePayloadEnvelope
        tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
        targetCount consumed := by
  exact
    (compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed hgraph).trans
    (compactAdditiveNatListDropFixedNumeralRowsGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount sourceBoundary sourceCount targetBoundary
      targetCount consumed hgraph)

#print axioms
  compactAdditiveNatListDropFixedNumeralRowsExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectNatListDropFixedNumeralRowsPublicBounds
