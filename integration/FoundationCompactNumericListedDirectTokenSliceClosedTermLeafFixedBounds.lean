import integration.FoundationCompactNumericListedDirectTokenSlicePostWitnessClosedTermAtomicFixedBounds
import integration.FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalEndpointFixedBounds

/-!
# Token-slice resources with all semantic leaves fixed

This module replaces the five post-witness atomic resources and the complete
offset universal by fixed public bounds while preserving the original
conjunction and existential assembly syntax.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectTokenSliceClosedTermLeafFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompilerPublicBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSlicePostWitnessClosedTermAtomicFixedBounds
open FoundationCompactNumericListedDirectTokenSliceOffsetClosedTermUniversalEndpointFixedBounds

def tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count numericBound termCode bitBound : Nat) : Nat :=
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm count) < !!tokenCountTerm + 1”
  let sourceEndpointFormula : ValuationFormula :=
    “!!sourceFinishTerm =
      !!sourceStartTerm + !!(shortBinaryNumeralTerm count)”
  let targetEndpointFormula : ValuationFormula :=
    “!!targetFinishTerm =
      !!targetStartTerm + !!(shortBinaryNumeralTerm count)”
  let sourceFinishFormula : ValuationFormula :=
    “!!sourceFinishTerm ≤ !!tokenCountTerm”
  let targetFinishFormula : ValuationFormula :=
    “!!targetFinishTerm ≤ !!tokenCountTerm”
  let offsetFormula := tokenSliceAtValuationOffsetUniversalFormula
    tokenTableTerm widthTerm sourceStartTerm targetStartTerm count
  let atomicResource :=
    tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
      termCode
  let leResource :=
    tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial termCode
  let offsetResource :=
    tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
      numericBound termCode bitBound
  let targetFinishTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation targetFinishFormula offsetFormula leResource offsetResource
  let sourceFinishTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation sourceFinishFormula (targetFinishFormula ⋏ offsetFormula)
    leResource targetFinishTailResource
  let targetEndpointTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation targetEndpointFormula
    (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula))
    atomicResource sourceFinishTailResource
  let sourceEndpointTailResource := transparentHybridConjunctionPayloadEnvelope
    valuation sourceEndpointFormula
    (targetEndpointFormula ⋏
      (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula)))
    atomicResource targetEndpointTailResource
  transparentHybridConjunctionPayloadEnvelope valuation countFormula
    (sourceEndpointFormula ⋏
      (targetEndpointFormula ⋏
        (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula))))
    atomicResource sourceEndpointTailResource

theorem tokenSliceAtValuationPostWitnessPayloadEnvelope_le_closedLeafFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm : ValuationTerm)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode)
    (htokenCountCode : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStartCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinishCode : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStartCode : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinishCode : (binaryTermCode targetFinishTerm).length <= termCode)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hsourceStartClosed : sourceStartTerm.freeVariables = ∅)
    (hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅)
    (htargetStartClosed : targetStartTerm.freeVariables = ∅)
    (htargetFinishClosed : targetFinishTerm.freeVariables = ∅)
    (hwidth : width <= numericBound)
    (hsourceStart : termValue valuation sourceStartTerm <= numericBound)
    (htargetStart : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    tokenSliceAtValuationPostWitnessPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count <=
      tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count numericBound
        termCode bitBound := by
  have hcountClosed :
      (shortBinaryNumeralTerm count : ValuationTerm).freeVariables = ∅ :=
    shortBinaryNumeralTerm_freeVariables_eq_empty count
  have hcountResource :=
    tokenSliceAtValuationCountGuardStructuralEnvelope_le_closedFixed valuation
      tokenCountTerm count termCode htokenCountClosed hcountClosed
      htokenCountCode hcountCode
  have hsourceEndpointResource :=
    tokenSliceAtValuationEndpointStructuralEnvelope_le_closedFixed valuation
      sourceStartTerm sourceFinishTerm count termCode hsourceStartClosed
      hsourceFinishClosed hcountClosed hsourceStartCode hsourceFinishCode
      hcountCode
  have htargetEndpointResource :=
    tokenSliceAtValuationEndpointStructuralEnvelope_le_closedFixed valuation
      targetStartTerm targetFinishTerm count termCode htargetStartClosed
      htargetFinishClosed hcountClosed htargetStartCode htargetFinishCode
      hcountCode
  have hsourceFinishResource :=
    tokenSliceAtValuationLeStructuralEnvelope_le_closedFixed valuation
      sourceFinishTerm tokenCountTerm termCode hsourceFinishClosed
      htokenCountClosed hsourceFinishCode htokenCountCode
  have htargetFinishResource :=
    tokenSliceAtValuationLeStructuralEnvelope_le_closedFixed valuation
      targetFinishTerm tokenCountTerm termCode htargetFinishClosed
      htokenCountClosed htargetFinishCode htokenCountCode
  have hoffsetResource :=
    tokenSliceAtValuationOffsetUniversalPayloadEnvelope_le_closedFixed valuation
      tokenTable width count numericBound termCode bitBound sourceStartTerm
      targetStartTerm hsourceStartClosed htargetStartClosed htableCode
      hwidthCode hsourceStartCode htargetStartCode hwidth hsourceStart
      htargetStart hcount htableSize hwidthSize hnumericSize
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm count) < !!tokenCountTerm + 1”
  let sourceEndpointFormula : ValuationFormula :=
    “!!sourceFinishTerm =
      !!sourceStartTerm + !!(shortBinaryNumeralTerm count)”
  let targetEndpointFormula : ValuationFormula :=
    “!!targetFinishTerm =
      !!targetStartTerm + !!(shortBinaryNumeralTerm count)”
  let sourceFinishFormula : ValuationFormula :=
    “!!sourceFinishTerm ≤ !!tokenCountTerm”
  let targetFinishFormula : ValuationFormula :=
    “!!targetFinishTerm ≤ !!tokenCountTerm”
  let offsetFormula := tokenSliceAtValuationOffsetUniversalFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    sourceStartTerm targetStartTerm count
  let atomicResource :=
    tokenSlicePostWitnessClosedTermPositiveAtomicFixedPayloadPolynomial
      termCode
  let leResource :=
    tokenSlicePostWitnessClosedTermLeFixedPayloadPolynomial termCode
  let offsetResource :=
    tokenSliceClosedTermOffsetUniversalFullyFixedPayloadPolynomial
      numericBound termCode bitBound
  have htargetFinishTail :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation
      targetFinishFormula offsetFormula htargetFinishResource hoffsetResource
  have hsourceFinishTail :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation
      sourceFinishFormula (targetFinishFormula ⋏ offsetFormula)
      hsourceFinishResource htargetFinishTail
  have htargetEndpointTail :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation
      targetEndpointFormula
      (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula))
      htargetEndpointResource hsourceFinishTail
  have hsourceEndpointTail :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation
      sourceEndpointFormula
      (targetEndpointFormula ⋏
        (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula)))
      hsourceEndpointResource htargetEndpointTail
  have htotal :=
    transparentHybridConjunctionPayloadEnvelope_mono valuation countFormula
      (sourceEndpointFormula ⋏
        (targetEndpointFormula ⋏
          (sourceFinishFormula ⋏ (targetFinishFormula ⋏ offsetFormula))))
      hcountResource hsourceEndpointTail
  simpa only [tokenSliceAtValuationPostWitnessPayloadEnvelope,
    tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial, countFormula,
    sourceEndpointFormula, targetEndpointFormula, sourceFinishFormula,
    targetFinishFormula, offsetFormula, atomicResource, leResource,
    offsetResource] using htotal

private theorem hybridExistsWitnessStructuralPayloadEnvelope_mono_closed
    (valuation : Nat -> Nat)
    (body : LO.FirstOrder.ArithmeticSemiformula Nat 1)
    (witness : Nat) {small large : Nat} (hresource : small <= large) :
    hybridExistsWitnessStructuralPayloadEnvelope valuation body witness small <=
      hybridExistsWitnessStructuralPayloadEnvelope valuation body witness
        large := by
  unfold hybridExistsWitnessStructuralPayloadEnvelope
  dsimp only
  omega

def compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial
    (valuation : Nat -> Nat)
    (tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm : ValuationTerm)
    (count numericBound termCode bitBound : Nat) : Nat :=
  hybridExistsWitnessStructuralPayloadEnvelope valuation
    (tokenSliceAtValuationWitnessBody tokenTableTerm widthTerm tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm)
    count
    (tokenSliceClosedTermPostWitnessLeafFixedPayloadPolynomial valuation
      tokenTableTerm widthTerm tokenCountTerm sourceStartTerm sourceFinishTerm
      targetStartTerm targetFinishTerm count numericBound termCode bitBound)

theorem
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedLeafFixed
    (valuation : Nat -> Nat)
    (tokenTable width count numericBound termCode bitBound : Nat)
    (tokenCountTerm sourceStartTerm sourceFinishTerm targetStartTerm
      targetFinishTerm : ValuationTerm)
    (htableCode :
      (binaryTermCode (shortBinaryNumeralTerm tokenTable)).length <= termCode)
    (hwidthCode :
      (binaryTermCode (shortBinaryNumeralTerm width)).length <= termCode)
    (hcountCode :
      (binaryTermCode (shortBinaryNumeralTerm count)).length <= termCode)
    (htokenCountCode : (binaryTermCode tokenCountTerm).length <= termCode)
    (hsourceStartCode : (binaryTermCode sourceStartTerm).length <= termCode)
    (hsourceFinishCode : (binaryTermCode sourceFinishTerm).length <= termCode)
    (htargetStartCode : (binaryTermCode targetStartTerm).length <= termCode)
    (htargetFinishCode : (binaryTermCode targetFinishTerm).length <= termCode)
    (htokenCountClosed : tokenCountTerm.freeVariables = ∅)
    (hsourceStartClosed : sourceStartTerm.freeVariables = ∅)
    (hsourceFinishClosed : sourceFinishTerm.freeVariables = ∅)
    (htargetStartClosed : targetStartTerm.freeVariables = ∅)
    (htargetFinishClosed : targetFinishTerm.freeVariables = ∅)
    (hwidth : width <= numericBound)
    (hsourceStart : termValue valuation sourceStartTerm <= numericBound)
    (htargetStart : termValue valuation targetStartTerm <= numericBound)
    (hcount : count <= numericBound)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope valuation
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count <=
      compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial
        valuation (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm count numericBound
        termCode bitBound := by
  have hpost :=
    tokenSliceAtValuationPostWitnessPayloadEnvelope_le_closedLeafFixed valuation
      tokenTable width count numericBound termCode bitBound tokenCountTerm
      sourceStartTerm sourceFinishTerm targetStartTerm targetFinishTerm
      htableCode hwidthCode hcountCode htokenCountCode hsourceStartCode hsourceFinishCode
      htargetStartCode htargetFinishCode htokenCountClosed hsourceStartClosed
      hsourceFinishClosed htargetStartClosed htargetFinishClosed hwidth
      hsourceStart htargetStart hcount htableSize hwidthSize hnumericSize
  simpa only [compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope,
    compactFixedWidthTokenSlicesEqAtValuationClosedTermLeafFixedPayloadPolynomial]
    using hybridExistsWitnessStructuralPayloadEnvelope_mono_closed valuation
      (tokenSliceAtValuationWitnessBody
        (shortBinaryNumeralTerm tokenTable)
        (shortBinaryNumeralTerm width) tokenCountTerm sourceStartTerm
        sourceFinishTerm targetStartTerm targetFinishTerm) count hpost

#print axioms
  tokenSliceAtValuationPostWitnessPayloadEnvelope_le_closedLeafFixed
#print axioms
  compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_closedLeafFixed

end FoundationCompactNumericListedDirectTokenSliceClosedTermLeafFixedBounds
