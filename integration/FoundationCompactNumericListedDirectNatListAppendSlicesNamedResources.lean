import integration.FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial

/-! # Named formulas and resources for the append-slices leaf -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 250000

namespace FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources

open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridThreeConjunctionClosedGeneralBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactPAFixedWidthEntryIndexValuationHybridCompiler
open FoundationCompactNumericListedDirectNatListAppendSlices
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesFormulaFixedBounds
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate

def appendSlicesNamedCountFormula
    (leftCount rightCount targetCount : Nat) : ValuationFormula :=
  “!!(shortBinaryNumeralTerm targetCount) =
    !!(shortBinaryNumeralTerm leftCount) +
      !!(shortBinaryNumeralTerm rightCount)”

def appendSlicesNamedLeftFormula
    (tokenTable width tokenCount leftStart leftFinish leftCount targetStart : Nat) :
    ValuationFormula :=
  compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm leftStart))
    (shortBinaryNumeralTerm leftFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount))

def appendSlicesNamedRightFormula
    (tokenTable width tokenCount rightStart rightFinish leftCount targetStart
      targetFinish : Nat) : ValuationFormula :=
  compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm rightStart))
    (shortBinaryNumeralTerm rightFinish)
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)

noncomputable def appendSlicesNamedLeftResource
    (tokenTable width tokenCount leftStart leftFinish leftCount targetStart : Nat)
    (leftSliceCount : Nat) : Nat :=
  compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
    FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.zeroValuation
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm leftStart))
    (shortBinaryNumeralTerm leftFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount)) leftSliceCount

noncomputable def appendSlicesNamedRightResource
    (tokenTable width tokenCount rightStart rightFinish leftCount targetStart
      targetFinish rightSliceCount : Nat) : Nat :=
  compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
    FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.zeroValuation
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm rightStart))
    (shortBinaryNumeralTerm rightFinish)
    (appendMidpointTerm (shortBinaryNumeralTerm targetStart)
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish) rightSliceCount

noncomputable def compactAdditiveNatListAppendSlicesNamedTransparentEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount) : Nat :=
  let leftSliceCount := Classical.choose hgraph.2.1
  let rightSliceCount := Classical.choose hgraph.2.2
  let countFormula := appendSlicesNamedCountFormula leftCount rightCount
    targetCount
  let leftFormula := appendSlicesNamedLeftFormula tokenTable width tokenCount
    leftStart leftFinish leftCount targetStart
  let rightFormula := appendSlicesNamedRightFormula tokenTable width tokenCount
    rightStart rightFinish leftCount targetStart targetFinish
  let countResource := appendSlicesCountPayloadEnvelope leftCount rightCount
    targetCount
  let leftResource := appendSlicesNamedLeftResource tokenTable width tokenCount
    leftStart leftFinish leftCount targetStart leftSliceCount
  let rightResource := appendSlicesNamedRightResource tokenTable width tokenCount
    rightStart rightFinish leftCount targetStart targetFinish rightSliceCount
  transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.zeroValuation countFormula
    (leftFormula ⋏ rightFormula) countResource
    (transparentHybridConjunctionPayloadEnvelope
      FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate.zeroValuation leftFormula
      rightFormula leftResource rightResource)

noncomputable def compactAdditiveNatListAppendSlicesNamedGeneralEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      rightStart rightFinish rightCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSlices tokenTable width tokenCount
      leftStart leftFinish leftCount rightStart rightFinish rightCount
      targetStart targetFinish targetCount)
    (syntaxResource : Nat) : Nat :=
  let leftSliceCount := Classical.choose hgraph.2.1
  let rightSliceCount := Classical.choose hgraph.2.2
  hybridThreeConjunctionGeneralPayloadEnvelope syntaxResource
    (appendSlicesCountPayloadEnvelope leftCount rightCount targetCount)
    (appendSlicesNamedLeftResource tokenTable width tokenCount leftStart
      leftFinish leftCount targetStart leftSliceCount)
    (appendSlicesNamedRightResource tokenTable width tokenCount rightStart
      rightFinish leftCount targetStart targetFinish rightSliceCount)

end FoundationCompactNumericListedDirectNatListAppendSlicesNamedResources
