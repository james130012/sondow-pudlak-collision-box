import integration.FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectTokenSlicePublicBounds
import integration.FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for a mapped source prefix

All eight checked leaves are charged by public resources derived from the
graph itself.  No caller-supplied payload bound enters the certificate.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 800000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds

open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABitMembershipValuationContextCompilerBounds
open FoundationCompactPAHybridConnectiveTransparentBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompiler
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds
open FoundationCompactPAHybridValuationBoundedFormulaCompilerBounds.CheckedHybridValuationBoundedFormulaCertificate
open FoundationCompactPAValuationAtomicCompilerBounds
open FoundationCompactPAValuationContextRewriting
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAtRowsPublicBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds

private abbrev mappedSourceZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixExplicitHybridCertificate.zeroValuation

private theorem termValue_mappedSourceOne :
    termValue mappedSourceZeroValuation (‘1’ : ValuationTerm) = 1 := by
  exact termValue_one mappedSourceZeroValuation ![]

def mappedSourcePrefixValuationLeStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    mappedSourceZeroValuation
  compilePositiveRelationPayloadResource mappedSourceZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadResource mappedSourceZeroValuation
      Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hle : termValue mappedSourceZeroValuation left <=
      termValue mappedSourceZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (valuationLeCertificate left right hle) <=
      mappedSourcePrefixValuationLeStructuralEnvelope left right := by
  let args : Fin 2 -> ValuationTerm := ![left, right]
  by_cases hequal : termValue mappedSourceZeroValuation left =
      termValue mappedSourceZeroValuation right
  · simp only [valuationLeCertificate]
    rw [dif_pos hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold mappedSourcePrefixValuationLeStructuralEnvelope
    dsimp only [args, mappedSourceZeroValuation]
    omega
  · simp only [valuationLeCertificate]
    rw [dif_neg hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold mappedSourcePrefixValuationLeStructuralEnvelope
    dsimp only [args, mappedSourceZeroValuation]
    omega

def mappedSourcePrefixValuationEqStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource mappedSourceZeroValuation
    Language.Eq.eq ![left, right]

theorem valuationEqCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hequal : termValue mappedSourceZeroValuation left =
      termValue mappedSourceZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (valuationEqCertificate left right hequal) <=
      mappedSourcePrefixValuationEqStructuralEnvelope left right := by
  simp only [valuationEqCertificate, hybridFormulaStructuralPayloadBound,
    mappedSourcePrefixValuationEqStructuralEnvelope]
  exact le_rfl

noncomputable def
    compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) : Nat :=
  let leftSliceCount := Classical.choose hgraph.2.2.2.2.2.1
  let tailSliceCount := Classical.choose hgraph.2.2.2.2.2.2.2
  let headIndexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (shortBinaryNumeralTerm leftCount) = leftCount := by
    simp [termValue_shortBinaryNumeralTerm]
  let positiveFormula : ValuationFormula :=
    “!!(‘1’ : ValuationTerm) ≤
      !!(shortBinaryNumeralTerm prefixCount)”
  let prefixFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm prefixCount) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let sourceWithinFormula : ValuationFormula :=
    “!!(addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm prefixCount)) ≤
      !!(shortBinaryNumeralTerm sourceFinish)”
  let targetFinishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount))”
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount))”
  let leftSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm leftStart))
    (shortBinaryNumeralTerm leftFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm leftCount))
  let headFormula := compactAdditiveNatListAtRowsAtValuationIndexFormula
    tokenTable width tokenCount targetBoundary targetCount mappedHead
    (shortBinaryNumeralTerm leftCount)
  let tailSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)
  let positiveResource := mappedSourcePrefixValuationLeStructuralEnvelope
    (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount)
  let prefixResource := mappedSourcePrefixValuationLeStructuralEnvelope
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount)
  let sourceWithinResource := mappedSourcePrefixValuationLeStructuralEnvelope
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish)
  let targetFinishResource := mappedSourcePrefixValuationEqStructuralEnvelope
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount))
  let countResource := mappedSourcePrefixValuationEqStructuralEnvelope
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount))
  let leftSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount
  let headResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope
      tokenTable width tokenCount targetBoundary targetCount leftCount
      mappedHead (shortBinaryNumeralTerm leftCount) headIndexValue
      hgraph.2.2.2.2.2.2.1
  let tailSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) tailSliceCount
  let headTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
    headFormula tailSliceFormula
    headResource tailSliceResource
  let leftTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation leftSliceFormula
    (headFormula ⋏ tailSliceFormula) leftSliceResource headTailResource
  let countTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation countFormula
    (leftSliceFormula ⋏ (headFormula ⋏ tailSliceFormula))
    countResource leftTailResource
  let targetTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation targetFinishFormula
    (countFormula ⋏ (leftSliceFormula ⋏ (headFormula ⋏ tailSliceFormula)))
    targetFinishResource countTailResource
  let sourceTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation sourceWithinFormula
    (targetFinishFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏
        (headFormula ⋏ tailSliceFormula))))
    sourceWithinResource targetTailResource
  let prefixTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation prefixFormula
    (sourceWithinFormula ⋏ (targetFinishFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏
        (headFormula ⋏ tailSliceFormula)))))
    prefixResource sourceTailResource
  transparentHybridConjunctionPayloadEnvelope mappedSourceZeroValuation
    positiveFormula
    (prefixFormula ⋏ (sourceWithinFormula ⋏ (targetFinishFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏
        (headFormula ⋏ tailSliceFormula))))))
    positiveResource prefixTailResource

noncomputable def
    compactAdditiveNatListAppendMappedSourcePrefixPublicFinitePayloadEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat) : Nat :=
  let positiveFormula : ValuationFormula :=
    “!!(‘1’ : ValuationTerm) ≤
      !!(shortBinaryNumeralTerm prefixCount)”
  let prefixFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm prefixCount) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let sourceWithinFormula : ValuationFormula :=
    “!!(addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm prefixCount)) ≤
      !!(shortBinaryNumeralTerm sourceFinish)”
  let targetFinishFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetFinish) =
      !!(addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount))”
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm targetCount) =
      !!(addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount))”
  let leftSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm leftStart))
    (shortBinaryNumeralTerm leftFinish)
    (successorTerm (shortBinaryNumeralTerm targetStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm leftCount))
  let headFormula := compactAdditiveNatListAtRowsAtValuationIndexFormula
    tokenTable width tokenCount targetBoundary targetCount mappedHead
    (shortBinaryNumeralTerm leftCount)
  let tailSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)
  let positiveResource := mappedSourcePrefixValuationLeStructuralEnvelope
    (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount)
  let prefixResource := mappedSourcePrefixValuationLeStructuralEnvelope
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount)
  let sourceWithinResource := mappedSourcePrefixValuationLeStructuralEnvelope
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish)
  let targetFinishResource := mappedSourcePrefixValuationEqStructuralEnvelope
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount))
  let countResource := mappedSourcePrefixValuationEqStructuralEnvelope
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount))
  let leftSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope
      tokenCount mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
  let headResource :=
    compactAdditiveNatListAtRowsAtValuationIndexPublicFinitePayloadEnvelope
      tokenTable width tokenCount targetBoundary targetCount mappedHead
      (shortBinaryNumeralTerm leftCount)
  let tailSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope
      tokenCount mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
  let headTailResource := transparentHybridConjunctionPayloadEnvelope
    FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
    headFormula tailSliceFormula headResource tailSliceResource
  let leftTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation leftSliceFormula
    (headFormula ⋏ tailSliceFormula) leftSliceResource headTailResource
  let countTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation countFormula
    (leftSliceFormula ⋏ (headFormula ⋏ tailSliceFormula))
    countResource leftTailResource
  let targetTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation targetFinishFormula
    (countFormula ⋏ (leftSliceFormula ⋏ (headFormula ⋏ tailSliceFormula)))
    targetFinishResource countTailResource
  let sourceTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation sourceWithinFormula
    (targetFinishFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏
        (headFormula ⋏ tailSliceFormula))))
    sourceWithinResource targetTailResource
  let prefixTailResource := transparentHybridConjunctionPayloadEnvelope
    mappedSourceZeroValuation prefixFormula
    (sourceWithinFormula ⋏ (targetFinishFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏
        (headFormula ⋏ tailSliceFormula)))))
    prefixResource sourceTailResource
  transparentHybridConjunctionPayloadEnvelope mappedSourceZeroValuation
    positiveFormula
    (prefixFormula ⋏ (sourceWithinFormula ⋏ (targetFinishFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏
        (headFormula ⋏ tailSliceFormula))))))
    positiveResource prefixTailResource

theorem
    compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) :
    compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
        tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
        sourceFinish sourceCount prefixCount targetStart targetFinish
        targetBoundary targetCount mappedHead hgraph <=
      compactAdditiveNatListAppendMappedSourcePrefixPublicFinitePayloadEnvelope
        tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
        sourceFinish sourceCount prefixCount targetStart targetFinish
        targetBoundary targetCount mappedHead := by
  let leftSliceCount := Classical.choose hgraph.2.2.2.2.2.1
  let tailSliceCount := Classical.choose hgraph.2.2.2.2.2.2.2
  let headIndexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (shortBinaryNumeralTerm leftCount) = leftCount := by
    simp [termValue_shortBinaryNumeralTerm]
  have hleftCount : leftSliceCount <= tokenCount := by
    dsimp only [leftSliceCount]
    exact (Classical.choose_spec hgraph.2.2.2.2.2.1).1
  have htailCount : tailSliceCount <= tokenCount := by
    dsimp only [tailSliceCount]
    exact (Classical.choose_spec hgraph.2.2.2.2.2.2.2).1
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_publicFinite
      tokenCount mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCount
  have hheadResource :=
    compactAdditiveNatListAtRowsAtValuationIndexGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount targetBoundary targetCount leftCount
      mappedHead (shortBinaryNumeralTerm leftCount) headIndexValue
      hgraph.2.2.2.2.2.2.1
  have htailResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_publicFinite
      tokenCount mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) tailSliceCount htailCount
  unfold compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
    compactAdditiveNatListAppendMappedSourcePrefixPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
          (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
            (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
              hleftResource
              (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
                hheadResource htailResource))))))

theorem
    compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount
          sourceStart sourceFinish sourceCount prefixCount targetStart
          targetFinish targetBoundary targetCount mappedHead hgraph) <=
      compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope
        tokenTable width tokenCount leftStart leftFinish leftCount
        sourceStart sourceFinish sourceCount prefixCount targetStart
        targetFinish targetBoundary targetCount mappedHead hgraph := by
  rcases hgraph with
    ⟨hpositive, hprefix, hsourceWithin, htargetFinish, hcount,
      hleftSlice, hhead, htailSlice⟩
  let leftSliceCount := Classical.choose hleftSlice
  have hleftSpec :
      leftSliceCount <= tokenCount ∧
      leftFinish = leftStart + 1 + leftSliceCount ∧
      targetStart + 1 + leftCount = targetStart + 1 + leftSliceCount ∧
      leftFinish <= tokenCount ∧
      targetStart + 1 + leftCount <= tokenCount ∧
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using
      Classical.choose_spec hleftSlice
  let tailSliceCount := Classical.choose htailSlice
  have htailSpec :
      tailSliceCount <= tokenCount ∧
      sourceStart + 1 + prefixCount =
        sourceStart + 2 + tailSliceCount ∧
      targetFinish = targetStart + 2 + leftCount + tailSliceCount ∧
      sourceStart + 1 + prefixCount <= tokenCount ∧
      targetFinish <= tokenCount ∧
      ∀ offset < tailSliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((sourceStart + 2 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 2 + leftCount + offset) * width + bitIndex) := by
    simpa [tailSliceCount, Nat.add_assoc] using
      Classical.choose_spec htailSlice
  have hleftCountBound : leftSliceCount <=
      termValue mappedSourceZeroValuation
        (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.1
  have hleftSourceEndpoint : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm leftFinish) =
        termValue mappedSourceZeroValuation
          (successorTerm (shortBinaryNumeralTerm leftStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.1
  have hleftTargetEndpoint : termValue mappedSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) =
        termValue mappedSourceZeroValuation
          (successorTerm (shortBinaryNumeralTerm targetStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.1
  have hleftSourceFinish : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm leftFinish) <=
        termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.1
  have hleftTargetFinish : termValue mappedSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) <=
        termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.2.1
  have hleftBits : ∀ offset < leftSliceCount,
      ∀ bitIndex < termValue mappedSourceZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue mappedSourceZeroValuation
                (successorTerm (shortBinaryNumeralTerm leftStart)) + offset) *
              termValue mappedSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue mappedSourceZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue mappedSourceZeroValuation
                (successorTerm (shortBinaryNumeralTerm targetStart)) +
                  offset) *
              termValue mappedSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hleftSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have htailCountBound : tailSliceCount <=
      termValue mappedSourceZeroValuation
        (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using htailSpec.1
  have htailSourceEndpoint : termValue mappedSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) =
        termValue mappedSourceZeroValuation
          (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm) +
          tailSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm, Nat.add_assoc] using
      htailSpec.2.1
  have htailTargetEndpoint : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue mappedSourceZeroValuation
          (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
            (shortBinaryNumeralTerm leftCount)) + tailSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm, Nat.add_assoc] using
      htailSpec.2.2.1
  have htailSourceFinish : termValue mappedSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) <=
        termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using htailSpec.2.2.2.1
  have htailTargetFinish : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm targetFinish) <=
        termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using
      htailSpec.2.2.2.2.1
  have htailBits : ∀ offset < tailSliceCount,
      ∀ bitIndex < termValue mappedSourceZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue mappedSourceZeroValuation
                (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm) +
                  offset) *
              termValue mappedSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue mappedSourceZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue mappedSourceZeroValuation
                (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
                  (shortBinaryNumeralTerm leftCount)) + offset) *
              termValue mappedSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm, Nat.add_assoc] using
      htailSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have hindexClosed :
      (shortBinaryNumeralTerm leftCount).freeVariables ⊆ {0} := by
    rw [shortBinaryNumeralTerm_freeVariables_eq_empty]
    simp
  have hindexValue : termValue
      FoundationCompactNumericListedDirectNatListAtRowsExplicitHybridCertificate.zeroValuation
      (shortBinaryNumeralTerm leftCount) = leftCount := by
    simp [termValue_shortBinaryNumeralTerm]
  let leftCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  let headCertificate :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph
      tokenTable width tokenCount targetBoundary targetCount leftCount
      mappedHead (shortBinaryNumeralTerm leftCount) hindexValue hhead
  let tailCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) tailSliceCount htailCountBound
      htailSourceEndpoint htailTargetEndpoint htailSourceFinish
      htailTargetFinish htailBits
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  have hheadResource :=
    compactAdditiveNatListAtRowsAtValuationIndexExplicitHybridCertificateOfGraph_structuralPayloadBound_le_public
      tokenTable width tokenCount targetBoundary targetCount leftCount
      mappedHead (shortBinaryNumeralTerm leftCount) hindexClosed hindexValue
      hhead
  have htailResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      mappedSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (addTerm (shortBinaryNumeralTerm sourceStart) twoTerm)
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (addTerm (shortBinaryNumeralTerm targetStart) twoTerm)
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) tailSliceCount htailCountBound
      htailSourceEndpoint htailTargetEndpoint htailSourceFinish
      htailTargetFinish htailBits
  have hpositiveValue : termValue mappedSourceZeroValuation
      (‘1’ : ValuationTerm) <= termValue mappedSourceZeroValuation
        (shortBinaryNumeralTerm prefixCount) := by
    rw [termValue_mappedSourceOne]
    simpa [termValue_shortBinaryNumeralTerm] using hpositive
  have hprefixValue : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm prefixCount) <=
        termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm sourceCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hprefix
  have hsourceWithinValue : termValue mappedSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) <=
        termValue mappedSourceZeroValuation
          (shortBinaryNumeralTerm sourceFinish) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin
  have htargetFinishValue : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue mappedSourceZeroValuation
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm targetCount)) := by
    simpa [termValue_shortBinaryNumeralTerm] using htargetFinish
  have hcountValue : termValue mappedSourceZeroValuation
      (shortBinaryNumeralTerm targetCount) =
        termValue mappedSourceZeroValuation
          (addTerm (shortBinaryNumeralTerm leftCount)
            (shortBinaryNumeralTerm prefixCount)) := by
    simpa [termValue_shortBinaryNumeralTerm] using hcount
  let positiveCertificate := valuationLeCertificate (‘1’ : ValuationTerm)
    (shortBinaryNumeralTerm prefixCount) hpositiveValue
  let prefixCertificate := valuationLeCertificate
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount) hprefixValue
  let sourceWithinCertificate := valuationLeCertificate
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish) hsourceWithinValue
  let targetFinishCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetFinish)
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm targetCount)) htargetFinishValue
  let countCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount)) hcountValue
  have hpositiveResource :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (‘1’ : ValuationTerm) (shortBinaryNumeralTerm prefixCount)
      hpositiveValue
  have hprefixResource :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm prefixCount)
      (shortBinaryNumeralTerm sourceCount) hprefixValue
  have hsourceWithinResource :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (shortBinaryNumeralTerm sourceFinish) hsourceWithinValue
  have htargetFinishResource :=
    valuationEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetFinish)
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm targetCount)) htargetFinishValue
  have hcountResource :=
    valuationEqCertificate_structuralPayloadBound_le_transparent
      (shortBinaryNumeralTerm targetCount)
      (addTerm (shortBinaryNumeralTerm leftCount)
        (shortBinaryNumeralTerm prefixCount)) hcountValue
  let headTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    headCertificate tailCertificate
  have hheadTail := transparentHybridConjunctionPayloadBound_le
    headCertificate tailCertificate _ _ hheadResource htailResource
  let leftTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate headTail
  have hleftTail := transparentHybridConjunctionPayloadBound_le
    leftCertificate headTail _ _ hleftResource hheadTail
  let countTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate leftTail
  have hcountTail := transparentHybridConjunctionPayloadBound_le
    countCertificate leftTail _ _ hcountResource hleftTail
  let targetTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    targetFinishCertificate countTail
  have htargetTail := transparentHybridConjunctionPayloadBound_le
    targetFinishCertificate countTail _ _ htargetFinishResource hcountTail
  let sourceTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sourceWithinCertificate targetTail
  have hsourceTail := transparentHybridConjunctionPayloadBound_le
    sourceWithinCertificate targetTail _ _ hsourceWithinResource htargetTail
  let prefixTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    prefixCertificate sourceTail
  have hprefixTail := transparentHybridConjunctionPayloadBound_le
    prefixCertificate sourceTail _ _ hprefixResource hsourceTail
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    positiveCertificate prefixTail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    positiveCertificate prefixTail _ _ hpositiveResource hprefixTail
  have hcertificate :
      hybridFormulaStructuralPayloadBound
          (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
            tokenTable width tokenCount leftStart leftFinish leftCount
            sourceStart sourceFinish sourceCount prefixCount targetStart
            targetFinish targetBoundary targetCount mappedHead
            ⟨hpositive, hprefix, hsourceWithin, htargetFinish, hcount,
              hleftSlice, hhead, htailSlice⟩) =
        hybridFormulaStructuralPayloadBound direct := by
    simp only [
      compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph,
      hybridFormulaStructuralPayloadBound, leftSliceCount, tailSliceCount,
      leftCertificate, headCertificate, tailCertificate,
      positiveCertificate, prefixCertificate, sourceWithinCertificate,
      targetFinishCertificate, countCertificate, headTail, leftTail,
      countTail, targetTail, sourceTail, prefixTail, direct]
  rw [hcertificate]
  simpa only [
    compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope,
    leftSliceCount, tailSliceCount] using hdirect

theorem
    compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetBoundary targetCount
      mappedHead : Nat)
    (hgraph : CompactAdditiveNatListAppendMappedSourcePrefix
      tokenTable width tokenCount leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount targetStart
      targetFinish targetBoundary targetCount mappedHead) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount
          sourceStart sourceFinish sourceCount prefixCount targetStart
          targetFinish targetBoundary targetCount mappedHead hgraph) <=
      compactAdditiveNatListAppendMappedSourcePrefixPublicFinitePayloadEnvelope
        tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
        sourceFinish sourceCount prefixCount targetStart targetFinish
        targetBoundary targetCount mappedHead := by
  exact
    (compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish
      targetBoundary targetCount mappedHead hgraph).trans
    (compactAdditiveNatListAppendMappedSourcePrefixGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish
      targetBoundary targetCount mappedHead hgraph)

#print axioms valuationLeCertificate_structuralPayloadBound_le_transparent
#print axioms valuationEqCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendMappedSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectNatListAppendMappedSourcePrefixPublicBounds
