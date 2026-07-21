import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
import integration.FoundationCompactNumericListedDirectTokenSlicePublicBounds
import integration.FoundationCompactPAHybridConnectiveTransparentBounds

/-!
# Public structural resource for appending a source prefix

The three arithmetic leaves and both token-slice certificates are exposed as
proof-free child resources.  The two existential slice counts are read from
the checked graph and never replaced by caller-supplied payload bounds.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 600000
set_option Elab.async false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds

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
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds

private abbrev appendSourceZeroValuation : Nat -> Nat :=
  FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate.zeroValuation

def appendSourcePrefixValuationLeStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  let args : Fin 2 -> ValuationTerm := ![left, right]
  let equalityFormula := LO.FirstOrder.Semiformula.rel Language.Eq.eq args
  let strictFormula :=
    LO.FirstOrder.Semiformula.rel Language.ORing.Rel.lt args
  let targetFormula := equalityFormula ⋎ strictFormula
  let Gamma := valuationContext targetFormula.freeVariables
    appendSourceZeroValuation
  compilePositiveRelationPayloadResource appendSourceZeroValuation
      Language.Eq.eq args +
    compilePositiveRelationPayloadResource appendSourceZeroValuation
      Language.ORing.Rel.lt args +
    weakeningFullAssemblyCost (insert equalityFormula Gamma) +
    weakeningFullAssemblyCost (insert strictFormula Gamma) +
    disjunctionFullAssemblyCost Gamma equalityFormula strictFormula

theorem valuationLeCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hle : termValue appendSourceZeroValuation left <=
      termValue appendSourceZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (valuationLeCertificate left right hle) <=
      appendSourcePrefixValuationLeStructuralEnvelope left right := by
  let args : Fin 2 -> ValuationTerm := ![left, right]
  by_cases hequal : termValue appendSourceZeroValuation left =
      termValue appendSourceZeroValuation right
  · simp only [valuationLeCertificate]
    rw [dif_pos hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold appendSourcePrefixValuationLeStructuralEnvelope
    dsimp only [args, appendSourceZeroValuation]
    omega
  · simp only [valuationLeCertificate]
    rw [dif_neg hequal]
    simp only [hybridFormulaStructuralPayloadBound]
    unfold appendSourcePrefixValuationLeStructuralEnvelope
    dsimp only [args, appendSourceZeroValuation]
    omega

def appendSourcePrefixValuationEqStructuralEnvelope
    (left right : ValuationTerm) : Nat :=
  compilePositiveRelationPayloadResource appendSourceZeroValuation
    Language.Eq.eq ![left, right]

theorem valuationEqCertificate_structuralPayloadBound_le_transparent
    (left right : ValuationTerm)
    (hequal : termValue appendSourceZeroValuation left =
      termValue appendSourceZeroValuation right) :
    hybridFormulaStructuralPayloadBound
        (valuationEqCertificate left right hequal) <=
      appendSourcePrefixValuationEqStructuralEnvelope left right := by
  simp only [valuationEqCertificate, hybridFormulaStructuralPayloadBound,
    appendSourcePrefixValuationEqStructuralEnvelope]
  exact le_rfl

noncomputable def compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) : Nat :=
  let leftSliceCount := Classical.choose hgraph.2.2.2.1
  let sourceSliceCount := Classical.choose hgraph.2.2.2.2
  let prefixFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm prefixCount) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let sourceWithinFormula : ValuationFormula :=
    “!!(addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm prefixCount)) ≤
      !!(shortBinaryNumeralTerm sourceFinish)”
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
  let sourceSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm sourceStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)
  let prefixResource := appendSourcePrefixValuationLeStructuralEnvelope
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount)
  let sourceWithinResource := appendSourcePrefixValuationLeStructuralEnvelope
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish)
  let countResource := appendSourcePrefixValuationEqStructuralEnvelope
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount))
  let leftSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      leftSliceCount
  let sourceSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope
      appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      sourceSliceCount
  let slicesResource := transparentHybridConjunctionPayloadEnvelope
    appendSourceZeroValuation leftSliceFormula sourceSliceFormula
    leftSliceResource sourceSliceResource
  let countTailResource := transparentHybridConjunctionPayloadEnvelope
    appendSourceZeroValuation countFormula
    (leftSliceFormula ⋏ sourceSliceFormula) countResource slicesResource
  let sourceTailResource := transparentHybridConjunctionPayloadEnvelope
    appendSourceZeroValuation sourceWithinFormula
    (countFormula ⋏ (leftSliceFormula ⋏ sourceSliceFormula))
    sourceWithinResource countTailResource
  transparentHybridConjunctionPayloadEnvelope appendSourceZeroValuation
    prefixFormula
    (sourceWithinFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏ sourceSliceFormula)))
    prefixResource sourceTailResource

noncomputable def
    compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat) : Nat :=
  let prefixFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm prefixCount) ≤
      !!(shortBinaryNumeralTerm sourceCount)”
  let sourceWithinFormula : ValuationFormula :=
    “!!(addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
          (shortBinaryNumeralTerm prefixCount)) ≤
      !!(shortBinaryNumeralTerm sourceFinish)”
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
  let sourceSliceFormula := compactFixedWidthTokenSlicesEqAtValuationFormula
    (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
    (shortBinaryNumeralTerm tokenCount)
    (successorTerm (shortBinaryNumeralTerm sourceStart))
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
      (shortBinaryNumeralTerm leftCount))
    (shortBinaryNumeralTerm targetFinish)
  let prefixResource := appendSourcePrefixValuationLeStructuralEnvelope
    (shortBinaryNumeralTerm prefixCount)
    (shortBinaryNumeralTerm sourceCount)
  let sourceWithinResource := appendSourcePrefixValuationLeStructuralEnvelope
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish)
  let countResource := appendSourcePrefixValuationEqStructuralEnvelope
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount))
  let leftSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope
      tokenCount appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
  let sourceSliceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPublicFinitePayloadEnvelope
      tokenCount appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
  let slicesResource := transparentHybridConjunctionPayloadEnvelope
    appendSourceZeroValuation leftSliceFormula sourceSliceFormula
    leftSliceResource sourceSliceResource
  let countTailResource := transparentHybridConjunctionPayloadEnvelope
    appendSourceZeroValuation countFormula
    (leftSliceFormula ⋏ sourceSliceFormula) countResource slicesResource
  let sourceTailResource := transparentHybridConjunctionPayloadEnvelope
    appendSourceZeroValuation sourceWithinFormula
    (countFormula ⋏ (leftSliceFormula ⋏ sourceSliceFormula))
    sourceWithinResource countTailResource
  transparentHybridConjunctionPayloadEnvelope appendSourceZeroValuation
    prefixFormula
    (sourceWithinFormula ⋏
      (countFormula ⋏ (leftSliceFormula ⋏ sourceSliceFormula)))
    prefixResource sourceTailResource

theorem
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) :
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
        width tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
        sourceCount prefixCount targetStart targetFinish targetCount hgraph <=
      compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
        tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
        sourceFinish sourceCount prefixCount targetStart targetFinish
        targetCount := by
  let leftSliceCount := Classical.choose hgraph.2.2.2.1
  let sourceSliceCount := Classical.choose hgraph.2.2.2.2
  have hleftCount : leftSliceCount <= tokenCount := by
    dsimp only [leftSliceCount]
    exact (Classical.choose_spec hgraph.2.2.2.1).1
  have hsourceCount : sourceSliceCount <= tokenCount := by
    dsimp only [sourceSliceCount]
    exact (Classical.choose_spec hgraph.2.2.2.2).1
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_publicFinite
      tokenCount appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCount
  have hsourceResource :=
    compactFixedWidthTokenSlicesEqAtValuationPayloadEnvelope_le_publicFinite
      tokenCount appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) sourceSliceCount hsourceCount
  unfold compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
    compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
  exact transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
    (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
      (transparentHybridConjunctionPayloadEnvelope_mono _ _ _ le_rfl
        (transparentHybridConjunctionPayloadEnvelope_mono _ _ _
          hleftResource hsourceResource)))

theorem compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
          sourceFinish sourceCount prefixCount targetStart targetFinish
          targetCount hgraph) <=
      compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
        width tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
        sourceCount prefixCount targetStart targetFinish targetCount hgraph := by
  rcases hgraph with
    ⟨hprefix, hsourceWithin, hcount, hleftSlice, hsourceSlice⟩
  let leftSliceCount := Classical.choose hleftSlice
  have hleftSpec :
      leftSliceCount ≤ tokenCount ∧
      leftFinish = leftStart + 1 + leftSliceCount ∧
      targetStart + 1 + leftCount = targetStart + 1 + leftSliceCount ∧
      leftFinish ≤ tokenCount ∧
      targetStart + 1 + leftCount ≤ tokenCount ∧
      ∀ offset < leftSliceCount, ∀ bitIndex < width,
        tokenTable.testBit ((leftStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + offset) * width + bitIndex) := by
    simpa [leftSliceCount, Nat.add_assoc] using
      Classical.choose_spec hleftSlice
  let sourceSliceCount := Classical.choose hsourceSlice
  have hsourceSpec :
      sourceSliceCount ≤ tokenCount ∧
      sourceStart + 1 + prefixCount =
        sourceStart + 1 + sourceSliceCount ∧
      targetFinish = targetStart + 1 + leftCount + sourceSliceCount ∧
      sourceStart + 1 + prefixCount ≤ tokenCount ∧
      targetFinish ≤ tokenCount ∧
      ∀ offset < sourceSliceCount, ∀ bitIndex < width,
        tokenTable.testBit
            ((sourceStart + 1 + offset) * width + bitIndex) =
          tokenTable.testBit
            ((targetStart + 1 + leftCount + offset) * width + bitIndex) := by
    simpa [sourceSliceCount, Nat.add_assoc] using
      Classical.choose_spec hsourceSlice
  have hleftCountBound : leftSliceCount <= termValue appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.1
  have hleftSourceEndpoint : termValue appendSourceZeroValuation
      (shortBinaryNumeralTerm leftFinish) =
        termValue appendSourceZeroValuation
          (successorTerm (shortBinaryNumeralTerm leftStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.1
  have hleftTargetEndpoint : termValue appendSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) =
        termValue appendSourceZeroValuation
          (successorTerm (shortBinaryNumeralTerm targetStart)) +
          leftSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.1
  have hleftSourceFinish : termValue appendSourceZeroValuation
      (shortBinaryNumeralTerm leftFinish) <=
        termValue appendSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.1
  have hleftTargetFinish : termValue appendSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) <=
        termValue appendSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hleftSpec.2.2.2.2.1
  have hleftBits : ∀ offset < leftSliceCount,
      ∀ bitIndex < termValue appendSourceZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue appendSourceZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSourceZeroValuation
                (successorTerm (shortBinaryNumeralTerm leftStart)) + offset) *
              termValue appendSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue appendSourceZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSourceZeroValuation
                (successorTerm (shortBinaryNumeralTerm targetStart)) + offset) *
              termValue appendSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hleftSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  have hsourceCountBound : sourceSliceCount <=
      termValue appendSourceZeroValuation
        (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.1
  have hsourceSourceEndpoint : termValue appendSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) =
        termValue appendSourceZeroValuation
          (successorTerm (shortBinaryNumeralTerm sourceStart)) +
          sourceSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.1
  have hsourceTargetEndpoint : termValue appendSourceZeroValuation
      (shortBinaryNumeralTerm targetFinish) =
        termValue appendSourceZeroValuation
          (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
            (shortBinaryNumeralTerm leftCount)) + sourceSliceCount := by
    simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.2.1
  have hsourceSourceFinish : termValue appendSourceZeroValuation
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount)) <=
        termValue appendSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using hsourceSpec.2.2.2.1
  have hsourceTargetFinish : termValue appendSourceZeroValuation
      (shortBinaryNumeralTerm targetFinish) <=
        termValue appendSourceZeroValuation
          (shortBinaryNumeralTerm tokenCount) := by
    simpa [termValue_shortBinaryNumeralTerm] using
      hsourceSpec.2.2.2.2.1
  have hsourceBits : ∀ offset < sourceSliceCount,
      ∀ bitIndex < termValue appendSourceZeroValuation
        (shortBinaryNumeralTerm width),
        (termValue appendSourceZeroValuation
          (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSourceZeroValuation
                (successorTerm (shortBinaryNumeralTerm sourceStart)) + offset) *
              termValue appendSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) =
          (termValue appendSourceZeroValuation
            (shortBinaryNumeralTerm tokenTable)).testBit
            ((termValue appendSourceZeroValuation
                (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
                  (shortBinaryNumeralTerm leftCount)) + offset) *
              termValue appendSourceZeroValuation
                (shortBinaryNumeralTerm width) + bitIndex) := by
    intro offset hoffset bitIndex hbitIndex
    have hbitIndex' : bitIndex < width := by
      simpa [termValue_shortBinaryNumeralTerm] using hbitIndex
    simpa [termValue_shortBinaryNumeralTerm] using
      hsourceSpec.2.2.2.2.2 offset hoffset bitIndex hbitIndex'
  let leftCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  let sourceCertificate :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate
      appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) sourceSliceCount
      hsourceCountBound hsourceSourceEndpoint hsourceTargetEndpoint
      hsourceSourceFinish hsourceTargetFinish hsourceBits
  have hleftResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm leftStart))
      (shortBinaryNumeralTerm leftFinish)
      (successorTerm (shortBinaryNumeralTerm targetStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount)) leftSliceCount hleftCountBound
      hleftSourceEndpoint hleftTargetEndpoint hleftSourceFinish
      hleftTargetFinish hleftBits
  have hsourceResource :=
    compactFixedWidthTokenSlicesEqAtValuationExplicitHybridCertificate_structuralPayloadBound_le_transparent
      appendSourceZeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish) sourceSliceCount
      hsourceCountBound hsourceSourceEndpoint hsourceTargetEndpoint
      hsourceSourceFinish hsourceTargetFinish hsourceBits
  let prefixCertificate := valuationLeCertificate
    (shortBinaryNumeralTerm prefixCount) (shortBinaryNumeralTerm sourceCount)
    (by simpa [termValue_shortBinaryNumeralTerm] using hprefix)
  let sourceWithinCertificate := valuationLeCertificate
    (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
      (shortBinaryNumeralTerm prefixCount))
    (shortBinaryNumeralTerm sourceFinish)
    (by simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin)
  let countCertificate := valuationEqCertificate
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount))
    (by simpa [termValue_shortBinaryNumeralTerm] using hcount)
  have hprefixResource := valuationLeCertificate_structuralPayloadBound_le_transparent
    (shortBinaryNumeralTerm prefixCount) (shortBinaryNumeralTerm sourceCount)
    (by simpa [termValue_shortBinaryNumeralTerm] using hprefix)
  have hsourceWithinResource :=
    valuationLeCertificate_structuralPayloadBound_le_transparent
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (shortBinaryNumeralTerm sourceFinish)
      (by simpa [termValue_shortBinaryNumeralTerm] using hsourceWithin)
  have hcountResource := valuationEqCertificate_structuralPayloadBound_le_transparent
    (shortBinaryNumeralTerm targetCount)
    (addTerm (shortBinaryNumeralTerm leftCount)
      (shortBinaryNumeralTerm prefixCount))
    (by simpa [termValue_shortBinaryNumeralTerm] using hcount)
  let slices := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    leftCertificate sourceCertificate
  have hslices := transparentHybridConjunctionPayloadBound_le
    leftCertificate sourceCertificate _ _ hleftResource hsourceResource
  let countTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    countCertificate slices
  have hcountTail := transparentHybridConjunctionPayloadBound_le
    countCertificate slices _ _ hcountResource hslices
  let sourceTail := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    sourceWithinCertificate countTail
  have hsourceTail := transparentHybridConjunctionPayloadBound_le
    sourceWithinCertificate countTail _ _ hsourceWithinResource hcountTail
  let direct := CheckedHybridValuationBoundedFormulaCertificate.conjunction
    prefixCertificate sourceTail
  have hdirect := transparentHybridConjunctionPayloadBound_le
    prefixCertificate sourceTail _ _ hprefixResource hsourceTail
  simpa only [
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph,
    hybridFormulaStructuralPayloadBound,
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope,
    leftSliceCount, sourceSliceCount, leftCertificate, sourceCertificate,
    prefixCertificate, sourceWithinCertificate, countCertificate, slices,
    countTail, sourceTail, direct] using hdirect

theorem
    compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount) :
    hybridFormulaStructuralPayloadBound
        (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph
          tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
          sourceFinish sourceCount prefixCount targetStart targetFinish
          targetCount hgraph) <=
      compactAdditiveNatListAppendSourcePrefixPublicFinitePayloadEnvelope
        tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
        sourceFinish sourceCount prefixCount targetStart targetFinish
        targetCount := by
  exact
    (compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish targetCount
      hgraph).trans
    (compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_publicFinite
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish targetCount
      hgraph)

#print axioms valuationLeCertificate_structuralPayloadBound_le_transparent
#print axioms valuationEqCertificate_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_transparent
#print axioms
  compactAdditiveNatListAppendSourcePrefixExplicitHybridCertificateOfGraph_structuralPayloadBound_le_publicFinite

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
