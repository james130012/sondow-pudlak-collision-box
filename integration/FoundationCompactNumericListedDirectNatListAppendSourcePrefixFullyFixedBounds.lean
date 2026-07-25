import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixTokenSlicesFixedBounds
import integration.FoundationCompactNumericListedDirectNatListAppendSourcePrefixFormulaFixedBounds
import integration.FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

/-!
# Fully fixed source-prefix append graph payload

The three arithmetic leaves and the two graph-extracted token slices are
assembled in the exact right-associated formula used by the checked append
certificate.  No leaf resource, formula-code bound, or conjunction cost remains
as a caller-supplied parameter.
-/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option maxRecDepth 32768
set_option maxHeartbeats 500000
set_option Elab.async false
set_option autoImplicit false

namespace FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactBinaryNumeralTerm
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactNumericListedDirectArithmeticPrimitives
open FoundationCompactNumericListedDirectNatListAppendSourcePrefix
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixPublicBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixArithmeticFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixTokenSlicesFixedBounds
open FoundationCompactNumericListedDirectNatListAppendSourcePrefixFormulaFixedBounds
open FoundationCompactNumericListedDirectTokenSliceExplicitHybridCertificate
open FoundationCompactNumericListedDirectTokenSlicePublicBounds
open FoundationCompactPAHybridConjunctionGeneralContextBounds
open FoundationCompactPAHybridFiveConjunctionClosedGeneralBounds

def appendSourcePrefixFullyFixedSyntaxPolynomial (bitBound : Nat) : Nat :=
  appendSourcePrefixFullFormulaCodePolynomial bitBound + 1

def appendSourcePrefixFullyFixedPayloadPolynomial
    (numericBound bitBound : Nat) : Nat :=
  let syntaxResource := appendSourcePrefixFullyFixedSyntaxPolynomial bitBound
  let arithmeticResource :=
    appendSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound
  let slicesResource :=
    appendSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound bitBound
  hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
    arithmeticResource arithmeticResource arithmeticResource slicesResource
    slicesResource

theorem compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_fullyFixed
    (tokenTable width tokenCount
      leftStart leftFinish leftCount
      sourceStart sourceFinish sourceCount prefixCount
      targetStart targetFinish targetCount numericBound bitBound : Nat)
    (hgraph : CompactAdditiveNatListAppendSourcePrefix tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount)
    (htableSize : Nat.size tokenTable <= bitBound)
    (hwidthSize : Nat.size width <= bitBound)
    (htokenCountSize : Nat.size tokenCount <= bitBound)
    (hleftStartSize : Nat.size leftStart <= bitBound)
    (hleftFinishSize : Nat.size leftFinish <= bitBound)
    (hleftCountSize : Nat.size leftCount <= bitBound)
    (hsourceStartSize : Nat.size sourceStart <= bitBound)
    (hsourceFinishSize : Nat.size sourceFinish <= bitBound)
    (hsourceCountSize : Nat.size sourceCount <= bitBound)
    (hprefixCountSize : Nat.size prefixCount <= bitBound)
    (htargetStartSize : Nat.size targetStart <= bitBound)
    (htargetFinishSize : Nat.size targetFinish <= bitBound)
    (htargetCountSize : Nat.size targetCount <= bitBound)
    (hwidthBound : width <= numericBound)
    (htokenCountBound : tokenCount <= numericBound)
    (hnumericSize : Nat.size numericBound <= bitBound) :
    compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope tokenTable
        width tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
        sourceCount prefixCount targetStart targetFinish targetCount hgraph <=
      appendSourcePrefixFullyFixedPayloadPolynomial numericBound bitBound := by
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
    (shortBinaryNumeralTerm prefixCount) (shortBinaryNumeralTerm sourceCount)
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
      zeroValuation
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
      zeroValuation
      (shortBinaryNumeralTerm tokenTable) (shortBinaryNumeralTerm width)
      (shortBinaryNumeralTerm tokenCount)
      (successorTerm (shortBinaryNumeralTerm sourceStart))
      (addTerm (successorTerm (shortBinaryNumeralTerm sourceStart))
        (shortBinaryNumeralTerm prefixCount))
      (addTerm (successorTerm (shortBinaryNumeralTerm targetStart))
        (shortBinaryNumeralTerm leftCount))
      (shortBinaryNumeralTerm targetFinish)
      sourceSliceCount
  let syntaxResource := appendSourcePrefixFullyFixedSyntaxPolynomial bitBound
  let arithmeticResource :=
    appendSourcePrefixArithmeticLeavesFixedPayloadPolynomial bitBound
  let slicesResource :=
    appendSourcePrefixTokenSlicesFixedPayloadPolynomial numericBound bitBound
  have harithmetic :=
    appendSourcePrefixArithmeticLeavesResource_le_fixed sourceStart sourceFinish
      sourceCount prefixCount leftCount targetCount bitBound hsourceStartSize
      hsourceFinishSize hsourceCountSize hprefixCountSize hleftCountSize
      htargetCountSize
  have hslices :=
    appendSourcePrefixTokenSlicesResource_le_fixed tokenTable width tokenCount
      leftStart leftFinish leftCount sourceStart sourceFinish sourceCount
      prefixCount targetStart targetFinish targetCount numericBound bitBound
      hgraph htableSize hwidthBound htokenCountBound hnumericSize
  have hprefixResource : prefixResource <= arithmeticResource := by
    dsimp only [prefixResource, sourceWithinResource, countResource,
      arithmeticResource] at harithmetic ⊢
    omega
  have hsourceWithinResource :
      sourceWithinResource <= arithmeticResource := by
    dsimp only [prefixResource, sourceWithinResource, countResource,
      arithmeticResource] at harithmetic ⊢
    omega
  have hcountResource : countResource <= arithmeticResource := by
    dsimp only [prefixResource, sourceWithinResource, countResource,
      arithmeticResource] at harithmetic ⊢
    omega
  have hleftSliceResource : leftSliceResource <= slicesResource := by
    dsimp only [leftSliceCount, sourceSliceCount, leftSliceResource,
      sourceSliceResource, slicesResource] at hslices ⊢
    omega
  have hsourceSliceResource : sourceSliceResource <= slicesResource := by
    dsimp only [leftSliceCount, sourceSliceCount, leftSliceResource,
      sourceSliceResource, slicesResource] at hslices ⊢
    omega
  have hclosed :=
    compactAdditiveNatListAppendSourcePrefixExplicitFormula_closed tokenTable
      width tokenCount leftStart leftFinish leftCount sourceStart sourceFinish
      sourceCount prefixCount targetStart targetFinish targetCount
  have hclosed' :
      (prefixFormula ⋏
        (sourceWithinFormula ⋏
          (countFormula ⋏
            (leftSliceFormula ⋏ sourceSliceFormula)))).freeVariables = ∅ := by
    simpa only [prefixFormula, sourceWithinFormula, countFormula,
      leftSliceFormula, sourceSliceFormula,
      compactAdditiveNatListAppendSourcePrefixExplicitFormula] using hclosed
  have hcodeRaw :=
    compactAdditiveNatListAppendSourcePrefixClosedFormula_code_length_le_fixed
      tokenTable width tokenCount leftStart leftFinish leftCount sourceStart
      sourceFinish sourceCount prefixCount targetStart targetFinish targetCount
      bitBound htableSize hwidthSize htokenCountSize hleftStartSize
      hleftFinishSize hleftCountSize hsourceStartSize hsourceFinishSize
      hsourceCountSize hprefixCountSize htargetStartSize htargetFinishSize
      htargetCountSize
  rw [compactAdditiveNatListAppendSourcePrefixClosedFormula_alignment] at hcodeRaw
  have hcode :
      (binaryFormulaCode
        (prefixFormula ⋏
          (sourceWithinFormula ⋏
            (countFormula ⋏
              (leftSliceFormula ⋏ sourceSliceFormula))))).length <=
        syntaxResource := by
    dsimp only [prefixFormula, sourceWithinFormula, countFormula,
      leftSliceFormula, sourceSliceFormula, syntaxResource,
      compactAdditiveNatListAppendSourcePrefixExplicitFormula] at hcodeRaw ⊢
    unfold appendSourcePrefixFullyFixedSyntaxPolynomial
    omega
  have hpositive : 1 <= syntaxResource := by
    unfold syntaxResource appendSourcePrefixFullyFixedSyntaxPolynomial
    omega
  have hassembly :=
    transparentHybridFiveConjunctionPayloadEnvelope_le_closedGeneral
      zeroValuation prefixFormula sourceWithinFormula countFormula
      leftSliceFormula sourceSliceFormula prefixResource sourceWithinResource
      countResource leftSliceResource sourceSliceResource syntaxResource
      hpositive hclosed' hcode
  have hresourceMono :
      hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource prefixResource
          sourceWithinResource countResource leftSliceResource
          sourceSliceResource <=
        hybridFiveConjunctionGeneralPayloadEnvelope syntaxResource
          arithmeticResource arithmeticResource arithmeticResource
          slicesResource slicesResource := by
    unfold hybridFiveConjunctionGeneralPayloadEnvelope
      hybridConjunctionGeneralPayloadEnvelope
    omega
  unfold compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope
    appendSourcePrefixFullyFixedPayloadPolynomial
  simpa only [leftSliceCount, sourceSliceCount, prefixFormula,
    sourceWithinFormula, countFormula, leftSliceFormula, sourceSliceFormula,
    prefixResource, sourceWithinResource, countResource, leftSliceResource,
    sourceSliceResource, syntaxResource, arithmeticResource, slicesResource]
    using hassembly.trans hresourceMono

#print axioms
  compactAdditiveNatListAppendSourcePrefixGraphPayloadEnvelope_le_fullyFixed

end FoundationCompactNumericListedDirectNatListAppendSourcePrefixFullyFixedBounds
