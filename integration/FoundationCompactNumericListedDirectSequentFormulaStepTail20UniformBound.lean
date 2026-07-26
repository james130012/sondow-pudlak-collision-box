import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedAppendLeaf
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Row-independent resource for the final two sequent-step leaves -/

open LO FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail20UniformBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedProof
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf

def compactSequentFormulaStepTail20UniformAppendNumericBound
    (width tokenCount : Nat) : Nat :=
  width + tokenCount + tokenCount + tokenCount + 1

def compactSequentFormulaStepTail20UniformAppendBitBound
    (tokenTable width tokenCount : Nat) : Nat :=
  Nat.size tokenTable +
    Nat.size
      (compactSequentFormulaStepTail20UniformAppendNumericBound width tokenCount) +
    1

def compactSequentFormulaStepTail20UniformSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat) : Nat :=
  appendSlicesFullyFixedPayloadPolynomial
      (compactSequentFormulaStepTail20UniformAppendNumericBound width tokenCount)
      (compactSequentFormulaStepTail20UniformAppendBitBound tokenTable width
        tokenCount) +
    compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
      valueCount +
    (binaryNatCode 4).length + 4

def compactSequentFormulaStepTail20UniformPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat) : Nat :=
  appendSlicesFullyFixedPayloadPolynomial
      (compactSequentFormulaStepTail20UniformAppendNumericBound width tokenCount)
      (compactSequentFormulaStepTail20UniformAppendBitBound tokenTable width
        tokenCount) +
    compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
      valueCount +
    smallContextAssemblyEnvelope
      (compactSequentFormulaStepTail20UniformSyntaxPolynomial tokenTable width
        tokenCount suffixCount valueCount)

noncomputable def compactSequentFormulaStepTail20UniformBoundOfGraph
    (tokenTable width tokenCount suffixBoundary suffixCount valueBoundary
      valueCount rowIndex : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (hgraph : CompactSequentFormulaStepGraph tokenTable width tokenCount
      suffixBoundary suffixCount valueBoundary valueCount rowIndex row) :
    ClosedDirectFormulaBound
      ((compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
          tokenCount row.value.start row.value.finish row.value.count
          row.next.start row.next.finish row.next.count row.current.start
          row.current.finish row.current.count) ⋏
        (“!!(shortBinaryNumeralTerm suffixCount) =
          !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula))
      (compactSequentFormulaStepTail20UniformPayloadPolynomial tokenTable width
        tokenCount suffixCount valueCount) := by
  rcases hgraph with
    ⟨_, _, hcurrentCount, _, _, hnextCount, _, _, _, _, _, _, _, _, _, _, _,
      _, _, happend, hcount⟩
  let appendNumeric :=
    compactSequentFormulaStepTail20UniformAppendNumericBound width tokenCount
  let appendBit :=
    compactSequentFormulaStepTail20UniformAppendBitBound tokenTable width
      tokenCount
  have hwidthAppend : width <= appendNumeric := by
    unfold appendNumeric
      compactSequentFormulaStepTail20UniformAppendNumericBound
    omega
  have htokenCountAppend : tokenCount <= appendNumeric := by
    unfold appendNumeric
      compactSequentFormulaStepTail20UniformAppendNumericBound
    omega
  have hrightCountAppend : row.next.count <= appendNumeric := by
    unfold appendNumeric
      compactSequentFormulaStepTail20UniformAppendNumericBound
    omega
  have htargetCountAppend : row.current.count <= appendNumeric := by
    unfold appendNumeric
      compactSequentFormulaStepTail20UniformAppendNumericBound
    omega
  have htableSizeAppend : Nat.size tokenTable <= appendBit := by
    unfold appendBit compactSequentFormulaStepTail20UniformAppendBitBound
    omega
  have hnumericSizeAppend : Nat.size appendNumeric <= appendBit := by
    change Nat.size appendNumeric <=
      Nat.size tokenTable + Nat.size appendNumeric + 1
    omega
  let appendExists :=
    exists_compactAdditiveNatListAppendSlicesFullyFixedPAProof tokenTable width
      tokenCount row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count row.current.start
      row.current.finish row.current.count appendNumeric appendBit happend
      htableSizeAppend hwidthAppend htokenCountAppend hrightCountAppend
      htargetCountAppend hnumericSizeAppend
  let append : ClosedDirectFormulaBound
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount row.value.start row.value.finish row.value.count
        row.next.start row.next.finish row.next.count row.current.start
        row.current.finish row.current.count)
      (appendSlicesFullyFixedPayloadPolynomial appendNumeric appendBit) :=
    { proof := Classical.choose appendExists
      payloadLength_le := Classical.choose_spec appendExists }
  have happendPayload :
      append.proof.payloadLength <=
        appendSlicesFullyFixedPayloadPolynomial appendNumeric appendBit := by
    simpa only [append] using (Classical.choose_spec appendExists)
  let countExists :=
    exists_compactSequentFormulaStepTail16FixedCountLeaf suffixCount valueCount
      hcount
  let countProof := Classical.choose countExists
  have hcountPayload := Classical.choose_spec countExists
  have hcountPayload' : countProof.payloadLength <=
      compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
        valueCount := by
    simpa only [countProof] using hcountPayload
  let syntaxResource :=
    compactSequentFormulaStepTail20UniformSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount
  let appendFormula :=
    compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      row.value.start row.value.finish row.value.count row.next.start
      row.next.finish row.next.count row.current.start row.current.finish
      row.current.count
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1”
  let proof := CertifiedPAContextProof.conjunction append.proof countProof
  have happendCode :=
    CertifiedPAContextProof.conclusionCodeLength_le_payloadLength append.proof
  have hcountCode :=
    CertifiedPAContextProof.conclusionCodeLength_le_payloadLength countProof
  have happendSyntax :
      (binaryFormulaCode appendFormula).length <= syntaxResource := by
    have hresource :
        appendSlicesFullyFixedPayloadPolynomial appendNumeric appendBit <=
          syntaxResource := by
      dsimp only [syntaxResource, appendNumeric, appendBit]
      unfold compactSequentFormulaStepTail20UniformSyntaxPolynomial
      omega
    simpa only [appendFormula] using
      happendCode.trans (happendPayload.trans hresource)
  have hcountSyntax :
      (binaryFormulaCode countFormula).length <= syntaxResource := by
    have hresource :
        compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
            valueCount <= syntaxResource := by
      dsimp only [syntaxResource, appendNumeric, appendBit]
      unfold compactSequentFormulaStepTail20UniformSyntaxPolynomial
      omega
    simpa only [countFormula] using
      hcountCode.trans (hcountPayload'.trans hresource)
  have hconjunctionSyntax :
      (binaryFormulaCode (appendFormula ⋏ countFormula)).length <=
        syntaxResource := by
    have happendCodePayload :
        (binaryFormulaCode appendFormula).length <=
          appendSlicesFullyFixedPayloadPolynomial appendNumeric appendBit := by
      simpa only [appendFormula] using
        happendCode.trans happendPayload
    have happendCodePayloadUniform :
        (binaryFormulaCode appendFormula).length <=
          appendSlicesFullyFixedPayloadPolynomial
            (compactSequentFormulaStepTail20UniformAppendNumericBound width
              tokenCount)
            (compactSequentFormulaStepTail20UniformAppendBitBound tokenTable width
              tokenCount) := by
      simpa only [appendNumeric, appendBit] using happendCodePayload
    have hcountCodePayload :
        (binaryFormulaCode countFormula).length <=
          compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
            valueCount := by
      simpa only [countFormula] using
        hcountCode.trans hcountPayload'
    simp only [binaryFormulaCode, List.length_append]
    dsimp only [syntaxResource, appendNumeric, appendBit]
    unfold compactSequentFormulaStepTail20UniformSyntaxPolynomial
    omega
  have hcost := conjunctionFullAssemblyCost_le_small ∅ appendFormula
    countFormula syntaxResource (by simp) (by
      intro formula hmem
      simp at hmem) happendSyntax hcountSyntax hconjunctionSyntax
  have hassembly := CertifiedPAContextProof.conjunction_payloadLength_le
    append.proof countProof
  have hassembly' : proof.payloadLength <=
      append.proof.payloadLength + countProof.payloadLength +
        CertifiedPAContextProof.conjunctionFullAssemblyCost ∅ appendFormula
          countFormula := by
    simpa only [proof] using hassembly
  refine { proof := proof, payloadLength_le := ?_ }
  have hproof : proof.payloadLength <=
      appendSlicesFullyFixedPayloadPolynomial appendNumeric appendBit +
        compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
          valueCount +
        smallContextAssemblyEnvelope syntaxResource := by
    calc
      proof.payloadLength <= append.proof.payloadLength +
          countProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
              appendFormula countFormula := hassembly'
      _ <= _ := by omega
  simpa only [compactSequentFormulaStepTail20UniformPayloadPolynomial,
    syntaxResource, appendNumeric, appendBit, appendFormula, countFormula] using
    hproof

#print axioms compactSequentFormulaStepTail20UniformBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepTail20UniformBound
