import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedAppendLeaf
import integration.FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Fully fixed final two leaves of one sequent-formula step -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 300000

namespace FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactNumericListedDirectNatListAppendSlicesExplicitHybridCertificate
open FoundationCompactNumericListedDirectNatListAppendSlicesFullyFixedPolynomial
open FoundationCompactNumericListedDirectParserStateCoreFullyUniformDirectCompiler
open FoundationCompactNumericListedDirectSequentFormulaStepFormula
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedAppendLeaf
open FoundationCompactNumericListedDirectSequentFormulaStepTail16FixedCountLeaf

def compactSequentFormulaStepTail20FullyFixedSyntaxPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  appendSlicesFullyFixedPayloadPolynomial
      (compactSequentFormulaStepTail16AppendNumericBound width tokenCount
        row.next.count row.current.count)
      (compactSequentFormulaStepTail16AppendBitBound tokenTable width tokenCount
        row.next.count row.current.count) +
    compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
      valueCount + (binaryNatCode 4).length + 4

def compactSequentFormulaStepTail20FullyFixedPayloadPolynomial
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates) : Nat :=
  let syntaxResource :=
    compactSequentFormulaStepTail20FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount row
  appendSlicesFullyFixedPayloadPolynomial
      (compactSequentFormulaStepTail16AppendNumericBound width tokenCount
        row.next.count row.current.count)
      (compactSequentFormulaStepTail16AppendBitBound tokenTable width tokenCount
        row.next.count row.current.count) +
    compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
      valueCount + smallContextAssemblyEnvelope syntaxResource

noncomputable def compactSequentFormulaStepTail20FullyFixedBoundOfLeaves
    (tokenTable width tokenCount suffixCount valueCount : Nat)
    (row : CompactSequentFormulaStepCoordinates)
    (append : ClosedDirectFormulaBound
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount row.value.start row.value.finish row.value.count
        row.next.start row.next.finish row.next.count row.current.start
        row.current.finish row.current.count)
      (appendSlicesFullyFixedPayloadPolynomial
        (compactSequentFormulaStepTail16AppendNumericBound width tokenCount
          row.next.count row.current.count)
        (compactSequentFormulaStepTail16AppendBitBound tokenTable width
          tokenCount row.next.count row.current.count)))
    (countProof : CertifiedPAContextProof ∅
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula))
    (hcountPayload : countProof.payloadLength <=
      compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
        valueCount) :
    ClosedDirectFormulaBound
      ((compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
          tokenCount row.value.start row.value.finish row.value.count
          row.next.start row.next.finish row.next.count row.current.start
          row.current.finish row.current.count) ⋏
        (“!!(shortBinaryNumeralTerm suffixCount) =
          !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula))
      (compactSequentFormulaStepTail20FullyFixedPayloadPolynomial tokenTable
        width tokenCount suffixCount valueCount row) := by
  let syntaxResource :=
    compactSequentFormulaStepTail20FullyFixedSyntaxPolynomial tokenTable width
      tokenCount suffixCount valueCount row
  let appendFormula :=
    compactAdditiveNatListAppendSlicesClosedFormula tokenTable width tokenCount
      row.value.start row.value.finish row.value.count
      row.next.start row.next.finish row.next.count
      row.current.start row.current.finish row.current.count
  let countFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm suffixCount) =
      !!(shortBinaryNumeralTerm valueCount) + 1”
  let proof := CertifiedPAContextProof.conjunction append.proof countProof
  have happendCode :=
    CertifiedPAContextProof.conclusionCodeLength_le_payloadLength append.proof
  have hcountCode :=
    CertifiedPAContextProof.conclusionCodeLength_le_payloadLength countProof
  have happendPayload := append.payloadLength_le
  have happendLeafCode := happendCode.trans happendPayload
  have hcountLeafCode := hcountCode.trans hcountPayload
  have happendSyntax :
      (binaryFormulaCode appendFormula).length <= syntaxResource := by
    exact happendCode.trans (append.payloadLength_le.trans (by
      unfold syntaxResource
        compactSequentFormulaStepTail20FullyFixedSyntaxPolynomial
      omega))
  have hcountSyntax :
      (binaryFormulaCode countFormula).length <= syntaxResource := by
    exact hcountCode.trans (hcountPayload.trans (by
      unfold syntaxResource
        compactSequentFormulaStepTail20FullyFixedSyntaxPolynomial
      omega))
  have hconjunctionSyntax :
      (binaryFormulaCode (appendFormula ⋏ countFormula)).length <=
        syntaxResource := by
    dsimp only [appendFormula, countFormula]
    simp only [binaryFormulaCode, List.length_append]
    unfold syntaxResource
    rw [compactSequentFormulaStepTail20FullyFixedSyntaxPolynomial]
    omega
  have hcost := conjunctionFullAssemblyCost_le_small ∅ appendFormula
    countFormula syntaxResource (by simp) (by
      intro formula hmem
      simp at hmem) happendSyntax hcountSyntax hconjunctionSyntax
  have hcost' : CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
      (compactAdditiveNatListAppendSlicesClosedFormula tokenTable width
        tokenCount row.value.start row.value.finish row.value.count
        row.next.start row.next.finish row.next.count row.current.start
        row.current.finish row.current.count)
      (“!!(shortBinaryNumeralTerm suffixCount) =
        !!(shortBinaryNumeralTerm valueCount) + 1” : ValuationFormula) <=
      smallContextAssemblyEnvelope syntaxResource := by
    simpa only [appendFormula, countFormula] using hcost
  have hassembly := CertifiedPAContextProof.conjunction_payloadLength_le
    append.proof countProof
  refine { proof := proof, payloadLength_le := ?_ }
  have hproof : proof.payloadLength <=
      appendSlicesFullyFixedPayloadPolynomial
          (compactSequentFormulaStepTail16AppendNumericBound width tokenCount
            row.next.count row.current.count)
          (compactSequentFormulaStepTail16AppendBitBound tokenTable width
            tokenCount row.next.count row.current.count) +
        compactSequentFormulaStepTail16CountDirectPayloadPolynomial suffixCount
          valueCount + smallContextAssemblyEnvelope syntaxResource := by
    calc
      proof.payloadLength <= append.proof.payloadLength +
          countProof.payloadLength +
            CertifiedPAContextProof.conjunctionFullAssemblyCost ∅
              appendFormula countFormula := by
        exact hassembly
      _ <= _ := by omega
  unfold compactSequentFormulaStepTail20FullyFixedPayloadPolynomial
  simpa only [syntaxResource, appendFormula, countFormula] using hproof

end FoundationCompactNumericListedDirectSequentFormulaStepTail20FullyFixedBound
