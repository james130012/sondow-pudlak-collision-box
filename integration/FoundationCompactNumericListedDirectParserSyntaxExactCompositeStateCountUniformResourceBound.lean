import integration.FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedPayload
import integration.FoundationCompactNumericListedDirectParserSyntaxExactBoundedUniformResourceDirectCompiler
import integration.FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Composite parser state count with a uniform source resource -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectParserSyntaxExactCompositeStateCountUniformResourceBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserInitialFinalExactFuelCountFixedBound
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedUniformResourceDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxTraceBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransportFixedPayload
open FoundationCompactNumericListedDirectAdditiveCodecGraph

private theorem certifiedPAProof_conclusionCodeLength_le_payloadLength
    {formula : LO.FirstOrder.ArithmeticProposition}
    (proof : CertifiedPAProof formula) :
    (binaryFormulaCode formula).length <= proof.payloadLength := by
  have hformula : formula ∈ ({formula} :
      Finset LO.FirstOrder.ArithmeticProposition) := by simp
  have hsequent :=
    binaryFormulaCode_length_le_binarySequentCode_length_of_mem
      {formula} formula hformula
  have hproof := binarySequentCode_length_le_binaryProofLength proof.derivation
  have hpayload : binaryProofLength proof.derivation <= proof.payloadLength := by
    rw [CertifiedPAProof.payloadLength_eq]
    omega
  exact hsequent.trans (hproof.trans hpayload)

private theorem binaryFormulaCode_antecedent_le_implication
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode antecedent).length <=
      2 * (binaryFormulaCode (antecedent 🡒 consequent)).length := by
  have hdoubleRaw := binaryFormulaCode_neg_length_le (∼antecedent)
  have hneg : (binaryFormulaCode (∼antecedent)).length <=
      (binaryFormulaCode (antecedent 🡒 consequent)).length := by
    change (binaryFormulaCode (∼antecedent)).length <=
      (binaryFormulaCode ((∼antecedent) ⋎ consequent)).length
    simp only [binaryFormulaCode, List.length_append]
    omega
  have hdouble : (binaryFormulaCode antecedent).length <=
      2 * (binaryFormulaCode (∼antecedent)).length := by
    calc
      (binaryFormulaCode antecedent).length =
          (binaryFormulaCode (∼∼antecedent)).length := by
        change (binaryFormulaCode antecedent).length =
          (binaryFormulaCode
            (Semiformula.neg (Semiformula.neg antecedent))).length
        rw [Semiformula.neg_neg]
      _ <= 2 * (binaryFormulaCode (∼antecedent)).length := hdoubleRaw
  exact hdouble.trans (Nat.mul_le_mul_left 2 hneg)

private theorem binaryFormulaCode_consequent_le_implication
    (antecedent consequent : LO.FirstOrder.ArithmeticProposition) :
    (binaryFormulaCode consequent).length <=
      (binaryFormulaCode (antecedent 🡒 consequent)).length := by
  simp [binaryFormulaCode]
  omega

def compactParserSyntaxExactCompositeStateCountUniformFormulaPolynomial
    (numericBound : Nat) : Nat :=
  4 * compactParserSyntaxExactStateCountTransportFixedPayloadPolynomial
    numericBound + 64

def compactParserSyntaxExactCompositeStateCountUniformPayloadPolynomial
    (tokenCount uniformValueBound numericBound bitBound : Nat) : Nat :=
  let transport :=
    compactParserSyntaxExactStateCountTransportFixedPayloadPolynomial
      numericBound
  let count :=
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound
  let source := compactParserSyntaxExactBoundedUniformPayloadPolynomial
    tokenCount uniformValueBound numericBound bitBound
  let formula :=
    compactParserSyntaxExactCompositeStateCountUniformFormulaPolynomial
      numericBound
  transport + count + source + 3 * smallContextAssemblyEnvelope formula

noncomputable def
    compactParserSyntaxExactCompositeStateCountUniformClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth formulaValueBound uniformValueBound
      numericBound bitBound : Nat)
    (htableWidthUniform : tableWidth <= uniformValueBound)
    (hformulaValueUniform : formulaValueBound <= uniformValueBound)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      formulaValueBound)
    (htokenTable : tokenTable <= numericBound)
    (hwidth : width <= numericBound)
    (htokenCount : tokenCount <= numericBound)
    (hstateBoundary : stateBoundary <= numericBound)
    (hstateCount : stateCount <= numericBound)
    (hfuel : compactParserSyntaxExactFuel inputCount <= numericBound)
    (hinputBoundary : inputBoundary <= numericBound)
    (hinputCount : inputCount <= numericBound)
    (hexpectedBoundary : expectedBoundary <= numericBound)
    (hexpectedCount : expectedCount <= numericBound)
    (htaskKind : taskKind <= numericBound)
    (htaskBinderArity : taskBinderArity <= numericBound)
    (htaskRepeatCount : taskRepeatCount <= numericBound)
    (hareaNumeric : (tokenCount + 1) * tokenCount <= numericBound)
    (huniformValueSucc : uniformValueBound + 1 <= numericBound)
    (hnumericBit : numericBound <= bitBound)
    (hnumericSize : Nat.size numericBound <= bitBound)
    (hbitPositive : 1 <= bitBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable
        width tokenCount stateBoundary inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth formulaValueBound)
      (compactParserSyntaxExactCompositeStateCountUniformPayloadPolynomial
        tokenCount uniformValueBound numericBound bitBound) := by
  have htrace : CompactParserSyntaxTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
      (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth formulaValueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactParserSyntaxExactFuel] using hgraph
  have htableWidth : tableWidth <= numericBound := by omega
  have hformulaValue : formulaValueBound <= numericBound := by omega
  let countBound :=
    parserInitialFinalExactFuelCountClosedDirectBound stateCount inputCount
      htrace.1
  let sourceBound :=
    compactParserSyntaxExactBoundedUniformClosedDirectBoundOfGraph
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth formulaValueBound uniformValueBound
      numericBound bitBound htableWidthUniform hformulaValueUniform hgraph
      htokenTable hwidth htokenCount hstateBoundary hstateCount hfuel
      hinputBoundary hinputCount hexpectedBoundary hexpectedCount htaskKind
      htaskBinderArity htaskRepeatCount hareaNumeric huniformValueSucc
      hnumericBit hnumericSize hbitPositive
  let transportClosed :=
    compactParserSyntaxExactStateCountTransportPublicProof tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth formulaValueBound
  let transportContext :=
    CertifiedPAContextProof.weakenCertified ∅ transportClosed
  let afterCount :=
    CertifiedPAContextProof.modusPonens transportContext countBound.proof
  let proof := CertifiedPAContextProof.modusPonens afterCount sourceBound.proof
  let countFormula :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let sourceFormula :=
    compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth formulaValueBound
  let targetFormula :=
    compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      formulaValueBound
  let sourceImplication := sourceFormula 🡒 targetFormula
  let transportFormula := countFormula 🡒 sourceImplication
  let transportResource :=
    compactParserSyntaxExactStateCountTransportFixedPayloadPolynomial
      numericBound
  let countResource :=
    compactParserInitialFinalExactFuelCountFixedPayloadPolynomial numericBound
  let sourceResource := compactParserSyntaxExactBoundedUniformPayloadPolynomial
    tokenCount uniformValueBound numericBound bitBound
  let formulaResource :=
    compactParserSyntaxExactCompositeStateCountUniformFormulaPolynomial
      numericBound
  have htransport : transportClosed.payloadLength <= transportResource :=
    compactParserSyntaxExactStateCountTransportPublicProof_payload_le_fixed
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth formulaValueBound numericBound htokenTable
      hwidth htokenCount hstateBoundary hstateCount hinputBoundary hinputCount
      hexpectedBoundary hexpectedCount htaskKind htaskBinderArity
      htaskRepeatCount htableWidth hformulaValue
  have hcount : countBound.proof.payloadLength <= countResource :=
    countBound.payloadLength_le.trans
      (compactParserInitialFinalExactFuelCountResource_le_fixed inputCount
        numericBound hinputCount)
  have hsource : sourceBound.proof.payloadLength <= sourceResource :=
    sourceBound.payloadLength_le
  have htransportFormula :
      (binaryFormulaCode transportFormula).length <= transportResource := by
    have hraw :=
      certifiedPAProof_conclusionCodeLength_le_payloadLength transportClosed
    simpa only [transportFormula, sourceImplication, countFormula,
      sourceFormula, targetFormula,
      compactParserSyntaxExactStateCountTransportPublicFormula] using
        hraw.trans htransport
  have hcountFormula :
      (binaryFormulaCode countFormula).length <= 2 * transportResource :=
    (binaryFormulaCode_antecedent_le_implication countFormula
      sourceImplication).trans (Nat.mul_le_mul_left 2 htransportFormula)
  have hsourceImplication :
      (binaryFormulaCode sourceImplication).length <= transportResource :=
    (binaryFormulaCode_consequent_le_implication countFormula
      sourceImplication).trans htransportFormula
  have hsourceFormula :
      (binaryFormulaCode sourceFormula).length <= 2 * transportResource :=
    (binaryFormulaCode_antecedent_le_implication sourceFormula
      targetFormula).trans (Nat.mul_le_mul_left 2 hsourceImplication)
  have htargetFormula :
      (binaryFormulaCode targetFormula).length <= transportResource :=
    (binaryFormulaCode_consequent_le_implication sourceFormula
      targetFormula).trans hsourceImplication
  have htoFormulaResource {formula : ValuationFormula}
      (hformula :
        (binaryFormulaCode formula).length <= 2 * transportResource) :
      (binaryFormulaCode formula).length <= formulaResource := by
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactCompositeStateCountUniformFormulaPolynomial
    omega
  have hnegToFormulaResource {formula : ValuationFormula}
      (hformula :
        (binaryFormulaCode formula).length <= 2 * transportResource) :
      (binaryFormulaCode (∼formula)).length <= formulaResource := by
    have hneg := binaryFormulaCode_neg_length_le formula
    dsimp only [formulaResource]
    unfold compactParserSyntaxExactCompositeStateCountUniformFormulaPolynomial
    omega
  have hformulaContext : FormulaCodeBound ∅ formulaResource := by
    intro formula hmem
    simp at hmem
  have hweakeningCost := weakeningFullAssemblyCost_le_small
    (insert transportFormula ∅) formulaResource (by simp) (by
      intro formula hmem
      simp at hmem
      subst formula
      exact htoFormulaResource (htransportFormula.trans (by omega)))
  have hfirstCost := contextualModusPonensFullAssemblyCost_le_small ∅
    countFormula sourceImplication formulaResource (by simp) hformulaContext
    (htoFormulaResource hcountFormula)
    (htoFormulaResource (hsourceImplication.trans (by omega)))
    (htoFormulaResource (htransportFormula.trans (by omega)))
    (hnegToFormulaResource (htransportFormula.trans (by omega)))
    (hnegToFormulaResource (hsourceImplication.trans (by omega)))
  have hsecondCost := contextualModusPonensFullAssemblyCost_le_small ∅
    sourceFormula targetFormula formulaResource (by simp) hformulaContext
    (htoFormulaResource hsourceFormula)
    (htoFormulaResource (htargetFormula.trans (by omega)))
    (htoFormulaResource (hsourceImplication.trans (by omega)))
    (hnegToFormulaResource (hsourceImplication.trans (by omega)))
    (hnegToFormulaResource (htargetFormula.trans (by omega)))
  have hweaken :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅ transportClosed
  have hfirst := CertifiedPAContextProof.modusPonens_payloadLength_le
    transportContext countBound.proof
  have hsecond := CertifiedPAContextProof.modusPonens_payloadLength_le
    afterCount sourceBound.proof
  refine { proof := proof, payloadLength_le := ?_ }
  have htransportContext : transportContext.payloadLength <=
      transportResource + smallContextAssemblyEnvelope formulaResource := by
    calc
      transportContext.payloadLength <= transportClosed.payloadLength +
          weakeningFullAssemblyCost (insert transportFormula ∅) := by
        simpa only [transportContext, transportFormula, sourceImplication,
          countFormula, sourceFormula, targetFormula,
          compactParserSyntaxExactStateCountTransportPublicFormula] using
            hweaken
      _ <= transportResource + smallContextAssemblyEnvelope formulaResource :=
        Nat.add_le_add htransport hweakeningCost
  have hafter : afterCount.payloadLength <= transportResource +
      smallContextAssemblyEnvelope formulaResource + countResource +
      smallContextAssemblyEnvelope formulaResource := by
    calc
      afterCount.payloadLength <= transportContext.payloadLength +
          countBound.proof.payloadLength +
            contextualModusPonensFullAssemblyCost ∅ countFormula
              sourceImplication := hfirst
      _ <= transportResource + smallContextAssemblyEnvelope formulaResource +
          countResource + smallContextAssemblyEnvelope formulaResource := by
        omega
  have hproof : proof.payloadLength <= transportResource + countResource +
      sourceResource + 3 * smallContextAssemblyEnvelope formulaResource := by
    calc
      proof.payloadLength <= afterCount.payloadLength +
          sourceBound.proof.payloadLength +
            contextualModusPonensFullAssemblyCost ∅ sourceFormula
              targetFormula := hsecond
      _ <= transportResource + countResource + sourceResource +
          3 * smallContextAssemblyEnvelope formulaResource := by
        omega
  change proof.payloadLength <=
    compactParserSyntaxExactCompositeStateCountUniformPayloadPolynomial
      tokenCount uniformValueBound numericBound bitBound
  unfold compactParserSyntaxExactCompositeStateCountUniformPayloadPolynomial
  dsimp only [transportResource, countResource, sourceResource,
    formulaResource]
  exact hproof

#print axioms
  compactParserSyntaxExactCompositeStateCountUniformClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxExactCompositeStateCountUniformResourceBound
