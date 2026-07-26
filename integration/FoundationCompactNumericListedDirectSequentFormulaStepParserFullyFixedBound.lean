import integration.FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedPayload
import integration.FoundationCompactNumericListedDirectParserSyntaxExactCompositeStateCountFullyFixedBound
import integration.FoundationCompactCertifiedContextProofConclusionCodeBounds
import integration.FoundationCompactPAContextCostPolynomialBounds

/-! # Fully fixed sequent-formula-step parser bound -/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000

namespace FoundationCompactNumericListedDirectSequentFormulaStepParserFullyFixedBound

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextProofConclusionCodeBounds
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactPAContextCostPolynomialBounds
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPABinaryNumeralAdditionBounds
open FoundationCompactPAValuationTermCompiler
open FoundationCompactSyntaxTransformationCodeBounds
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
open FoundationCompactNumericListedDirectParserSyntaxExactCompositeStateCountFullyFixedBound
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
open FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransportFixedPayload

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

def compactSequentFormulaStepParserFullyFixedFormulaPolynomial
    (numericBound : Nat) : Nat :=
  4 * compactParserSyntaxExactTaskOneTransportFixedPayloadPolynomial
    numericBound + 64

def compactSequentFormulaStepParserFullyFixedPayloadPolynomial
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount tableWidth valueBound : Nat) :
    Nat :=
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount 1 0 0 tableWidth valueBound
  let transport :=
    compactParserSyntaxExactTaskOneTransportFixedPayloadPolynomial numericBound
  let equality :=
    compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength
  let source :=
    compactParserSyntaxExactCompositeStateCountFullyFixedPayloadPolynomial
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount 1 0 0 tableWidth valueBound
  let formula :=
    compactSequentFormulaStepParserFullyFixedFormulaPolynomial numericBound
  transport + equality + source + 4 * smallContextAssemblyEnvelope formula

noncomputable def
    compactSequentFormulaStepParserFullyFixedClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount tableWidth valueBound : Nat)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount 1 0 0 tableWidth valueBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
        stateBoundary inputBoundary inputCount expectedBoundary expectedCount
        tableWidth valueBound)
      (compactSequentFormulaStepParserFullyFixedPayloadPolynomial tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount tableWidth valueBound) := by
  let numericBound :=
    compactParserSyntaxExactBoundedDirectNumericBound tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount 1 0 0 tableWidth valueBound
  have htokenTable : tokenTable <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hwidth : width <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htokenCount : tokenCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hstateBoundary : stateBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hinputBoundary : inputBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hinputCount : inputCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hexpectedBoundary : expectedBoundary <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hexpectedCount : expectedCount <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have htableWidth : tableWidth <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hvalueBound : valueBound <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  have hnumericPositive : 1 <= numericBound := by
    unfold numericBound compactParserSyntaxExactBoundedDirectNumericBound
    omega
  let equalityFormula : ValuationFormula :=
    “!!(shortBinaryNumeralTerm 1) =
      !!compactParserSyntaxExactNativeOneTerm”
  let sourceFormula :=
    compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount 1 0 0 tableWidth valueBound
  let targetFormula :=
    compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
      stateBoundary inputBoundary inputCount expectedBoundary expectedCount
      tableWidth valueBound
  let sourceImplication := sourceFormula 🡒 targetFormula
  let transportFormula := equalityFormula 🡒 sourceImplication
  let transportClosed :=
    compactParserSyntaxExactTaskOneTransportPublicProof tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound
  let transportContext :=
    CertifiedPAContextProof.weakenCertified ∅ transportClosed
  let equalityClosed := compactParserSyntaxExactShortOneEqualsNativeOneProof
  let equalityContext :=
    CertifiedPAContextProof.weakenCertified ∅ equalityClosed
  let afterEquality :=
    CertifiedPAContextProof.modusPonens transportContext equalityContext
  let sourceBound :=
    compactParserSyntaxExactCompositeStateCountFullyFixedClosedDirectBoundOfGraph
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount 1 0 0 tableWidth valueBound
      hgraph
  let proof :=
    CertifiedPAContextProof.modusPonens afterEquality sourceBound.proof
  let transportResource :=
    compactParserSyntaxExactTaskOneTransportFixedPayloadPolynomial numericBound
  let equalityResource := equalityClosed.payloadLength
  let sourceResource :=
    compactParserSyntaxExactCompositeStateCountFullyFixedPayloadPolynomial
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount 1 0 0 tableWidth valueBound
  let formulaResource :=
    compactSequentFormulaStepParserFullyFixedFormulaPolynomial numericBound
  have htransport : transportClosed.payloadLength <= transportResource := by
    exact
      compactParserSyntaxExactTaskOneTransportPublicProof_payload_le_fixed
        tokenTable width tokenCount stateBoundary inputBoundary inputCount
        expectedBoundary expectedCount tableWidth valueBound numericBound
        htokenTable hwidth htokenCount hstateBoundary hinputBoundary hinputCount
        hexpectedBoundary hexpectedCount htableWidth hvalueBound
        hnumericPositive
  have hequality : equalityClosed.payloadLength <= equalityResource := by
    exact Nat.le_refl _
  have hsource : sourceBound.proof.payloadLength <= sourceResource :=
    sourceBound.payloadLength_le
  have htransportFormula :
      (binaryFormulaCode transportFormula).length <= transportResource := by
    have hraw :=
      certifiedPAProof_conclusionCodeLength_le_payloadLength transportClosed
    simpa only [transportFormula, sourceImplication, equalityFormula,
      sourceFormula, targetFormula,
      compactParserSyntaxExactTaskOneTransportPublicFormula] using
        hraw.trans htransport
  have hequalityFormula :
      (binaryFormulaCode equalityFormula).length <= 2 * transportResource :=
    (binaryFormulaCode_antecedent_le_implication equalityFormula
      sourceImplication).trans (Nat.mul_le_mul_left 2 htransportFormula)
  have hsourceImplication :
      (binaryFormulaCode sourceImplication).length <= transportResource :=
    (binaryFormulaCode_consequent_le_implication equalityFormula
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
    unfold compactSequentFormulaStepParserFullyFixedFormulaPolynomial
    omega
  have hnegToFormulaResource {formula : ValuationFormula}
      (hformula :
        (binaryFormulaCode formula).length <= 2 * transportResource) :
      (binaryFormulaCode (∼formula)).length <= formulaResource := by
    have hneg := binaryFormulaCode_neg_length_le formula
    dsimp only [formulaResource]
    unfold compactSequentFormulaStepParserFullyFixedFormulaPolynomial
    omega
  have hformulaContext : FormulaCodeBound ∅ formulaResource := by
    intro formula hmem
    simp at hmem
  have htransportWeakening := weakeningFullAssemblyCost_le_small
    (insert transportFormula ∅) formulaResource (by simp) (by
      intro formula hmem
      simp at hmem
      subst formula
      exact htoFormulaResource (htransportFormula.trans (by omega)))
  have hequalityWeakening := weakeningFullAssemblyCost_le_small
    (insert equalityFormula ∅) formulaResource (by simp) (by
      intro formula hmem
      simp at hmem
      subst formula
      exact htoFormulaResource hequalityFormula)
  have hfirstCost := contextualModusPonensFullAssemblyCost_le_small ∅
    equalityFormula sourceImplication formulaResource (by simp)
    hformulaContext (htoFormulaResource hequalityFormula)
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
  have htransportWeaken :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅
      transportClosed
  have hequalityWeaken :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅
      equalityClosed
  have hfirst := CertifiedPAContextProof.modusPonens_payloadLength_le
    transportContext equalityContext
  have hsecond := CertifiedPAContextProof.modusPonens_payloadLength_le
    afterEquality sourceBound.proof
  refine { proof := proof, payloadLength_le := ?_ }
  have htransportContext : transportContext.payloadLength <=
      transportResource + smallContextAssemblyEnvelope formulaResource := by
    calc
      transportContext.payloadLength <= transportClosed.payloadLength +
          weakeningFullAssemblyCost (insert transportFormula ∅) := by
        simpa only [transportContext, transportFormula, sourceImplication,
          equalityFormula, sourceFormula, targetFormula,
          compactParserSyntaxExactTaskOneTransportPublicFormula] using
            htransportWeaken
      _ <= transportResource + smallContextAssemblyEnvelope formulaResource :=
        Nat.add_le_add htransport htransportWeakening
  have hequalityContext : equalityContext.payloadLength <=
      equalityResource + smallContextAssemblyEnvelope formulaResource := by
    calc
      equalityContext.payloadLength <= equalityClosed.payloadLength +
          weakeningFullAssemblyCost (insert equalityFormula ∅) := by
        simpa only [equalityContext, equalityFormula] using hequalityWeaken
      _ <= equalityResource + smallContextAssemblyEnvelope formulaResource :=
        Nat.add_le_add hequality hequalityWeakening
  have hafter : afterEquality.payloadLength <=
      transportResource + smallContextAssemblyEnvelope formulaResource +
      equalityResource + 2 * smallContextAssemblyEnvelope formulaResource := by
    calc
      afterEquality.payloadLength <= transportContext.payloadLength +
          equalityContext.payloadLength +
            contextualModusPonensFullAssemblyCost ∅ equalityFormula
              sourceImplication := by
        exact hfirst
      _ <= transportResource + smallContextAssemblyEnvelope formulaResource +
          equalityResource + 2 * smallContextAssemblyEnvelope formulaResource := by
        omega
  have hproof : proof.payloadLength <=
      transportResource + equalityResource + sourceResource +
        4 * smallContextAssemblyEnvelope formulaResource := by
    calc
      proof.payloadLength <= afterEquality.payloadLength +
          sourceBound.proof.payloadLength +
            contextualModusPonensFullAssemblyCost ∅ sourceFormula
              targetFormula := by
        exact hsecond
      _ <= transportResource + equalityResource + sourceResource +
          4 * smallContextAssemblyEnvelope formulaResource := by
        omega
  change proof.payloadLength <=
    compactSequentFormulaStepParserFullyFixedPayloadPolynomial tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound
  unfold compactSequentFormulaStepParserFullyFixedPayloadPolynomial
  dsimp only [numericBound, transportResource, equalityResource,
    sourceResource, formulaResource, equalityClosed]
  exact hproof

#print axioms
  compactSequentFormulaStepParserFullyFixedClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepParserFullyFixedBound
