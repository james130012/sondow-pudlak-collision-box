import integration.FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax

/-!
# Fixed PA transport for the sequent-step parser task constant

The direct parser compiler uses a short-binary term for task kind `1`, whereas
the original sequent-step formula contains PA's native constant `1`.  This
module proves one fixed substitution theorem in PA and specializes it at the
public parser coordinates.  The two task-zero coordinates are already
syntactically identical after unfolding.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport

open FoundationSuccinctFiniteConsistencyTarget
open FoundationCompactPAQuantitativeCompilerCore
open FoundationCompactPAQuantitativeCompilerCore.CertifiedPAProof
open FoundationCompactCertifiedDerivationSpecialization
open FoundationCompactPABinaryNumeralAddition
open FoundationCompactPAValuationTermCompiler
open FoundationCompactCertifiedContextProof
open FoundationCompactCertifiedContextProof.CertifiedPAContextProof
open FoundationCompactCertifiedContextualModusPonens
open FoundationCompactNumericListedDirectParserSyntaxExactFuelEquality
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
open FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
open FoundationCompactNumericListedDirectSequentFormulaStepDirectSyntax

def compactParserSyntaxExactTaskOneTransportSourceTerms :
    Fin 14 -> ArithmeticSemiterm Empty 15 :=
  ![(#0 : ArithmeticSemiterm Empty 15), #1, #2, #3, #4, #5, #6,
    #7, #8, #9, #11, #12, #13, #14]

def compactParserSyntaxExactTaskOneTransportTargetTerms :
    Fin 14 -> ArithmeticSemiterm Empty 15 :=
  ![(#0 : ArithmeticSemiterm Empty 15), #1, #2, #3, #4, #5, #6,
    #7, #8, #10, #11, #12, #13, #14]

def compactParserSyntaxExactTaskOneTransportSource :
    ArithmeticSemisentence 15 :=
  Rew.subst compactParserSyntaxExactTaskOneTransportSourceTerms ▹
    compactParserSyntaxExactBoundedGraphDef.val

def compactParserSyntaxExactTaskOneTransportTarget :
    ArithmeticSemisentence 15 :=
  Rew.subst compactParserSyntaxExactTaskOneTransportTargetTerms ▹
    compactParserSyntaxExactBoundedGraphDef.val

def compactParserSyntaxExactTaskOneTransportBody :
    ArithmeticSemisentence 15 :=
  (“#9 = #10” : ArithmeticSemisentence 15) 🡒
    compactParserSyntaxExactTaskOneTransportSource 🡒
      compactParserSyntaxExactTaskOneTransportTarget

def compactParserSyntaxExactTaskOneTransportSentence :
    ArithmeticSentence :=
  ∀⁰* compactParserSyntaxExactTaskOneTransportBody

theorem compactParserSyntaxExactTaskOneTransportBody_valid
    {M : Type*} [ORingStructure M]
    (environment : Fin 15 -> M) :
    Semiformula.Eval environment Empty.elim
      compactParserSyntaxExactTaskOneTransportBody := by
  simp only [compactParserSyntaxExactTaskOneTransportBody,
    LO.LogicalConnective.HomClass.map_imply]
  intro htask hsource
  have htask' : environment 9 = environment 10 := by
    simpa using htask
  have hterms :
      (Semiterm.val environment Empty.elim ∘
          compactParserSyntaxExactTaskOneTransportSourceTerms) =
        (Semiterm.val environment Empty.elim ∘
          compactParserSyntaxExactTaskOneTransportTargetTerms) := by
    funext coordinate
    fin_cases coordinate <;>
      simp [compactParserSyntaxExactTaskOneTransportSourceTerms,
        compactParserSyntaxExactTaskOneTransportTargetTerms, htask']
  unfold compactParserSyntaxExactTaskOneTransportSource at hsource
  unfold compactParserSyntaxExactTaskOneTransportTarget
  simp only [Semiformula.eval_rew] at hsource ⊢
  have hbound :
      (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactTaskOneTransportSourceTerms) ∘
          Semiterm.bvar) =
        (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactTaskOneTransportTargetTerms) ∘
          Semiterm.bvar) := by
    funext coordinate
    simpa [Function.comp_def, Rew.subst_bvar] using
      congrFun hterms coordinate
  have hfree :
      (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactTaskOneTransportSourceTerms) ∘
          Semiterm.fvar) =
        (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactTaskOneTransportTargetTerms) ∘
          Semiterm.fvar) := by
    funext coordinate
    exact Empty.elim coordinate
  rw [hbound, hfree] at hsource
  exact hsource

theorem compactParserSyntaxExactTaskOneTransportSentence_valid
    {M : Type*} [ORingStructure M] :
    M↓[ℒₒᵣ] ⊧ compactParserSyntaxExactTaskOneTransportSentence := by
  rw [models_iff]
  simp only [compactParserSyntaxExactTaskOneTransportSentence,
    Semiformula.eval_allClosure]
  exact fun environment =>
    compactParserSyntaxExactTaskOneTransportBody_valid environment

noncomputable def compactParserSyntaxExactTaskOneTransportProvable :
    PA ⊢ compactParserSyntaxExactTaskOneTransportSentence :=
  LO.FirstOrder.Arithmetic.complete.{0} PA
    compactParserSyntaxExactTaskOneTransportSentence
    (fun (_ : Type) _ _ =>
      compactParserSyntaxExactTaskOneTransportSentence_valid)

noncomputable def compactParserSyntaxExactTaskOneTransportDerivation :
    LO.FirstOrder.Derivation2 PA
      {(compactParserSyntaxExactTaskOneTransportSentence :
        ArithmeticProposition)} :=
  compactParserSyntaxExactTaskOneTransportProvable.get.toProof2

noncomputable def compactParserSyntaxExactTaskOneTransportProof :
    CertifiedPAProof
      (compactParserSyntaxExactTaskOneTransportSentence :
        ArithmeticProposition) where
  derivation := compactParserSyntaxExactTaskOneTransportDerivation
  certificate :=
    certificateOfDerivation compactParserSyntaxExactTaskOneTransportDerivation
  certificate_valid :=
    certificateOfDerivation_valid
      compactParserSyntaxExactTaskOneTransportDerivation

def compactParserSyntaxExactTaskOneTransportBodyNat :
    ArithmeticSemiformula Nat 15 :=
  Rewriting.emb compactParserSyntaxExactTaskOneTransportBody

theorem compactParserSyntaxExactTaskOneTransportClosure_alignment :
    (∀⁰* compactParserSyntaxExactTaskOneTransportBodyNat) =
      (compactParserSyntaxExactTaskOneTransportSentence :
        ArithmeticProposition) := by
  simp [compactParserSyntaxExactTaskOneTransportBodyNat,
    compactParserSyntaxExactTaskOneTransportSentence]

def compactParserSyntaxExactNativeOneTerm : ValuationTerm :=
  ‘1’

def compactParserSyntaxExactTaskOneTransportPublicTerms
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    Fin 15 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    (‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’ : ValuationTerm),
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm 1,
    compactParserSyntaxExactNativeOneTerm,
    shortBinaryNumeralTerm 0,
    shortBinaryNumeralTerm 0,
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm valueBound]

def compactParserSyntaxExactTaskOneTransportPublicFormula
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  “!!(shortBinaryNumeralTerm 1) =
      !!compactParserSyntaxExactNativeOneTerm” 🡒
    compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable width
        tokenCount stateBoundary inputBoundary inputCount expectedBoundary
        expectedCount 1 0 0 tableWidth valueBound 🡒
      compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
        stateBoundary inputBoundary inputCount expectedBoundary expectedCount
        tableWidth valueBound

theorem compactParserSyntaxExactTaskOneTransportPublicFormula_alignment
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    Rew.subst
        (compactParserSyntaxExactTaskOneTransportPublicTerms tokenTable width
          tokenCount stateBoundary inputBoundary inputCount expectedBoundary
          expectedCount tableWidth valueBound) ▹
      compactParserSyntaxExactTaskOneTransportBodyNat =
    compactParserSyntaxExactTaskOneTransportPublicFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound := by
  simp [compactParserSyntaxExactTaskOneTransportBodyNat,
    compactParserSyntaxExactTaskOneTransportBody,
    compactParserSyntaxExactTaskOneTransportSource,
    compactParserSyntaxExactTaskOneTransportTarget,
    compactParserSyntaxExactTaskOneTransportPublicFormula,
    compactParserSyntaxExactTaskOneTransportSourceTerms,
    compactParserSyntaxExactTaskOneTransportTargetTerms,
    compactParserSyntaxExactTaskOneTransportPublicTerms,
    compactParserSyntaxExactCompositeStateCountClosedFormula,
    compactParserSyntaxExactCompositeStateCountPublicTerms,
    compactSequentFormulaStepParserClosedFormula,
    compactSequentFormulaStepParserPublicTerms,
    compactParserSyntaxExactNativeOneTerm,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [compactParserSyntaxExactTaskOneTransportSourceTerms,
          compactParserSyntaxExactTaskOneTransportPublicTerms,
          compactParserSyntaxExactCompositeStateCountPublicTerms,
          Rew.comp_app]
    · intro coordinate
      exact Empty.elim coordinate
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [compactParserSyntaxExactTaskOneTransportTargetTerms,
          compactParserSyntaxExactTaskOneTransportPublicTerms,
          compactSequentFormulaStepParserPublicTerms,
          compactParserSyntaxExactNativeOneTerm,
          shortBinaryNumeralTerm,
          FoundationCompactBinaryNumeralTerm.binaryNumeralTerm_zero,
          FoundationCompactBinaryNumeralTerm.arithmeticZeroTerm,
          Semiterm.Operator.operator, Semiterm.Operator.numeral_zero,
          Semiterm.Operator.Zero.term_eq, Rew.func, Matrix.empty_eq,
          Rew.comp_app]
    · intro coordinate
      exact Empty.elim coordinate

def compactParserSyntaxExactTaskOneTransportPublicPayloadEnvelope
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    Nat :=
  compactParserSyntaxExactTaskOneTransportProof.payloadLength +
    allClosureSpecializationCost
      compactParserSyntaxExactTaskOneTransportBodyNat
      (compactParserSyntaxExactTaskOneTransportPublicTerms tokenTable width
        tokenCount stateBoundary inputBoundary inputCount expectedBoundary
        expectedCount tableWidth valueBound)

noncomputable def compactParserSyntaxExactTaskOneTransportPublicProof
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    CertifiedPAProof
      (compactParserSyntaxExactTaskOneTransportPublicFormula tokenTable width
        tokenCount stateBoundary inputBoundary inputCount expectedBoundary
        expectedCount tableWidth valueBound) := by
  let baseProof : CertifiedPAProof
      (∀⁰* compactParserSyntaxExactTaskOneTransportBodyNat) :=
    CertifiedPAProof.cast
      compactParserSyntaxExactTaskOneTransportClosure_alignment.symm
      compactParserSyntaxExactTaskOneTransportProof
  let specializedProof := specializeAllClosure
    compactParserSyntaxExactTaskOneTransportBodyNat baseProof
    (compactParserSyntaxExactTaskOneTransportPublicTerms tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound)
  exact CertifiedPAProof.cast
    (compactParserSyntaxExactTaskOneTransportPublicFormula_alignment tokenTable
      width tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound)
    specializedProof

theorem
    compactParserSyntaxExactTaskOneTransportPublicProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound : Nat) :
    (compactParserSyntaxExactTaskOneTransportPublicProof tokenTable width
        tokenCount stateBoundary inputBoundary inputCount expectedBoundary
        expectedCount tableWidth valueBound).payloadLength <=
      compactParserSyntaxExactTaskOneTransportPublicPayloadEnvelope tokenTable
        width tokenCount stateBoundary inputBoundary inputCount expectedBoundary
        expectedCount tableWidth valueBound := by
  let publicTerms :=
    compactParserSyntaxExactTaskOneTransportPublicTerms tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound
  let baseProof : CertifiedPAProof
      (∀⁰* compactParserSyntaxExactTaskOneTransportBodyNat) :=
    CertifiedPAProof.cast
      compactParserSyntaxExactTaskOneTransportClosure_alignment.symm
      compactParserSyntaxExactTaskOneTransportProof
  have hspecialized :=
    specializeAllClosure_payloadLength_le
      compactParserSyntaxExactTaskOneTransportBodyNat baseProof publicTerms
  change
    (CertifiedPAProof.cast _
      (specializeAllClosure compactParserSyntaxExactTaskOneTransportBodyNat
        baseProof publicTerms)).payloadLength <= _
  rw [CertifiedPAProof.cast_payloadLength]
  have hbase :
      baseProof.payloadLength =
        compactParserSyntaxExactTaskOneTransportProof.payloadLength := by
    dsimp only [baseProof]
    rw [CertifiedPAProof.cast_payloadLength]
  rw [hbase] at hspecialized
  exact hspecialized

noncomputable def compactParserSyntaxExactShortOneEqualsNativeOneProof :
    CertifiedPAProof
      (“!!(shortBinaryNumeralTerm 1) =
        !!compactParserSyntaxExactNativeOneTerm” :
        ArithmeticProposition) := by
  have hformula :
      (“!!binaryOneAlgebraTerm = !!paOneTerm” :
          ArithmeticProposition) =
        (“!!(shortBinaryNumeralTerm 1) =
          !!compactParserSyntaxExactNativeOneTerm” :
          ArithmeticProposition) := by
    rw [binaryNumeralTerm_one_formula]
    simp [compactParserSyntaxExactNativeOneTerm, paOneTerm,
      FoundationCompactBinaryNumeralTerm.arithmeticOneTerm,
      Semiterm.Operator.operator, Semiterm.Operator.numeral_one,
      Semiterm.Operator.One.term_eq, Rew.func, Matrix.empty_eq]
  exact CertifiedPAProof.cast hformula proveBinaryOneAlgebraEqualsOne

def compactSequentFormulaStepParserClosedDirectPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount tableWidth valueBound : Nat) :
    Nat :=
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
  let transportFormula :=
    compactParserSyntaxExactTaskOneTransportPublicFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound
  compactParserSyntaxExactTaskOneTransportPublicPayloadEnvelope tokenTable
      width tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound +
    weakeningFullAssemblyCost (insert transportFormula ∅) +
    compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength +
    weakeningFullAssemblyCost (insert equalityFormula ∅) +
    contextualModusPonensFullAssemblyCost ∅ equalityFormula
      (sourceFormula 🡒 targetFormula) +
    compactParserSyntaxExactCompositeStateCountDirectPayloadEnvelope tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount 1 0 0 tableWidth valueBound +
    contextualModusPonensFullAssemblyCost ∅ sourceFormula targetFormula

noncomputable def compactSequentFormulaStepParserClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount tableWidth valueBound : Nat)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount 1 0 0 tableWidth valueBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactSequentFormulaStepParserClosedFormula tokenTable width tokenCount
        stateBoundary inputBoundary inputCount expectedBoundary expectedCount
        tableWidth valueBound)
      (compactSequentFormulaStepParserClosedDirectPayloadEnvelope tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount tableWidth valueBound) := by
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
  let transportFormula :=
    compactParserSyntaxExactTaskOneTransportPublicFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound
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
    compactParserSyntaxExactCompositeStateCountClosedDirectBoundOfGraph
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount 1 0 0 tableWidth valueBound
      hgraph
  let proof :=
    CertifiedPAContextProof.modusPonens afterEquality sourceBound.proof
  let transportEnvelope :=
    compactParserSyntaxExactTaskOneTransportPublicPayloadEnvelope tokenTable
      width tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount tableWidth valueBound
  let transportWeakeningCost :=
    weakeningFullAssemblyCost (insert transportFormula ∅)
  let equalityWeakeningCost :=
    weakeningFullAssemblyCost (insert equalityFormula ∅)
  let firstCost :=
    contextualModusPonensFullAssemblyCost ∅ equalityFormula
      (sourceFormula 🡒 targetFormula)
  let sourceEnvelope :=
    compactParserSyntaxExactCompositeStateCountDirectPayloadEnvelope tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount 1 0 0 tableWidth valueBound
  let secondCost :=
    contextualModusPonensFullAssemblyCost ∅ sourceFormula targetFormula
  refine { proof := proof, payloadLength_le := ?_ }
  have htransport :=
    compactParserSyntaxExactTaskOneTransportPublicProof_payloadLength_le
      tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount tableWidth valueBound
  have htransportWeakening :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅ transportClosed
  have hequalityWeakening :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅ equalityClosed
  have hfirst :=
    CertifiedPAContextProof.modusPonens_payloadLength_le transportContext
      equalityContext
  have hsource := sourceBound.payloadLength_le
  have hsecond :=
    CertifiedPAContextProof.modusPonens_payloadLength_le afterEquality
      sourceBound.proof
  have htransport' :
      transportClosed.payloadLength <= transportEnvelope := by
    simpa [transportClosed, transportEnvelope] using htransport
  have htransportContext :
      transportContext.payloadLength <=
        transportEnvelope + transportWeakeningCost := by
    calc
      transportContext.payloadLength <=
          transportClosed.payloadLength + transportWeakeningCost := by
        simpa [transportContext, transportWeakeningCost, transportFormula] using
          htransportWeakening
      _ <= transportEnvelope + transportWeakeningCost :=
        Nat.add_le_add_right htransport' transportWeakeningCost
  have hequalityContext :
      equalityContext.payloadLength <=
        equalityClosed.payloadLength + equalityWeakeningCost := by
    simpa [equalityContext, equalityWeakeningCost, equalityFormula] using
      hequalityWeakening
  have hafter :
      afterEquality.payloadLength <=
        transportEnvelope + transportWeakeningCost +
          equalityClosed.payloadLength + equalityWeakeningCost + firstCost := by
    calc
      afterEquality.payloadLength <=
          transportContext.payloadLength + equalityContext.payloadLength +
            firstCost := by
        exact hfirst
      _ <= (transportEnvelope + transportWeakeningCost) +
          (equalityClosed.payloadLength + equalityWeakeningCost) +
            firstCost := by
        omega
      _ = transportEnvelope + transportWeakeningCost +
          equalityClosed.payloadLength + equalityWeakeningCost + firstCost := by
        omega
  have hsource' :
      sourceBound.proof.payloadLength <= sourceEnvelope := by
    simpa [sourceEnvelope] using hsource
  have hproof :
      proof.payloadLength <=
        transportEnvelope + transportWeakeningCost +
          equalityClosed.payloadLength + equalityWeakeningCost + firstCost +
          sourceEnvelope + secondCost := by
    calc
      proof.payloadLength <=
          afterEquality.payloadLength + sourceBound.proof.payloadLength +
            secondCost := by
        exact hsecond
      _ <= (transportEnvelope + transportWeakeningCost +
            equalityClosed.payloadLength + equalityWeakeningCost + firstCost) +
          sourceEnvelope + secondCost := by
        omega
      _ = transportEnvelope + transportWeakeningCost +
          equalityClosed.payloadLength + equalityWeakeningCost + firstCost +
          sourceEnvelope + secondCost := by
        omega
  change proof.payloadLength <=
    transportEnvelope + transportWeakeningCost +
      compactParserSyntaxExactShortOneEqualsNativeOneProof.payloadLength +
      equalityWeakeningCost + firstCost + sourceEnvelope + secondCost
  simpa [equalityClosed] using hproof

#print axioms compactParserSyntaxExactTaskOneTransportBody_valid
#print axioms compactParserSyntaxExactTaskOneTransportSentence_valid
#print axioms compactParserSyntaxExactTaskOneTransportProof
#print axioms compactParserSyntaxExactTaskOneTransportPublicFormula_alignment
#print axioms compactParserSyntaxExactTaskOneTransportPublicProof
#print axioms
  compactParserSyntaxExactTaskOneTransportPublicProof_payloadLength_le
#print axioms compactParserSyntaxExactShortOneEqualsNativeOneProof
#print axioms compactSequentFormulaStepParserClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectSequentFormulaStepParserTaskTransport
