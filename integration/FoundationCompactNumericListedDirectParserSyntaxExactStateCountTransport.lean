import integration.FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler
import integration.FoundationCompactCertifiedDerivationSpecialization

/-!
# Fixed PA transport for the exact parser state-count coordinate

The exact parser graph is one fixed fourteen-parameter formula.  This module
proves, once and for all, that replacing its state-count coordinate by an
equal term preserves the graph.  The fixed mother proof is later specialized
at the public parser terms; no varying proof-existence premise is introduced.
-/

open LO FirstOrder LO.FirstOrder LO.FirstOrder.Arithmetic

noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 700000

namespace FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport

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
open FoundationCompactNumericListedDirectParserInitialFinalRowsExactFuelFixedLeafBundle
open FoundationCompactNumericListedDirectParserSyntaxTraceFormula
open FoundationCompactNumericListedDirectParserSyntaxExactFormula
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectSyntax
open FoundationCompactNumericListedDirectParserSyntaxExactBoundedDirectCompiler

def compactParserSyntaxExactStateCountTransportSourceTerms :
    Fin 14 -> ArithmeticSemiterm Empty 15 :=
  ![(#0 : ArithmeticSemiterm Empty 15), #1, #2, #3, #4,
    #6, #7, #8, #9, #10, #11, #12, #13, #14]

def compactParserSyntaxExactStateCountTransportTargetTerms :
    Fin 14 -> ArithmeticSemiterm Empty 15 :=
  ![(#0 : ArithmeticSemiterm Empty 15), #1, #2, #3, #5,
    #6, #7, #8, #9, #10, #11, #12, #13, #14]

def compactParserSyntaxExactStateCountTransportSource :
    ArithmeticSemisentence 15 :=
  Rew.subst compactParserSyntaxExactStateCountTransportSourceTerms ▹
    compactParserSyntaxExactBoundedGraphDef.val

def compactParserSyntaxExactStateCountTransportTarget :
    ArithmeticSemisentence 15 :=
  Rew.subst compactParserSyntaxExactStateCountTransportTargetTerms ▹
    compactParserSyntaxExactBoundedGraphDef.val

def compactParserSyntaxExactStateCountTransportBody :
    ArithmeticSemisentence 15 :=
  (“#4 = #5” : ArithmeticSemisentence 15) 🡒
    compactParserSyntaxExactStateCountTransportSource 🡒
      compactParserSyntaxExactStateCountTransportTarget

def compactParserSyntaxExactStateCountTransportSentence :
    ArithmeticSentence :=
  ∀⁰* compactParserSyntaxExactStateCountTransportBody

theorem compactParserSyntaxExactStateCountTransportBody_valid
    {M : Type*} [ORingStructure M]
    (environment : Fin 15 -> M) :
    Semiformula.Eval environment Empty.elim
      compactParserSyntaxExactStateCountTransportBody := by
  simp only [compactParserSyntaxExactStateCountTransportBody,
    LO.LogicalConnective.HomClass.map_imply]
  intro hstate hsource
  have hstate' : environment 4 = environment 5 := by
    simpa using hstate
  have hterms :
      (Semiterm.val environment Empty.elim ∘
          compactParserSyntaxExactStateCountTransportSourceTerms) =
        (Semiterm.val environment Empty.elim ∘
          compactParserSyntaxExactStateCountTransportTargetTerms) := by
    funext coordinate
    fin_cases coordinate <;>
      simp [compactParserSyntaxExactStateCountTransportSourceTerms,
        compactParserSyntaxExactStateCountTransportTargetTerms,
        hstate']
  unfold compactParserSyntaxExactStateCountTransportSource at hsource
  unfold compactParserSyntaxExactStateCountTransportTarget
  simp only [Semiformula.eval_rew] at hsource ⊢
  have hbound :
      (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactStateCountTransportSourceTerms) ∘
          Semiterm.bvar) =
        (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactStateCountTransportTargetTerms) ∘
          Semiterm.bvar) := by
    funext coordinate
    simpa [Function.comp_def, Rew.subst_bvar] using
      congrFun hterms coordinate
  have hfree :
      (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactStateCountTransportSourceTerms) ∘
          Semiterm.fvar) =
        (Semiterm.val environment Empty.elim ∘
          (Rew.subst
            compactParserSyntaxExactStateCountTransportTargetTerms) ∘
          Semiterm.fvar) := by
    funext coordinate
    exact Empty.elim coordinate
  rw [hbound, hfree] at hsource
  exact hsource

theorem compactParserSyntaxExactStateCountTransportSentence_valid
    {M : Type*} [ORingStructure M] :
    M↓[ℒₒᵣ] ⊧ compactParserSyntaxExactStateCountTransportSentence := by
  rw [models_iff]
  simp only [compactParserSyntaxExactStateCountTransportSentence,
    Semiformula.eval_allClosure]
  exact fun environment =>
    compactParserSyntaxExactStateCountTransportBody_valid environment

noncomputable def compactParserSyntaxExactStateCountTransportProvable :
    PA ⊢ compactParserSyntaxExactStateCountTransportSentence :=
  LO.FirstOrder.Arithmetic.complete.{0} PA
    compactParserSyntaxExactStateCountTransportSentence
    (fun (_ : Type) _ _ =>
      compactParserSyntaxExactStateCountTransportSentence_valid)

noncomputable def compactParserSyntaxExactStateCountTransportDerivation :
    LO.FirstOrder.Derivation2 PA
      {(compactParserSyntaxExactStateCountTransportSentence :
        ArithmeticProposition)} :=
  compactParserSyntaxExactStateCountTransportProvable.get.toProof2

noncomputable def compactParserSyntaxExactStateCountTransportProof :
    CertifiedPAProof
      (compactParserSyntaxExactStateCountTransportSentence :
        ArithmeticProposition) where
  derivation := compactParserSyntaxExactStateCountTransportDerivation
  certificate :=
    certificateOfDerivation
      compactParserSyntaxExactStateCountTransportDerivation
  certificate_valid :=
    certificateOfDerivation_valid
      compactParserSyntaxExactStateCountTransportDerivation

def allClosureSpecializationTailTerms
    {arity : Nat}
    (terms : Fin (arity + 1) -> ArithmeticSemiterm Nat 0) :
    Fin arity -> ArithmeticSemiterm Nat 0 :=
  fun coordinate => terms coordinate.succ

private theorem allClosureSpecializationTailFormula
    {arity : Nat}
    (formula : ArithmeticSemiformula Nat (arity + 1))
    (terms : Fin (arity + 1) -> ArithmeticSemiterm Nat 0) :
    (Rew.subst (allClosureSpecializationTailTerms terms) ▹
        (∀⁰ formula : ArithmeticSemiformula Nat arity)) =
      ∀⁰ ((Rew.subst
        (allClosureSpecializationTailTerms terms)).q ▹ formula) := by
  simp

private theorem allClosureSpecializationHeadFormula
    {arity : Nat}
    (formula : ArithmeticSemiformula Nat (arity + 1))
    (terms : Fin (arity + 1) -> ArithmeticSemiterm Nat 0) :
    ((Rew.subst
        (allClosureSpecializationTailTerms terms)).q ▹ formula)/[terms 0] =
      Rew.subst terms ▹ formula := by
  change
    Rew.subst ![terms 0] ▹
        ((Rew.subst
          (allClosureSpecializationTailTerms terms)).q ▹ formula) =
      Rew.subst terms ▹ formula
  rw [← TransitiveRewriting.comp_app]
  apply Rewriting.smul_ext'
  rw [Rew.q_subst, Rew.subst_comp_subst]
  apply congrArg Rew.subst
  funext coordinate
  cases coordinate using Fin.cases with
  | zero => simp
  | succ coordinate =>
      simp [allClosureSpecializationTailTerms]

noncomputable def specializeAllClosure :
    {arity : Nat} ->
    (formula : ArithmeticSemiformula Nat arity) ->
    CertifiedPAProof (∀⁰* formula) ->
    (terms : Fin arity -> ArithmeticSemiterm Nat 0) ->
    CertifiedPAProof (Rew.subst terms ▹ formula)
  | 0, formula, proof, terms =>
      CertifiedPAProof.cast (by
        simpa using
          (Semiformula.rew_eq_self_of
            (φ := formula)
            (ω := Rew.subst terms)
            (fun coordinate => Fin.elim0 coordinate)
            (fun _ _ => rfl)).symm) proof
  | arity + 1, formula, proof, terms => by
      let tailTerms := allClosureSpecializationTailTerms terms
      let tailProof := specializeAllClosure
        (∀⁰ formula : ArithmeticSemiformula Nat arity) proof tailTerms
      let body :=
        (Rew.subst tailTerms).q ▹ formula
      let universalProof : CertifiedPAProof (∀⁰ body) :=
        CertifiedPAProof.cast
          (allClosureSpecializationTailFormula formula terms) tailProof
      let headProof := CertifiedPAProof.specialize universalProof (terms 0)
      exact CertifiedPAProof.cast
        (allClosureSpecializationHeadFormula formula terms) headProof

def allClosureSpecializationCost :
    {arity : Nat} ->
    (formula : ArithmeticSemiformula Nat arity) ->
    (terms : Fin arity -> ArithmeticSemiterm Nat 0) ->
    Nat
  | 0, _formula, _terms => 0
  | arity + 1, formula, terms =>
      let tailTerms := allClosureSpecializationTailTerms terms
      allClosureSpecializationCost
          (∀⁰ formula : ArithmeticSemiformula Nat arity) tailTerms +
        CertifiedPAProof.specializationCost
          ((Rew.subst tailTerms).q ▹ formula) (terms 0)

theorem specializeAllClosure_payloadLength_le :
    {arity : Nat} ->
    (formula : ArithmeticSemiformula Nat arity) ->
    (proof : CertifiedPAProof (∀⁰* formula)) ->
    (terms : Fin arity -> ArithmeticSemiterm Nat 0) ->
    (specializeAllClosure formula proof terms).payloadLength <=
      proof.payloadLength +
        allClosureSpecializationCost formula terms
  | 0, formula, proof, terms => by
      change
        (CertifiedPAProof.cast _ proof).payloadLength <=
          proof.payloadLength + 0
      rw [CertifiedPAProof.cast_payloadLength]
      omega
  | arity + 1, formula, proof, terms => by
      let tailTerms := allClosureSpecializationTailTerms terms
      let tailProof := specializeAllClosure
        (∀⁰ formula : ArithmeticSemiformula Nat arity) proof tailTerms
      let body := (Rew.subst tailTerms).q ▹ formula
      let universalProof : CertifiedPAProof (∀⁰ body) :=
        CertifiedPAProof.cast
          (allClosureSpecializationTailFormula formula terms) tailProof
      let headProof := CertifiedPAProof.specialize universalProof (terms 0)
      have htail :=
        specializeAllClosure_payloadLength_le
          (∀⁰ formula : ArithmeticSemiformula Nat arity) proof tailTerms
      have hhead :=
        CertifiedPAProof.specialize_payloadLength_le_cost
          universalProof (terms 0)
      change
        (CertifiedPAProof.cast
          (allClosureSpecializationHeadFormula formula terms)
          headProof).payloadLength <= _
      rw [CertifiedPAProof.cast_payloadLength]
      have huniversal :
          universalProof.payloadLength = tailProof.payloadLength := by
        dsimp only [universalProof]
        rw [CertifiedPAProof.cast_payloadLength]
      change
        headProof.payloadLength <=
          proof.payloadLength +
            (allClosureSpecializationCost
                (∀⁰ formula : ArithmeticSemiformula Nat arity) tailTerms +
              CertifiedPAProof.specializationCost body (terms 0))
      calc
        headProof.payloadLength <=
            universalProof.payloadLength +
              CertifiedPAProof.specializationCost body (terms 0) := hhead
        _ = tailProof.payloadLength +
              CertifiedPAProof.specializationCost body (terms 0) := by
            rw [huniversal]
        _ <=
            (proof.payloadLength +
                allClosureSpecializationCost
                  (∀⁰ formula : ArithmeticSemiformula Nat arity)
                  tailTerms) +
              CertifiedPAProof.specializationCost body (terms 0) :=
            Nat.add_le_add_right htail _
        _ = proof.payloadLength +
              (allClosureSpecializationCost
                  (∀⁰ formula : ArithmeticSemiformula Nat arity)
                  tailTerms +
                CertifiedPAProof.specializationCost body (terms 0)) := by
            omega

def compactParserSyntaxExactStateCountTransportBodyNat :
    ArithmeticSemiformula Nat 15 :=
  Rewriting.emb compactParserSyntaxExactStateCountTransportBody

theorem compactParserSyntaxExactStateCountTransportClosure_alignment :
    (∀⁰* compactParserSyntaxExactStateCountTransportBodyNat) =
      (compactParserSyntaxExactStateCountTransportSentence :
        ArithmeticProposition) := by
  simp [compactParserSyntaxExactStateCountTransportBodyNat,
    compactParserSyntaxExactStateCountTransportSentence]

def compactParserSyntaxExactCompositeStateCountPublicTerms
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    Fin 14 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    (‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’ :
      ValuationTerm),
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount,
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm valueBound]

def compactParserSyntaxExactCompositeStateCountClosedFormula
    (tokenTable width tokenCount stateBoundary inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound : Nat) :
    ValuationFormula :=
  (Rewriting.emb (ξ := Nat) compactParserSyntaxExactBoundedGraphDef.val) ⇜
    compactParserSyntaxExactCompositeStateCountPublicTerms tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound

def compactParserSyntaxExactStateCountTransportPublicTerms
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Fin 15 -> ValuationTerm :=
  ![shortBinaryNumeralTerm tokenTable,
    shortBinaryNumeralTerm width,
    shortBinaryNumeralTerm tokenCount,
    shortBinaryNumeralTerm stateBoundary,
    shortBinaryNumeralTerm stateCount,
    (‘!!(compactParserSyntaxExactFuelTerm inputCount) + 1’ :
      ValuationTerm),
    shortBinaryNumeralTerm inputBoundary,
    shortBinaryNumeralTerm inputCount,
    shortBinaryNumeralTerm expectedBoundary,
    shortBinaryNumeralTerm expectedCount,
    shortBinaryNumeralTerm taskKind,
    shortBinaryNumeralTerm taskBinderArity,
    shortBinaryNumeralTerm taskRepeatCount,
    shortBinaryNumeralTerm tableWidth,
    shortBinaryNumeralTerm valueBound]

def compactParserSyntaxExactStateCountTransportPublicFormula
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    ValuationFormula :=
  compactParserInitialFinalExactFuelCountFormula stateCount inputCount 🡒
    compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound 🡒
    compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound

theorem compactParserSyntaxExactStateCountTransportPublicFormula_alignment
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Rew.subst
        (compactParserSyntaxExactStateCountTransportPublicTerms tokenTable
          width tokenCount stateBoundary stateCount inputBoundary inputCount
          expectedBoundary expectedCount taskKind taskBinderArity
          taskRepeatCount tableWidth valueBound) ▹
      compactParserSyntaxExactStateCountTransportBodyNat =
    compactParserSyntaxExactStateCountTransportPublicFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
  simp [compactParserSyntaxExactStateCountTransportBodyNat,
    compactParserSyntaxExactStateCountTransportBody,
    compactParserSyntaxExactStateCountTransportSource,
    compactParserSyntaxExactStateCountTransportTarget,
    compactParserSyntaxExactStateCountTransportPublicFormula,
    compactParserInitialFinalExactFuelCountFormula,
    compactParserSyntaxExactBoundedDirectClosedFormula,
    compactParserSyntaxExactCompositeStateCountClosedFormula,
    compactParserSyntaxExactStateCountTransportSourceTerms,
    compactParserSyntaxExactStateCountTransportTargetTerms,
    compactParserSyntaxExactStateCountTransportPublicTerms,
    compactParserSyntaxExactBoundedDirectPublicTerms,
    compactParserSyntaxExactCompositeStateCountPublicTerms,
    ← TransitiveRewriting.comp_app]
  constructor
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [compactParserSyntaxExactStateCountTransportSourceTerms,
          compactParserSyntaxExactStateCountTransportPublicTerms,
          compactParserSyntaxExactBoundedDirectPublicTerms,
          Rew.comp_app]
    · intro coordinate
      exact Empty.elim coordinate
  · apply Rewriting.smul_ext'
    apply Rew.ext
    · intro coordinate
      fin_cases coordinate <;>
        simp [compactParserSyntaxExactStateCountTransportTargetTerms,
          compactParserSyntaxExactStateCountTransportPublicTerms,
          compactParserSyntaxExactCompositeStateCountPublicTerms,
          Rew.comp_app]
    · intro coordinate
      exact Empty.elim coordinate

def compactParserSyntaxExactStateCountTransportPublicPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  compactParserSyntaxExactStateCountTransportProof.payloadLength +
    allClosureSpecializationCost
      compactParserSyntaxExactStateCountTransportBodyNat
      (compactParserSyntaxExactStateCountTransportPublicTerms tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound)

noncomputable def compactParserSyntaxExactStateCountTransportPublicProof
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    CertifiedPAProof
      (compactParserSyntaxExactStateCountTransportPublicFormula tokenTable
        width tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound) := by
  let baseProof : CertifiedPAProof
      (∀⁰* compactParserSyntaxExactStateCountTransportBodyNat) :=
    CertifiedPAProof.cast
      compactParserSyntaxExactStateCountTransportClosure_alignment.symm
      compactParserSyntaxExactStateCountTransportProof
  let specializedProof := specializeAllClosure
    compactParserSyntaxExactStateCountTransportBodyNat baseProof
    (compactParserSyntaxExactStateCountTransportPublicTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound)
  exact CertifiedPAProof.cast
    (compactParserSyntaxExactStateCountTransportPublicFormula_alignment
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound)
    specializedProof

theorem
    compactParserSyntaxExactStateCountTransportPublicProof_payloadLength_le
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    (compactParserSyntaxExactStateCountTransportPublicProof tokenTable width
        tokenCount stateBoundary stateCount inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound).payloadLength <=
      compactParserSyntaxExactStateCountTransportPublicPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound := by
  let publicTerms :=
    compactParserSyntaxExactStateCountTransportPublicTerms tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let baseProof : CertifiedPAProof
      (∀⁰* compactParserSyntaxExactStateCountTransportBodyNat) :=
    CertifiedPAProof.cast
      compactParserSyntaxExactStateCountTransportClosure_alignment.symm
      compactParserSyntaxExactStateCountTransportProof
  have hspecialized :=
    specializeAllClosure_payloadLength_le
      compactParserSyntaxExactStateCountTransportBodyNat baseProof publicTerms
  change
    (CertifiedPAProof.cast _
      (specializeAllClosure
        compactParserSyntaxExactStateCountTransportBodyNat baseProof
        publicTerms)).payloadLength <= _
  rw [CertifiedPAProof.cast_payloadLength]
  have hbase :
      baseProof.payloadLength =
        compactParserSyntaxExactStateCountTransportProof.payloadLength := by
    dsimp only [baseProof]
    rw [CertifiedPAProof.cast_payloadLength]
  rw [hbase] at hspecialized
  exact hspecialized

def compactParserSyntaxExactCompositeStateCountDirectPayloadEnvelope
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat) :
    Nat :=
  let countFormula :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let sourceFormula :=
    compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let targetFormula :=
    compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  let transportFormula :=
    compactParserSyntaxExactStateCountTransportPublicFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  compactParserSyntaxExactStateCountTransportPublicPayloadEnvelope tokenTable
      width tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound +
    weakeningFullAssemblyCost (insert transportFormula ∅) +
    compactParserInitialFinalExactFuelCountResource inputCount +
    contextualModusPonensFullAssemblyCost ∅ countFormula
      (sourceFormula 🡒 targetFormula) +
    compactParserSyntaxExactBoundedDirectPayloadEnvelope tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound +
    contextualModusPonensFullAssemblyCost ∅ sourceFormula targetFormula

noncomputable def
    compactParserSyntaxExactCompositeStateCountClosedDirectBoundOfGraph
    (tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound : Nat)
    (hgraph : CompactParserSyntaxExactBoundedGraph tokenTable width tokenCount
      stateBoundary stateCount inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound) :
    ParserSyntaxExactBoundedClosedDirectBound
      (compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable
        width tokenCount stateBoundary inputBoundary inputCount
        expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound)
      (compactParserSyntaxExactCompositeStateCountDirectPayloadEnvelope
        tokenTable width tokenCount stateBoundary stateCount inputBoundary
        inputCount expectedBoundary expectedCount taskKind taskBinderArity
        taskRepeatCount tableWidth valueBound) := by
  have htrace : CompactParserSyntaxTraceBoundedGraph tokenTable width
      tokenCount stateBoundary stateCount
      (compactParserSyntaxExactFuel inputCount) inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound := by
    simpa [CompactParserSyntaxExactBoundedGraph,
      compactParserSyntaxExactFuel] using hgraph
  let countBound :=
    parserInitialFinalExactFuelCountClosedDirectBound stateCount inputCount
      htrace.1
  let sourceBound :=
    compactParserSyntaxExactBoundedClosedDirectBoundOfGraph tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound hgraph
  let transportClosed :=
    compactParserSyntaxExactStateCountTransportPublicProof tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let transportContext :=
    CertifiedPAContextProof.weakenCertified ∅ transportClosed
  let afterCount :=
    CertifiedPAContextProof.modusPonens transportContext countBound.proof
  let proof :=
    CertifiedPAContextProof.modusPonens afterCount sourceBound.proof
  let transportEnvelope :=
    compactParserSyntaxExactStateCountTransportPublicPayloadEnvelope
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound
  let transportFormula :=
    compactParserSyntaxExactStateCountTransportPublicFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let weakenCost :=
    weakeningFullAssemblyCost (insert transportFormula ∅)
  let countFormula :=
    compactParserInitialFinalExactFuelCountFormula stateCount inputCount
  let countEnvelope :=
    compactParserInitialFinalExactFuelCountResource inputCount
  let sourceFormula :=
    compactParserSyntaxExactBoundedDirectClosedFormula tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let targetFormula :=
    compactParserSyntaxExactCompositeStateCountClosedFormula tokenTable width
      tokenCount stateBoundary inputBoundary inputCount expectedBoundary
      expectedCount taskKind taskBinderArity taskRepeatCount tableWidth
      valueBound
  let firstCost :=
    contextualModusPonensFullAssemblyCost ∅ countFormula
      (sourceFormula 🡒 targetFormula)
  let sourceEnvelope :=
    compactParserSyntaxExactBoundedDirectPayloadEnvelope tokenTable width
      tokenCount stateBoundary stateCount inputBoundary inputCount
      expectedBoundary expectedCount taskKind taskBinderArity taskRepeatCount
      tableWidth valueBound
  let secondCost :=
    contextualModusPonensFullAssemblyCost ∅ sourceFormula targetFormula
  refine { proof := proof, payloadLength_le := ?_ }
  have htransport :=
    compactParserSyntaxExactStateCountTransportPublicProof_payloadLength_le
      tokenTable width tokenCount stateBoundary stateCount inputBoundary
      inputCount expectedBoundary expectedCount taskKind taskBinderArity
      taskRepeatCount tableWidth valueBound
  have hweaken :=
    CertifiedPAContextProof.weakenCertified_payloadLength_le ∅ transportClosed
  have hcount := countBound.payloadLength_le
  have hsource := sourceBound.payloadLength_le
  have hfirst :=
    CertifiedPAContextProof.modusPonens_payloadLength_le transportContext
      countBound.proof
  have hsecond :=
    CertifiedPAContextProof.modusPonens_payloadLength_le afterCount
      sourceBound.proof
  have htransport' :
      transportClosed.payloadLength <= transportEnvelope := by
    simpa [transportClosed, transportEnvelope] using htransport
  have hweaken' :
      transportContext.payloadLength <=
        transportClosed.payloadLength + weakenCost := by
    simpa [transportContext, weakenCost, transportFormula] using hweaken
  have hcount' :
      countBound.proof.payloadLength <= countEnvelope := by
    simpa [countEnvelope] using hcount
  have hsource' :
      sourceBound.proof.payloadLength <= sourceEnvelope := by
    simpa [sourceEnvelope] using hsource
  have hfirst' :
      afterCount.payloadLength <=
        transportContext.payloadLength + countBound.proof.payloadLength +
          firstCost := by
    exact hfirst
  have hsecond' :
      proof.payloadLength <=
        afterCount.payloadLength + sourceBound.proof.payloadLength +
          secondCost := by
    exact hsecond
  have hcontext :
      transportContext.payloadLength <=
        transportEnvelope + weakenCost :=
    hweaken'.trans (by omega)
  have hafter :
      afterCount.payloadLength <=
        transportEnvelope + weakenCost + countEnvelope + firstCost :=
    hfirst'.trans (by omega)
  have hproof :
      proof.payloadLength <=
        transportEnvelope + weakenCost + countEnvelope + firstCost +
          sourceEnvelope + secondCost :=
    hsecond'.trans (by omega)
  change proof.payloadLength <=
    transportEnvelope + weakenCost + countEnvelope + firstCost +
      sourceEnvelope + secondCost
  exact hproof

#print axioms compactParserSyntaxExactStateCountTransportBody_valid
#print axioms compactParserSyntaxExactStateCountTransportSentence_valid
#print axioms compactParserSyntaxExactStateCountTransportProof
#print axioms specializeAllClosure
#print axioms specializeAllClosure_payloadLength_le
#print axioms
  compactParserSyntaxExactStateCountTransportPublicFormula_alignment
#print axioms compactParserSyntaxExactStateCountTransportPublicProof
#print axioms
  compactParserSyntaxExactStateCountTransportPublicProof_payloadLength_le
#print axioms
  compactParserSyntaxExactCompositeStateCountClosedDirectBoundOfGraph

end FoundationCompactNumericListedDirectParserSyntaxExactStateCountTransport
