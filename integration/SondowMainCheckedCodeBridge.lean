/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import EulerLimit.SondowShortProofReproof
import BoundedArithmeticLab.SondowHilbertProofCodeBridge

/-!
# Main Sondow accepted-code bridge to the bounded-arithmetic sidecar

This file is intentionally outside both Lake libraries.  It is an integration
probe: the main repository stays independent of the sidecar, while Lean verifies
that the main `AcceptedCertificateCodeSemantics` interface can be adapted to the
sidecar `ExternalAcceptedCheckedCodeSemantics` interface.

The reverse direction is not stated.  Main `AcceptedCertificateCodeSemantics`
contains a total `ProofCodeSemantics.complete` field on its relevant fragment,
which is stronger than the sidecar's conditional
`accepted n ↔ ∃ checked code at n` interface.
-/

open BoundedArithmeticLab

namespace SondowMainCheckedCodeBridge

universe u

/-- The main Sondow accepted predicate, named so the bridge statements do not
hide their target behind repeated lambda expressions. -/
abbrev mainSondowAcceptedAt (n : ℕ) : Prop :=
  _root_.accepted_certificate
    (_root_.sondowCertificateValidCode n)

/-- The concrete checked-code predicate exposed by the main definition of
`accepted_certificate` for `sondowCertificateValidCode`: a checked code is the
rational parameter `q` together with the full Sondow certificate acceptance
predicate at index `n`. -/
abbrev mainSondowFullCertificateChecks (q : ℚ) (n : ℕ) : Prop :=
  _root_.full_sondow_certificate_accepted q n

/-- Exact source propositions exposed by the current main-library full Sondow
certificate.  The `threePowSource` field is the tail-bound certificate source:
in the current main route the `3^n` input enters through the tail estimate used
to prove `sondow_term_lt_one_prop`. -/
structure MainSondowFullCertificateSourceComponents (q : ℚ) (n : ℕ) :
    Prop where
  gamma_eq : (q : ℝ) = _root_.euler_mascheroni
  threePowSource : _root_.tail_bound_certificate_accepted n
  denominatorSource : _root_.denominator_certificate_accepted q n
  productLogSource : _root_.sondow_explicit_product_log_relation_prop n
  decompositionSource : _root_.sondow_explicit_decomposition_prop n

structure MainSondowProductLogSourceCertificate where
  index : ℕ
  source : _root_.sondow_explicit_product_log_relation_prop index

structure MainSondowDecompositionSourceCertificate where
  index : ℕ
  source : _root_.sondow_explicit_decomposition_prop index

structure MainSondowThreePowSourceCertificate where
  index : ℕ
  source : _root_.tail_bound_certificate_accepted index

structure MainSondowPayloadSourceCertificate where
  index : ℕ
  q : ℚ
  source :
    ((q : ℝ) = _root_.euler_mascheroni ∧
      _root_.denominator_certificate_accepted q index)

namespace MainSondowFullCertificateSourceComponents

def productLogCertificate
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    MainSondowProductLogSourceCertificate where
  index := n
  source := hsource.productLogSource

def decompositionCertificate
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    MainSondowDecompositionSourceCertificate where
  index := n
  source := hsource.decompositionSource

def threePowCertificate
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    MainSondowThreePowSourceCertificate where
  index := n
  source := hsource.threePowSource

def payloadCertificate
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    MainSondowPayloadSourceCertificate where
  index := n
  q := q
  source := ⟨hsource.gamma_eq, hsource.denominatorSource⟩

end MainSondowFullCertificateSourceComponents

theorem mainSondowFullCertificateChecks_iff_sourceComponents
    (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n := by
  unfold mainSondowFullCertificateChecks
  unfold _root_.full_sondow_certificate_accepted
  unfold _root_.rational_sondow_certificate_components_accepted
  constructor
  · intro hchecked
    rcases hchecked with
      ⟨hgamma, ⟨hthree, hdenominator⟩, hproductLog, hdecomposition⟩
    exact
      { gamma_eq := hgamma
        threePowSource := hthree
        denominatorSource := hdenominator
        productLogSource := hproductLog
        decompositionSource := hdecomposition }
  · intro hsource
    exact
      ⟨hsource.gamma_eq,
        ⟨hsource.threePowSource, hsource.denominatorSource⟩,
        hsource.productLogSource,
        hsource.decompositionSource⟩

/-- The first hard item is now closed definitionally:
`accepted_certificate (sondowCertificateValidCode n)` is exactly the existence
of a rational parameter whose full Sondow certificate is accepted at `n`. -/
def mainSondowFullCertificateCheckedCodeSemantics :
    ExternalAcceptedCheckedCodeSemantics.{u} mainSondowAcceptedAt where
  Code := ULift.{u} ℚ
  checksAt := fun q n => mainSondowFullCertificateChecks q.down n
  size := fun _q => 1
  accepted_iff_checked_at := by
    intro n
    constructor
    · intro haccepted
      rcases haccepted with ⟨q, hq⟩
      exact ⟨ULift.up q, hq⟩
    · intro hchecked
      rcases hchecked with ⟨q, hq⟩
      exact ⟨q.down, hq⟩

def proofObjectAcceptedTrace
    {target : ℕ → BAFormula} {bound : ℕ → ℝ} {n : ℕ}
    (proof : BAProofObject BussS21Axiom)
    (hconclusion : proof.conclusion = target n)
    (hsize : (((proof.size + 2 : ℕ) : ℝ)) ≤ bound n) :
    CertificateVerifierMachine.AcceptedTrace
      (proofCertificateVerifierMachine target bound) n where
  cert := proof
  final :=
    ProofCertificateState.accepted n proof hconclusion hsize
  steps := 1
  reaches :=
    CertificateVerifierMachine.Reaches.cons
      (ProofCertificateState.Step.accept hconclusion hsize)
      (CertificateVerifierMachine.Reaches.refl _)
  accepts := by
    simp [proofCertificateVerifierMachine, ProofCertificateState.accepting]

def bussS21AxiomProofObject
    {φ : BAFormula} (hφ : BussS21Axiom φ) :
    BAProofObject BussS21Axiom where
  conclusion := φ
  derivation := BADerivation.ax hφ

def polytimeDefinabilityProofObject
    (name : ℕ) (graph : BAFormula) :
    BAProofObject BussS21Axiom :=
  bussS21AxiomProofObject
    (BussS21Axiom.polytimeDefinability name graph)

theorem not_bussS21Axiom_projectComponentAtom
    (family : BoundedArithmeticLab.FormulaFamily) (n : ℕ) :
    ¬ BussS21Axiom (projectComponentAtom family n) := by
  intro h
  cases h

theorem not_bussS21Axiom_sondowProductFormula (n : ℕ) :
    ¬ BussS21Axiom (sondowProductFormula n) := by
  simpa [sondowProductFormula] using
    not_bussS21Axiom_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowProduct n

theorem not_bussS21Axiom_sondowLogRelationFormula (n : ℕ) :
    ¬ BussS21Axiom (sondowLogRelationFormula n) := by
  simpa [sondowLogRelationFormula] using
    not_bussS21Axiom_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowLogRelation n

theorem not_bussS21Axiom_sondowDecompositionFormula (n : ℕ) :
    ¬ BussS21Axiom (sondowDecompositionFormula n) := by
  simpa [sondowDecompositionFormula] using
    not_bussS21Axiom_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowDecomposition n

theorem not_bussS21Axiom_sondowThreePowFormula (n : ℕ) :
    ¬ BussS21Axiom (sondowThreePowFormula n) := by
  simpa [sondowThreePowFormula] using
    not_bussS21Axiom_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowThreePow n

theorem not_bussS21Axiom_sondowPayloadFormula (n : ℕ) :
    ¬ BussS21Axiom (sondowPayloadFormula n) := by
  simpa [sondowPayloadFormula] using
    not_bussS21Axiom_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowPayload n

/-- Audit probe: none of the five project component atoms is currently a direct
Buss S21 axiom.  Any proof object for these atoms must therefore come from an
explicit derivation/compiler route, not from a hidden project-atom axiom. -/
structure SondowProjectComponentAtomsNotDirectBussS21Axioms : Prop where
  product : ∀ n : ℕ, ¬ BussS21Axiom (sondowProjectComponentFormulas.product n)
  logRelation :
    ∀ n : ℕ, ¬ BussS21Axiom (sondowProjectComponentFormulas.logRelation n)
  decomposition :
    ∀ n : ℕ, ¬ BussS21Axiom (sondowProjectComponentFormulas.decomposition n)
  threePow :
    ∀ n : ℕ, ¬ BussS21Axiom (sondowProjectComponentFormulas.threePow n)
  payload : ∀ n : ℕ, ¬ BussS21Axiom (sondowProjectComponentFormulas.payload n)

theorem sondowProjectComponentAtoms_not_direct_bussS21Axioms :
    SondowProjectComponentAtomsNotDirectBussS21Axioms where
  product := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Axiom_sondowProductFormula n
  logRelation := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Axiom_sondowLogRelationFormula n
  decomposition := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Axiom_sondowDecompositionFormula n
  threePow := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Axiom_sondowThreePowFormula n
  payload := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Axiom_sondowPayloadFormula n

namespace BAFormula

/-- Audit semantics for the current narrow Buss S21 object language.  All
project atoms are false, while the built-in equality/order and bounded
quantifier wrappers are true.  This is not mathematical semantics; it is a
syntactic no-free-proof probe for bare project atoms. -/
def auditTrue : BAFormula → Prop
  | BAFormula.atom _ _ => False
  | BAFormula.falsum => False
  | BAFormula.equal _ _ => True
  | BAFormula.le _ _ => True
  | BAFormula.not φ => ¬ auditTrue φ
  | BAFormula.and φ ψ => auditTrue φ ∧ auditTrue ψ
  | BAFormula.or φ ψ => auditTrue φ ∨ auditTrue ψ
  | BAFormula.imp φ ψ => auditTrue φ → auditTrue ψ
  | BAFormula.forallBounded _ _ _ => True
  | BAFormula.existsBounded _ _ _ => True

end BAFormula

theorem BussS21Axiom.auditTrue {φ : BAFormula}
    (hφ : BussS21Axiom φ) :
    BAFormula.auditTrue φ := by
  cases hφ <;>
    simp [BAFormula.auditTrue, sigmaBInductionFormula,
      polytimeDefinabilityFormula]

theorem BADerivation.auditTrue
    {Ax : BAFormula → Prop}
    (hAx : ∀ {φ : BAFormula}, Ax φ → BAFormula.auditTrue φ)
    {φ : BAFormula}
    (derivation : BADerivation Ax φ) :
    BAFormula.auditTrue φ := by
  induction derivation with
  | ax h =>
      exact hAx h
  | andIntro _ _ hp hq =>
      simpa [BAFormula.auditTrue] using And.intro hp hq
  | @andElimRight A B _ hp =>
      have hp' : BAFormula.auditTrue A ∧ BAFormula.auditTrue B := by
        simpa [BAFormula.auditTrue] using hp
      exact hp'.2
  | @impIntro A B _ hp =>
      simpa [BAFormula.auditTrue] using (fun _h => hp)
  | @mp A B _ _ hp hq =>
      have hp' : BAFormula.auditTrue A → BAFormula.auditTrue B := by
        simpa [BAFormula.auditTrue] using hp
      exact hp' hq

theorem not_bussS21Derivable_projectComponentAtom
    (family : BoundedArithmeticLab.FormulaFamily) (n : ℕ) :
    BADerivation BussS21Axiom (projectComponentAtom family n) → False := by
  intro derivation
  simpa [projectComponentAtom, BAFormula.auditTrue] using
    (BADerivation.auditTrue
      (fun {φ : BAFormula} hφ => BussS21Axiom.auditTrue hφ)
      derivation)

theorem not_bussS21Derivable_sondowProductFormula (n : ℕ) :
    BADerivation BussS21Axiom (sondowProductFormula n) → False := by
  simpa [sondowProductFormula] using
    not_bussS21Derivable_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowProduct n

theorem not_bussS21Derivable_sondowLogRelationFormula (n : ℕ) :
    BADerivation BussS21Axiom (sondowLogRelationFormula n) → False := by
  simpa [sondowLogRelationFormula] using
    not_bussS21Derivable_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowLogRelation n

theorem not_bussS21Derivable_sondowDecompositionFormula (n : ℕ) :
    BADerivation BussS21Axiom (sondowDecompositionFormula n) → False := by
  simpa [sondowDecompositionFormula] using
    not_bussS21Derivable_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowDecomposition n

theorem not_bussS21Derivable_sondowThreePowFormula (n : ℕ) :
    BADerivation BussS21Axiom (sondowThreePowFormula n) → False := by
  simpa [sondowThreePowFormula] using
    not_bussS21Derivable_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowThreePow n

theorem not_bussS21Derivable_sondowPayloadFormula (n : ℕ) :
    BADerivation BussS21Axiom (sondowPayloadFormula n) → False := by
  simpa [sondowPayloadFormula] using
    not_bussS21Derivable_projectComponentAtom
      BoundedArithmeticLab.FormulaFamily.sondowPayload n

/-- Stronger audit probe: in the current narrow object language, the five
project component atoms are not merely non-axioms; they are not derivable at
all.  A real construction must therefore extend the object-language compiler
with genuine definitional/verification transport, then audit that extension. -/
structure SondowProjectComponentAtomsNotBussS21Derivable : Prop where
  product :
    ∀ n : ℕ,
      BADerivation BussS21Axiom
        (sondowProjectComponentFormulas.product n) → False
  logRelation :
    ∀ n : ℕ,
      BADerivation BussS21Axiom
        (sondowProjectComponentFormulas.logRelation n) → False
  decomposition :
    ∀ n : ℕ,
      BADerivation BussS21Axiom
        (sondowProjectComponentFormulas.decomposition n) → False
  threePow :
    ∀ n : ℕ,
      BADerivation BussS21Axiom
        (sondowProjectComponentFormulas.threePow n) → False
  payload :
    ∀ n : ℕ,
      BADerivation BussS21Axiom
        (sondowProjectComponentFormulas.payload n) → False

theorem sondowProjectComponentAtoms_not_bussS21Derivable :
    SondowProjectComponentAtomsNotBussS21Derivable where
  product := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Derivable_sondowProductFormula n
  logRelation := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Derivable_sondowLogRelationFormula n
  decomposition := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Derivable_sondowDecompositionFormula n
  threePow := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Derivable_sondowThreePowFormula n
  payload := by
    intro n
    simpa [sondowProjectComponentFormulas] using
      not_bussS21Derivable_sondowPayloadFormula n

@[simp] theorem polytimeDefinabilityProofObject_conclusion
    (name : ℕ) (graph : BAFormula) :
    (polytimeDefinabilityProofObject name graph).conclusion =
      polytimeDefinabilityFormula name graph :=
  rfl

@[simp] theorem polytimeDefinabilityProofObject_size
    (name : ℕ) (graph : BAFormula) :
    (polytimeDefinabilityProofObject name graph).size = 1 :=
  rfl

def BAProofObject.mp'
    {Ax : BAFormula → Prop} (pImp pArg : BAProofObject Ax)
    {A B : BAFormula}
    (hImp : pImp.conclusion = BAFormula.imp A B)
    (hArg : pArg.conclusion = A) :
    BAProofObject Ax where
  conclusion := B
  derivation := by
    cases pImp with
    | mk conclusionImp derivationImp =>
        cases pArg with
        | mk conclusionArg derivationArg =>
            dsimp at hImp hArg
            subst conclusionImp
            subst conclusionArg
            exact BADerivation.mp derivationImp derivationArg

theorem BAProofObject.size_mp'_eq
    {Ax : BAFormula → Prop} (pImp pArg : BAProofObject Ax)
    {A B : BAFormula}
    (hImp : pImp.conclusion = BAFormula.imp A B)
    (hArg : pArg.conclusion = A) :
    (BAProofObject.mp' pImp pArg hImp hArg).size =
      pImp.size + pArg.size + 1 := by
  cases pImp with
  | mk conclusionImp derivationImp =>
      cases pArg with
      | mk conclusionArg derivationArg =>
          dsimp at hImp hArg ⊢
          subst conclusionImp
          subst conclusionArg
          rfl

def BAProofObject.impIntro'
    {Ax : BAFormula → Prop} (pBody : BAProofObject Ax)
    (A : BAFormula) :
    BAProofObject Ax where
  conclusion := BAFormula.imp A pBody.conclusion
  derivation := BADerivation.impIntro pBody.derivation

@[simp] theorem BAProofObject.size_impIntro'
    {Ax : BAFormula → Prop} (pBody : BAProofObject Ax)
    (A : BAFormula) :
    (BAProofObject.impIntro' pBody A).size = pBody.size + 1 :=
  rfl

/-- A single project atom is justified by an explicit polytime-definability
formula plus an S21 transport proof from that formula to the project atom.  This
keeps the audit boundary visible: the atom itself is not declared by any S21
project axiom declaration. -/
structure ProjectAtomDefinabilityBridge
    (target : ℕ → BAFormula) (bound : ℕ → ℝ) where
  name : ℕ
  graph : ℕ → BAFormula
  graph_eq_target : ∀ n : ℕ, graph n = target n
  transportProof :
    ∀ _n : ℕ, BAProofObject BussS21Axiom
  transport_conclusion :
    ∀ n : ℕ,
      (transportProof n).conclusion =
        BAFormula.imp (polytimeDefinabilityFormula name (graph n))
          (target n)
  transport_size_plus_four_le :
    ∀ n : ℕ,
      ((((transportProof n).size + 4 : ℕ) : ℝ)) ≤ bound n

def ProjectAtomDefinabilityBridge.definabilityProof
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (bridge : ProjectAtomDefinabilityBridge target bound)
    (n : ℕ) :
    BAProofObject BussS21Axiom :=
  polytimeDefinabilityProofObject bridge.name (bridge.graph n)

def ProjectAtomDefinabilityBridge.proofObject
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (bridge : ProjectAtomDefinabilityBridge target bound)
    (n : ℕ) :
    BAProofObject BussS21Axiom :=
  BAProofObject.mp'
    (bridge.transportProof n)
    (bridge.definabilityProof n)
    (bridge.transport_conclusion n)
    rfl

@[simp] theorem ProjectAtomDefinabilityBridge.proofObject_conclusion
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (bridge : ProjectAtomDefinabilityBridge target bound)
    (n : ℕ) :
    (bridge.proofObject n).conclusion = target n :=
  rfl

theorem ProjectAtomDefinabilityBridge.proofObject_size_plus_two_le
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (bridge : ProjectAtomDefinabilityBridge target bound)
    (n : ℕ) :
    ((((bridge.proofObject n).size + 2 : ℕ) : ℝ)) ≤ bound n := by
  rw [ProjectAtomDefinabilityBridge.proofObject,
    BAProofObject.size_mp'_eq]
  simp [ProjectAtomDefinabilityBridge.definabilityProof]
  have htransport := bridge.transport_size_plus_four_le n
  have hcast :
      ((((bridge.transportProof n).size + 4 : ℕ) : ℝ)) =
        ((bridge.transportProof n).size : ℝ) + 1 + 1 + 2 := by
    rw [Nat.cast_add]
    ring_nf
  rw [hcast] at htransport
  simpa [add_assoc] using htransport

/-- Direct S21 proof objects for one project atom family.  This is the same
audit obligation as a definability bridge after accounting for the explicit
modus-ponens and implication-introduction overheads. -/
structure DirectProjectAtomProofBridge
    (target : ℕ → BAFormula) (bound : ℕ → ℝ) where
  proof : ∀ _n : ℕ, BAProofObject BussS21Axiom
  proof_conclusion :
    ∀ n : ℕ, (proof n).conclusion = target n
  proof_size_plus_two_le :
    ∀ n : ℕ, ((((proof n).size + 2 : ℕ) : ℝ)) ≤ bound n

def ProjectAtomDefinabilityBridge.toDirectProofBridge
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (bridge : ProjectAtomDefinabilityBridge target bound) :
    DirectProjectAtomProofBridge target bound where
  proof := bridge.proofObject
  proof_conclusion := bridge.proofObject_conclusion
  proof_size_plus_two_le := bridge.proofObject_size_plus_two_le

def DirectProjectAtomProofBridge.toDefinabilityBridgeWithOverhead
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (direct : DirectProjectAtomProofBridge target bound)
    (name : ℕ) (graph : ℕ → BAFormula)
    (hgraph : ∀ n : ℕ, graph n = target n) :
    ProjectAtomDefinabilityBridge target (fun n : ℕ => bound n + 3) where
  name := name
  graph := graph
  graph_eq_target := hgraph
  transportProof := fun n =>
    BAProofObject.impIntro'
      (direct.proof n)
      (polytimeDefinabilityFormula name (graph n))
  transport_conclusion := by
    intro n
    simp [BAProofObject.impIntro', direct.proof_conclusion n]
  transport_size_plus_four_le := by
    intro n
    simp
    have hdirect := direct.proof_size_plus_two_le n
    have hcast :
        ((((direct.proof n).size + 2 : ℕ) : ℝ)) + 3 =
          (((direct.proof n).size : ℝ) + 1 + 4) := by
      rw [Nat.cast_add]
      ring_nf
    have hdirect3 :
        (((direct.proof n).size : ℝ) + 1 + 4) ≤ bound n + 3 := by
      rw [← hcast]
      linarith
    simpa [add_assoc] using hdirect3

theorem projectAtomDefinabilityBridge_nonempty_to_directProofBridge_nonempty
    {target : ℕ → BAFormula} {bound : ℕ → ℝ} :
    Nonempty (ProjectAtomDefinabilityBridge target bound) →
      Nonempty (DirectProjectAtomProofBridge target bound) := by
  intro h
  rcases h with ⟨bridge⟩
  exact ⟨bridge.toDirectProofBridge⟩

theorem directProofBridge_nonempty_to_projectAtomDefinabilityBridge_nonempty_with_overhead
    {target : ℕ → BAFormula} {bound : ℕ → ℝ}
    (name : ℕ) (graph : ℕ → BAFormula)
    (hgraph : ∀ n : ℕ, graph n = target n) :
    Nonempty (DirectProjectAtomProofBridge target bound) →
      Nonempty
        (ProjectAtomDefinabilityBridge target
          (fun n : ℕ => bound n + 3)) := by
  intro h
  rcases h with ⟨direct⟩
  exact ⟨direct.toDefinabilityBridgeWithOverhead name graph hgraph⟩

/-- The remaining audit-facing compiler obligation in its sharpest concrete
form: from a full accepted Sondow certificate, produce the five S21 proof
objects, with exact conclusions and the declared component size bounds. -/
structure MainSondowFullCertificateComponentProofCompiler
    (bounds : SondowComponentBounds) where
  productProof :
    ∀ n : ℕ, ∀ q : ℚ, mainSondowFullCertificateChecks q n →
      BAProofObject BussS21Axiom
  logProof :
    ∀ n : ℕ, ∀ q : ℚ, mainSondowFullCertificateChecks q n →
      BAProofObject BussS21Axiom
  decompositionProof :
    ∀ n : ℕ, ∀ q : ℚ, mainSondowFullCertificateChecks q n →
      BAProofObject BussS21Axiom
  threePowProof :
    ∀ n : ℕ, ∀ q : ℚ, mainSondowFullCertificateChecks q n →
      BAProofObject BussS21Axiom
  payloadProof :
    ∀ n : ℕ, ∀ q : ℚ, mainSondowFullCertificateChecks q n →
      BAProofObject BussS21Axiom
  product_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      (productProof n q hchecked).conclusion =
        sondowProjectComponentFormulas.product n
  log_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      (logProof n q hchecked).conclusion =
        sondowProjectComponentFormulas.logRelation n
  decomposition_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      (decompositionProof n q hchecked).conclusion =
        sondowProjectComponentFormulas.decomposition n
  threePow_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      (threePowProof n q hchecked).conclusion =
        sondowProjectComponentFormulas.threePow n
  payload_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      (payloadProof n q hchecked).conclusion =
        sondowProjectComponentFormulas.payload n
  product_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((productProof n q hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.product n
  log_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((logProof n q hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.logRelation n
  decomposition_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((decompositionProof n q hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.decomposition n
  threePow_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((threePowProof n q hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.threePow n
  payload_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((payloadProof n q hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.payload n

/-- The proof-object compiler obligations after exposing the actual source
propositions contained in `full_sondow_certificate_accepted`.  This is narrower
and more auditable than asking for unconditional direct atom proofs: each
component proof object is allowed to use exactly the corresponding source
certificate extracted from the accepted full certificate. -/
structure MainSondowFullCertificateSourceComponentCompilers
    (bounds : SondowComponentBounds) where
  productProof :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.sondow_explicit_product_log_relation_prop n →
        BAProofObject BussS21Axiom
  logProof :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.sondow_explicit_product_log_relation_prop n →
        BAProofObject BussS21Axiom
  decompositionProof :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.sondow_explicit_decomposition_prop n →
        BAProofObject BussS21Axiom
  threePowProof :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.tail_bound_certificate_accepted n →
        BAProofObject BussS21Axiom
  payloadProof :
    ∀ n : ℕ, ∀ q : ℚ,
      ((q : ℝ) = _root_.euler_mascheroni ∧
        _root_.denominator_certificate_accepted q n) →
        BAProofObject BussS21Axiom
  product_conclusion :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_product_log_relation_prop n,
      (productProof n q hsource).conclusion =
        sondowProjectComponentFormulas.product n
  log_conclusion :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_product_log_relation_prop n,
      (logProof n q hsource).conclusion =
        sondowProjectComponentFormulas.logRelation n
  decomposition_conclusion :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_decomposition_prop n,
      (decompositionProof n q hsource).conclusion =
        sondowProjectComponentFormulas.decomposition n
  threePow_conclusion :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.tail_bound_certificate_accepted n,
      (threePowProof n q hsource).conclusion =
        sondowProjectComponentFormulas.threePow n
  payload_conclusion :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource :
        ((q : ℝ) = _root_.euler_mascheroni ∧
          _root_.denominator_certificate_accepted q n),
      (payloadProof n q hsource).conclusion =
        sondowProjectComponentFormulas.payload n
  product_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_product_log_relation_prop n,
      ((((productProof n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.product n
  log_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_product_log_relation_prop n,
      ((((logProof n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.logRelation n
  decomposition_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_decomposition_prop n,
      ((((decompositionProof n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.decomposition n
  threePow_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.tail_bound_certificate_accepted n,
      ((((threePowProof n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.threePow n
  payload_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource :
        ((q : ℝ) = _root_.euler_mascheroni ∧
          _root_.denominator_certificate_accepted q n),
      ((((payloadProof n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.payload n

def proofObjectOfBussS21Derivation {φ : BAFormula}
    (derivation : BADerivation BussS21Axiom φ) :
    BAProofObject BussS21Axiom where
  conclusion := φ
  derivation := derivation

@[simp] theorem proofObjectOfBussS21Derivation_conclusion
    {φ : BAFormula} (derivation : BADerivation BussS21Axiom φ) :
    (proofObjectOfBussS21Derivation derivation).conclusion = φ :=
  rfl

@[simp] theorem proofObjectOfBussS21Derivation_size
    {φ : BAFormula} (derivation : BADerivation BussS21Axiom φ) :
    (proofObjectOfBussS21Derivation derivation).size =
      derivation.size :=
  rfl

/-- Derivation-level source for the five project components.  This is the
bottom compiler layer: each accepted mathematical source certificate must be
realized as an actual S21 derivation of the corresponding project formula, with
the declared component size bound. -/
structure MainSondowFullCertificateS21DerivationSources
    (bounds : SondowComponentBounds) where
  productDerivation :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.sondow_explicit_product_log_relation_prop n →
        BADerivation BussS21Axiom
          (sondowProjectComponentFormulas.product n)
  logDerivation :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.sondow_explicit_product_log_relation_prop n →
        BADerivation BussS21Axiom
          (sondowProjectComponentFormulas.logRelation n)
  decompositionDerivation :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.sondow_explicit_decomposition_prop n →
        BADerivation BussS21Axiom
          (sondowProjectComponentFormulas.decomposition n)
  threePowDerivation :
    ∀ n : ℕ, ∀ _q : ℚ,
      _root_.tail_bound_certificate_accepted n →
        BADerivation BussS21Axiom
          (sondowProjectComponentFormulas.threePow n)
  payloadDerivation :
    ∀ n : ℕ, ∀ q : ℚ,
      ((q : ℝ) = _root_.euler_mascheroni ∧
        _root_.denominator_certificate_accepted q n) →
        BADerivation BussS21Axiom
          (sondowProjectComponentFormulas.payload n)
  product_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_product_log_relation_prop n,
      ((((productDerivation n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.product n
  log_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_product_log_relation_prop n,
      ((((logDerivation n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.logRelation n
  decomposition_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.sondow_explicit_decomposition_prop n,
      ((((decompositionDerivation n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.decomposition n
  threePow_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource : _root_.tail_bound_certificate_accepted n,
      ((((threePowDerivation n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.threePow n
  payload_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ,
      ∀ hsource :
        ((q : ℝ) = _root_.euler_mascheroni ∧
          _root_.denominator_certificate_accepted q n),
      ((((payloadDerivation n q hsource).size + 2 : ℕ) : ℝ)) ≤
        bounds.payload n

def MainSondowFullCertificateS21DerivationSources.toSourceComponentCompilers
    {bounds : SondowComponentBounds}
    (sources :
      MainSondowFullCertificateS21DerivationSources bounds) :
    MainSondowFullCertificateSourceComponentCompilers bounds where
  productProof := by
    intro n q hsource
    exact proofObjectOfBussS21Derivation
      (sources.productDerivation n q hsource)
  logProof := by
    intro n q hsource
    exact proofObjectOfBussS21Derivation
      (sources.logDerivation n q hsource)
  decompositionProof := by
    intro n q hsource
    exact proofObjectOfBussS21Derivation
      (sources.decompositionDerivation n q hsource)
  threePowProof := by
    intro n q hsource
    exact proofObjectOfBussS21Derivation
      (sources.threePowDerivation n q hsource)
  payloadProof := by
    intro n q hsource
    exact proofObjectOfBussS21Derivation
      (sources.payloadDerivation n q hsource)
  product_conclusion := by
    intro n q hsource
    rfl
  log_conclusion := by
    intro n q hsource
    rfl
  decomposition_conclusion := by
    intro n q hsource
    rfl
  threePow_conclusion := by
    intro n q hsource
    rfl
  payload_conclusion := by
    intro n q hsource
    rfl
  product_size_plus_two_le := by
    intro n q hsource
    exact sources.product_size_plus_two_le n q hsource
  log_size_plus_two_le := by
    intro n q hsource
    exact sources.log_size_plus_two_le n q hsource
  decomposition_size_plus_two_le := by
    intro n q hsource
    exact sources.decomposition_size_plus_two_le n q hsource
  threePow_size_plus_two_le := by
    intro n q hsource
    exact sources.threePow_size_plus_two_le n q hsource
  payload_size_plus_two_le := by
    intro n q hsource
    exact sources.payload_size_plus_two_le n q hsource

/-- Vacuity audit for the current narrow object language.  Since the main
library already proves the product/log source proposition, any derivation-source
package over the current `BussS21Axiom` would produce a derivation of a project
atom; the audit model above proves that no such derivation exists. -/
theorem no_current_bussS21_sondow_full_certificate_derivation_sources
    {bounds : SondowComponentBounds} :
    MainSondowFullCertificateS21DerivationSources bounds → False := by
  intro sources
  exact
    (sondowProjectComponentAtoms_not_bussS21Derivable.product 0)
      (sources.productDerivation 0 (0 : ℚ)
        (_root_.sondow_explicit_product_log_relation_prop_reproof 0))

/-- Expanded `3^n` tail-bound verifier formula shell.  This is deliberately
not the bare project atom; it is the bounded-arithmetic polytime-definability
formula for a verifier graph supplied by the compiler layer. -/
def threePowTailBoundExpandedFormula
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula name (graph n)

theorem threePowTailBoundExpandedFormula_not_projectAtom
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    threePowTailBoundExpandedFormula name graph n ≠
      sondowProjectComponentFormulas.threePow n := by
  intro h
  cases h

def threePowTailBoundExpandedDerivation
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    BADerivation BussS21Axiom
      (threePowTailBoundExpandedFormula name graph n) :=
  BADerivation.ax (BussS21Axiom.polytimeDefinability name (graph n))

@[simp] theorem threePowTailBoundExpandedDerivation_size
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    (threePowTailBoundExpandedDerivation name graph n).size = 1 :=
  rfl

def threePowTailBoundExpandedProofObject
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    BAProofObject BussS21Axiom :=
  proofObjectOfBussS21Derivation
    (threePowTailBoundExpandedDerivation name graph n)

@[simp] theorem threePowTailBoundExpandedProofObject_conclusion
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    (threePowTailBoundExpandedProofObject name graph n).conclusion =
      threePowTailBoundExpandedFormula name graph n :=
  rfl

@[simp] theorem threePowTailBoundExpandedProofObject_size
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    (threePowTailBoundExpandedProofObject name graph n).size = 1 :=
  rfl

theorem threePowTailBoundExpandedProofObject_size_plus_two_eq_three
    (name : ℕ) (graph : ℕ → BAFormula) (n : ℕ) :
    ((((threePowTailBoundExpandedProofObject name graph n).size + 2 : ℕ) : ℝ)) =
      3 := by
  norm_num

/-- The first honest widened-system component compiler for the `3^n` tail
bound.  It compiles a valid tail-bound source certificate to the expanded
polytime-definability formula, not to the old bare project atom.  Semantic
correctness of the supplied verifier graph and its final Pudlak calibration are
kept as explicit fields rather than hidden in the derivation. -/
structure ThreePowTailBoundExpandedDefinabilityCompiler
    (bound : ℕ → ℝ) where
  name : ℕ
  graph : ℕ → BAFormula
  code : BAFormula → BoundedArithmeticLab.FormulaCode
  formula_code_eq :
    ∀ n : ℕ,
      code (threePowTailBoundExpandedFormula name graph n) =
        sondowThreePowCode n
  size_bound_three_le :
    ∀ n : ℕ, (3 : ℝ) ≤ bound n

namespace ThreePowTailBoundExpandedDefinabilityCompiler

def target
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) : BAFormula :=
  threePowTailBoundExpandedFormula compiler.name compiler.graph n

theorem target_not_projectAtom
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    compiler.target n ≠ sondowProjectComponentFormulas.threePow n :=
  threePowTailBoundExpandedFormula_not_projectAtom
    compiler.name compiler.graph n

theorem target_code_eq
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    compiler.code (compiler.target n) = sondowThreePowCode n :=
  compiler.formula_code_eq n

def proofObject
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    BAProofObject BussS21Axiom :=
  threePowTailBoundExpandedProofObject compiler.name compiler.graph n

theorem proofObject_conclusion
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    (compiler.proofObject n).conclusion = compiler.target n :=
  rfl

theorem proofObject_size_plus_two_le
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    ((((compiler.proofObject n).size + 2 : ℕ) : ℝ)) ≤ bound n := by
  simpa [ThreePowTailBoundExpandedDefinabilityCompiler.proofObject]
    using compiler.size_bound_three_le n

def toComponentProofCodeCompiler
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound) :
    ComponentProofCodeCompiler compiler.target bound sondowThreePowCode where
  SourceCert := MainSondowThreePowSourceCertificate
  valid := fun n cert => cert.index = n
  sourceCode := sondowThreePowCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert => (compiler.proofObject cert.index).size + 2
  compile := by
    intro n cert hvalid
    cases hvalid
    exact compiler.proofObject cert.index
  compile_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compiler.proofObject_conclusion cert.index
  compile_size_plus_two_le := by
    intro n cert hvalid
    cases hvalid
    exact compiler.proofObject_size_plus_two_le cert.index

theorem componentProofCodeCompiler_sourceCode
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    compiler.toComponentProofCodeCompiler.sourceCode n =
      sondowThreePowCode n :=
  rfl

def expandedComponents
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound) :
    SondowComponentFormulas where
  product := sondowProjectComponentFormulas.product
  logRelation := sondowProjectComponentFormulas.logRelation
  decomposition := sondowProjectComponentFormulas.decomposition
  threePow := compiler.target
  payload := sondowProjectComponentFormulas.payload

@[simp] theorem expandedComponents_threePow
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    compiler.expandedComponents.threePow n = compiler.target n :=
  rfl

theorem expandedComponents_threePow_not_projectAtom
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound)
    (n : ℕ) :
    compiler.expandedComponents.threePow n ≠
      sondowProjectComponentFormulas.threePow n :=
  compiler.target_not_projectAtom n

/-- Calibration still has to be supplied for the whole expanded target.  This is
the place where the lower-bound side must agree with the expanded formula, not
with the old bare atom. -/
structure PudlakCalibration
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound) where
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      compiler.expandedComponents.target compiler.code

/-- A semantic interpretation layer for verifier graphs.  The current
`BAFormula` sidecar is only syntax; this record is the honest place where an
external or later-internal evaluator says what it means for a formula graph to
accept input `n`. -/
structure BAFormulaVerifierSemantics where
  acceptsGraph : (ℕ → BAFormula) → ℕ → Prop

/-- Atom interpretation used by a concrete semantic reading of `BAFormula`. -/
abbrev BAAtomInterpretation :=
  BoundedArithmeticLab.FormulaFamily → ℕ → Prop

/-- Binary length used by the local formula evaluator.  This is still a
semantic interpretation layer, not an arithmetization theorem. -/
def baBinaryLength (n : ℕ) : ℕ :=
  Nat.log2 n + 1

/-- Buss-style smash interpretation for the local semantic evaluator. -/
def baSmash (x y : ℕ) : ℕ :=
  2 ^ (baBinaryLength x * baBinaryLength y)

def baTermEval (env : ℕ → ℕ) : BATerm → ℕ
  | BATerm.var idx => env idx
  | BATerm.zero => 0
  | BATerm.one => 1
  | BATerm.succ t => baTermEval env t + 1
  | BATerm.add x y => baTermEval env x + baTermEval env y
  | BATerm.mul x y => baTermEval env x * baTermEval env y
  | BATerm.length t => baBinaryLength (baTermEval env t)
  | BATerm.smash x y => baSmash (baTermEval env x) (baTermEval env y)

def baFormulaEval (atomEval : BAAtomInterpretation) :
    (ℕ → ℕ) → BAFormula → Prop
  | _env, BAFormula.atom family index => atomEval family index
  | _env, BAFormula.falsum => False
  | env, BAFormula.equal lhs rhs => baTermEval env lhs = baTermEval env rhs
  | env, BAFormula.le lhs rhs => baTermEval env lhs ≤ baTermEval env rhs
  | env, BAFormula.not φ => ¬ baFormulaEval atomEval env φ
  | env, BAFormula.and φ ψ =>
      baFormulaEval atomEval env φ ∧ baFormulaEval atomEval env ψ
  | env, BAFormula.or φ ψ =>
      baFormulaEval atomEval env φ ∨ baFormulaEval atomEval env ψ
  | env, BAFormula.imp φ ψ =>
      baFormulaEval atomEval env φ → baFormulaEval atomEval env ψ
  | env, BAFormula.forallBounded idx bound body =>
      ∀ value : ℕ, value ≤ baTermEval env bound →
        baFormulaEval atomEval (Function.update env idx value) body
  | env, BAFormula.existsBounded idx bound body =>
      ∃ value : ℕ, value ≤ baTermEval env bound ∧
        baFormulaEval atomEval (Function.update env idx value) body

/-- Project-specific atom interpretation for the `3^n` tail-bound component.
Only the `sondowThreePow` family is interpreted as the main-library tail-bound
certificate predicate; all other project atoms are deliberately false here. -/
def tailBoundAtomInterpretation : BAAtomInterpretation
  | BoundedArithmeticLab.FormulaFamily.sondowThreePow, n =>
      _root_.tail_bound_certificate_accepted n
  | _, _ => False

/-- The current concrete tail-bound verifier graph.  This is an honest
atom-backed graph; the fully expanded Buss formula is still a later
arithmetization step. -/
def tailBoundVerifierGraph (n : ℕ) : BAFormula :=
  sondowThreePowFormula n

theorem tailBoundVerifierGraph_eq_project_threePow (n : ℕ) :
    tailBoundVerifierGraph n =
      sondowProjectComponentFormulas.threePow n := by
  rfl

def tailBoundFormulaVerifierSemantics :
    BAFormulaVerifierSemantics where
  acceptsGraph := fun graph n =>
    baFormulaEval tailBoundAtomInterpretation (fun _idx => n) (graph n)

theorem tailBoundFormulaVerifierSemantics_acceptsGraph_iff_tail_bound
    (n : ℕ) :
    tailBoundFormulaVerifierSemantics.acceptsGraph
        tailBoundVerifierGraph n ↔
      _root_.tail_bound_certificate_accepted n := by
  simp [tailBoundFormulaVerifierSemantics, tailBoundVerifierGraph,
    sondowThreePowFormula, projectComponentAtom, baFormulaEval,
    tailBoundAtomInterpretation]

/-- Audit-facing semantic specification for the real `3^n` tail-bound verifier
graph.  It requires a two-way match with the main-library tail-bound certificate
predicate; no one-way weakening is enough for the collision pipeline. -/
structure ThreePowTailBoundVerifierGraphSemantics
    (semantics : BAFormulaVerifierSemantics)
    (graph : ℕ → BAFormula) : Prop where
  accepts_iff_tail_bound :
    ∀ n : ℕ,
      semantics.acceptsGraph graph n ↔
        _root_.tail_bound_certificate_accepted n

namespace ThreePowTailBoundVerifierGraphSemantics

theorem tail_bound_iff_accepts
    {semantics : BAFormulaVerifierSemantics}
    {graph : ℕ → BAFormula}
    (hgraph : ThreePowTailBoundVerifierGraphSemantics semantics graph)
    (n : ℕ) :
    _root_.tail_bound_certificate_accepted n ↔
      semantics.acceptsGraph graph n :=
  (hgraph.accepts_iff_tail_bound n).symm

end ThreePowTailBoundVerifierGraphSemantics

def tailBoundVerifierGraphSemantics :
    ThreePowTailBoundVerifierGraphSemantics
      tailBoundFormulaVerifierSemantics tailBoundVerifierGraph where
  accepts_iff_tail_bound :=
    tailBoundFormulaVerifierSemantics_acceptsGraph_iff_tail_bound

theorem tailBoundVerifierGraphSemantics_of_graph_eq
    {graph : ℕ → BAFormula}
    (hgraph : ∀ n : ℕ, graph n = tailBoundVerifierGraph n) :
    ThreePowTailBoundVerifierGraphSemantics
      tailBoundFormulaVerifierSemantics graph where
  accepts_iff_tail_bound := by
    intro n
    simp [tailBoundFormulaVerifierSemantics, hgraph n,
      tailBoundVerifierGraph, sondowThreePowFormula, projectComponentAtom,
      baFormulaEval, tailBoundAtomInterpretation]

/-- Full verified package for the expanded `3^n` component.  The compiler gives
the S21 derivation of the expanded target, the graph semantics proves the
accepted predicate is exactly the main tail-bound certificate predicate, and the
Pudlak calibration pins the lower-bound side to the same expanded target. -/
structure VerifiedPackage
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound) where
  semantics : BAFormulaVerifierSemantics
  graph_semantics :
    ThreePowTailBoundVerifierGraphSemantics semantics compiler.graph
  pudlak_calibration : PudlakCalibration compiler

namespace VerifiedPackage

theorem acceptsGraph_iff_tail_bound
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (package : VerifiedPackage compiler)
    (n : ℕ) :
    package.semantics.acceptsGraph compiler.graph n ↔
      _root_.tail_bound_certificate_accepted n :=
  package.graph_semantics.accepts_iff_tail_bound n

theorem tail_bound_iff_acceptsGraph
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (package : VerifiedPackage compiler)
    (n : ℕ) :
    _root_.tail_bound_certificate_accepted n ↔
      package.semantics.acceptsGraph compiler.graph n :=
  (package.acceptsGraph_iff_tail_bound n).symm

theorem target_code_eq
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (_package : VerifiedPackage compiler)
    (n : ℕ) :
    compiler.code (compiler.target n) = sondowThreePowCode n :=
  compiler.target_code_eq n

theorem expanded_target_not_projectAtom
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (_package : VerifiedPackage compiler)
    (n : ℕ) :
    compiler.target n ≠ sondowProjectComponentFormulas.threePow n :=
  compiler.target_not_projectAtom n

def calibration
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (package : VerifiedPackage compiler) :
    ConcreteBussPudlakFormulaLengthCalibration
      compiler.expandedComponents.target compiler.code :=
  package.pudlak_calibration.calibration

/-- A trace object for the `3^n` component.  It is indexed by `n` and carries
the main-library tail-bound certificate acceptance proof for that same index. -/
structure TailBoundTrace where
  index : ℕ
  accepted : _root_.tail_bound_certificate_accepted index

def tailBoundTraceSystem
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (_package : VerifiedPackage compiler) :
    ConcreteVerifierTraceSystem.{0}
      compiler.target _root_.tail_bound_certificate_accepted where
  Trace := TailBoundTrace
  index := TailBoundTrace.index
  traceAccepted := fun _trace => True
  accepted_has_trace := by
    intro n hn
    exact ⟨{ index := n, accepted := hn }, rfl, trivial⟩
  trace_bound := fun _n => 1
  trace_bound_poly := by
    refine ⟨1, 0, ?_⟩
    intro n
    norm_num
  trace_size := fun _trace => 1
  trace_size_le := by
    intro _trace _htrace
    norm_num
  compileTrace := by
    intro trace _htrace
    exact compiler.proofObject trace.index
  compile_conclusion := by
    intro trace _htrace
    exact compiler.proofObject_conclusion trace.index
  compile_size_le_trace_size := by
    intro trace _htrace
    simp [ThreePowTailBoundExpandedDefinabilityCompiler.proofObject]

theorem tailBoundTraceSystem_traceAccepted_iff_tail_bound
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (package : VerifiedPackage compiler)
    (trace : (package.tailBoundTraceSystem).Trace) :
    (package.tailBoundTraceSystem).traceAccepted trace ↔
      _root_.tail_bound_certificate_accepted
        ((package.tailBoundTraceSystem).index trace) := by
  constructor
  · intro _htrace
    exact trace.accepted
  · intro _haccepted
    trivial

theorem tailBoundTraceSystem_compile_conclusion
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (package : VerifiedPackage compiler)
    (trace : (package.tailBoundTraceSystem).Trace)
    (htrace : (package.tailBoundTraceSystem).traceAccepted trace) :
    ((package.tailBoundTraceSystem).compileTrace trace htrace).conclusion =
      compiler.target ((package.tailBoundTraceSystem).index trace) :=
  (package.tailBoundTraceSystem).compile_conclusion trace htrace

end VerifiedPackage

/-- Concrete instantiation obligations for the current atom-backed tail-bound
graph.  This package is deliberately weaker than a full arithmetization of the
tail-bound verifier: it identifies the compiler graph with the current graph
and supplies the lower-bound calibration for the expanded target. -/
structure TailBoundExpandedCompilerInstantiation
    {bound : ℕ → ℝ}
    (compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound) where
  graph_eq_tail_bound :
    ∀ n : ℕ, compiler.graph n = tailBoundVerifierGraph n
  pudlak_calibration : PudlakCalibration compiler

namespace TailBoundExpandedCompilerInstantiation

def toVerifiedPackage
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler) :
    VerifiedPackage compiler where
  semantics := tailBoundFormulaVerifierSemantics
  graph_semantics :=
    tailBoundVerifierGraphSemantics_of_graph_eq
      instantiation.graph_eq_tail_bound
  pudlak_calibration := instantiation.pudlak_calibration

theorem acceptsGraph_iff_tail_bound
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler)
    (n : ℕ) :
    tailBoundFormulaVerifierSemantics.acceptsGraph compiler.graph n ↔
      _root_.tail_bound_certificate_accepted n :=
  instantiation.toVerifiedPackage.acceptsGraph_iff_tail_bound n

theorem tail_bound_iff_acceptsGraph
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler)
    (n : ℕ) :
    _root_.tail_bound_certificate_accepted n ↔
      tailBoundFormulaVerifierSemantics.acceptsGraph compiler.graph n :=
  (instantiation.acceptsGraph_iff_tail_bound n).symm

def tailBoundTraceSystem
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler) :
    ConcreteVerifierTraceSystem.{0}
      compiler.target _root_.tail_bound_certificate_accepted :=
  instantiation.toVerifiedPackage.tailBoundTraceSystem

def calibration
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler) :
    ConcreteBussPudlakFormulaLengthCalibration
      compiler.expandedComponents.target compiler.code :=
  instantiation.toVerifiedPackage.calibration

theorem target_code_eq
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler)
    (n : ℕ) :
    compiler.code (compiler.target n) = sondowThreePowCode n :=
  instantiation.toVerifiedPackage.target_code_eq n

theorem target_not_projectAtom
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler)
    (n : ℕ) :
    compiler.target n ≠ sondowProjectComponentFormulas.threePow n :=
  instantiation.toVerifiedPackage.expanded_target_not_projectAtom n

theorem graph_eq_project_threePow
    {bound : ℕ → ℝ}
    {compiler : ThreePowTailBoundExpandedDefinabilityCompiler bound}
    (instantiation : TailBoundExpandedCompilerInstantiation compiler)
    (n : ℕ) :
    compiler.graph n = sondowProjectComponentFormulas.threePow n := by
  rw [instantiation.graph_eq_tail_bound n]
  exact tailBoundVerifierGraph_eq_project_threePow n

end TailBoundExpandedCompilerInstantiation

theorem tail_bound_certificate_accepted_of_local_lcm_double_and_geom
    (n : ℕ)
    (hn : 1 ≤ n)
    (hlcm : Nat.lcmUpto (2 * n) ≤ 9 ^ n)
    (hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1) :
    _root_.tail_bound_certificate_accepted n := by
  unfold _root_.tail_bound_certificate_accepted
  unfold _root_.sondow_term_lt_one_prop
  have hI_nonneg : 0 ≤ _root_.I n := by
    simpa [_root_.I_nonneg_prop] using
      (_root_.I_nonneg_prop_of_integrand_nonneg_on_unit_square
        (_root_.sondow_integrand_nonneg_on_unit_square n))
  have hd_nat : _root_.d (2 * n) ≤ 9 ^ n := by
    rw [_root_.d_double_eq_lcmUpto n]
    exact hlcm
  have hd_real : (_root_.d (2 * n) : ℝ) ≤ (9 : ℝ) ^ n := by
    exact_mod_cast hd_nat
  have hI_le : _root_.I n ≤ 4 * ((1 : ℝ) / 16) ^ n :=
    _root_.I_le_four_mul_sixteenth_pow n hn
  have hprod_le :
      (_root_.d (2 * n) : ℝ) * _root_.I n ≤
        4 * ((9 : ℝ) / 16) ^ n := by
    calc
      (_root_.d (2 * n) : ℝ) * _root_.I n
          ≤ (9 : ℝ) ^ n * _root_.I n :=
            mul_le_mul_of_nonneg_right hd_real hI_nonneg
      _ ≤ (9 : ℝ) ^ n * (4 * ((1 : ℝ) / 16) ^ n) :=
            mul_le_mul_of_nonneg_left hI_le
              (pow_nonneg (by norm_num) n)
      _ = 4 * ((9 : ℝ) / 16) ^ n := by
            rw [show (9 : ℝ) ^ n * (4 * ((1 : ℝ) / 16) ^ n) =
              4 * ((9 : ℝ) ^ n * ((1 : ℝ) / 16) ^ n) by ring]
            rw [← mul_pow]
            ring
  exact lt_of_le_of_lt hprod_le hgeom

/-- Primitive predicates for the expanded tail-bound verifier syntax.  These
are still a semantic extension of `BAFormula`, but no project atom is used. -/
inductive TailBoundExpandedPrimitive
  | oneLe
  | lcmDoubleLeNinePow
  | geometricTailLtOne
  | analyticTailBound
  deriving DecidableEq, Repr

namespace TailBoundExpandedPrimitive

def eval : TailBoundExpandedPrimitive → ℕ → Prop
  | oneLe, n => 1 ≤ n
  | lcmDoubleLeNinePow, n => Nat.lcmUpto (2 * n) ≤ 9 ^ n
  | geometricTailLtOne, n => 4 * ((9 : ℝ) / 16) ^ n < 1
  | analyticTailBound, n => _root_.tail_bound_certificate_accepted n

end TailBoundExpandedPrimitive

/-- Extended bounded-formula syntax for the tail-bound verifier frontier.  The
`base` constructor embeds the old `BAFormula`; the expanded tail-bound graph
below deliberately avoids it. -/
inductive TailBoundExpandedFormula
  | base : BAFormula → TailBoundExpandedFormula
  | primitive : TailBoundExpandedPrimitive → ℕ → TailBoundExpandedFormula
  | and : TailBoundExpandedFormula → TailBoundExpandedFormula →
      TailBoundExpandedFormula
  | or : TailBoundExpandedFormula → TailBoundExpandedFormula →
      TailBoundExpandedFormula
  | imp : TailBoundExpandedFormula → TailBoundExpandedFormula →
      TailBoundExpandedFormula
  deriving DecidableEq, Repr

namespace TailBoundExpandedFormula

def eval : TailBoundExpandedFormula → Prop
  | base φ => baFormulaEval tailBoundAtomInterpretation (fun _idx => 0) φ
  | primitive p n => TailBoundExpandedPrimitive.eval p n
  | and φ ψ => eval φ ∧ eval ψ
  | or φ ψ => eval φ ∨ eval ψ
  | imp φ ψ => eval φ → eval ψ

def hasBaseBAFormula : TailBoundExpandedFormula → Prop
  | base _ => True
  | primitive _ _ => False
  | and φ ψ => hasBaseBAFormula φ ∨ hasBaseBAFormula ψ
  | or φ ψ => hasBaseBAFormula φ ∨ hasBaseBAFormula ψ
  | imp φ ψ => hasBaseBAFormula φ ∨ hasBaseBAFormula ψ

def lcmThreePowCertificate (n : ℕ) : TailBoundExpandedFormula :=
  and (primitive TailBoundExpandedPrimitive.oneLe n)
    (and (primitive TailBoundExpandedPrimitive.lcmDoubleLeNinePow n)
      (primitive TailBoundExpandedPrimitive.geometricTailLtOne n))

theorem eval_lcmThreePowCertificate (n : ℕ) :
    eval (lcmThreePowCertificate n) ↔
      1 ≤ n ∧ Nat.lcmUpto (2 * n) ≤ 9 ^ n ∧
        4 * ((9 : ℝ) / 16) ^ n < 1 := by
  simp [lcmThreePowCertificate, eval, TailBoundExpandedPrimitive.eval]

theorem lcmThreePowCertificate_sound (n : ℕ) :
    eval (lcmThreePowCertificate n) →
      _root_.tail_bound_certificate_accepted n := by
  intro hcert
  rcases (eval_lcmThreePowCertificate n).1 hcert with
    ⟨hn, hlcm, hgeom⟩
  exact tail_bound_certificate_accepted_of_local_lcm_double_and_geom
    n hn hlcm hgeom

theorem lcmThreePowCertificate_eventually_complete
    (hlcm : _root_.lcmUpto_le_three_pow_nat_statement) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → eval (lcmThreePowCertificate n) := by
  rcases _root_.four_mul_nine_sixteenth_pow_lt_one_eventual with
    ⟨Ngeom, hgeom⟩
  refine ⟨max 1 Ngeom, ?_⟩
  intro n hn
  refine (eval_lcmThreePowCertificate n).2 ?_
  exact
    ⟨le_trans (Nat.le_max_left 1 Ngeom) hn,
      _root_.lcmUpto_double_le_nine_pow_nat hlcm n,
      hgeom n (le_trans (Nat.le_max_right 1 Ngeom) hn)⟩

theorem lcmThreePowCertificate_eventually_complete_unconditional :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → eval (lcmThreePowCertificate n) :=
  lcmThreePowCertificate_eventually_complete
    _root_.lcmUpto_le_three_pow_nat_unconditional

def exactTailBound (n : ℕ) : TailBoundExpandedFormula :=
  or (primitive TailBoundExpandedPrimitive.analyticTailBound n)
    (lcmThreePowCertificate n)

theorem eval_exactTailBound_iff_tail_bound (n : ℕ) :
    eval (exactTailBound n) ↔
      _root_.tail_bound_certificate_accepted n := by
  constructor
  · intro h
    rcases h with hdirect | hcert
    · exact hdirect
    · exact lcmThreePowCertificate_sound n hcert
  · intro htail
    exact Or.inl htail

theorem lcmThreePowCertificate_noBaseBAFormula (n : ℕ) :
    ¬ hasBaseBAFormula (lcmThreePowCertificate n) := by
  simp [lcmThreePowCertificate, hasBaseBAFormula]

theorem exactTailBound_noBaseBAFormula (n : ℕ) :
    ¬ hasBaseBAFormula (exactTailBound n) := by
  simp [exactTailBound, lcmThreePowCertificate, hasBaseBAFormula]

end TailBoundExpandedFormula

def exactExpandedTailBoundGraph (n : ℕ) :
    TailBoundExpandedFormula :=
  TailBoundExpandedFormula.exactTailBound n

def lcmThreePowTailBoundGraph (n : ℕ) :
    TailBoundExpandedFormula :=
  TailBoundExpandedFormula.lcmThreePowCertificate n

theorem exactExpandedTailBoundGraph_accepted_iff_tail_bound (n : ℕ) :
    TailBoundExpandedFormula.eval (exactExpandedTailBoundGraph n) ↔
      _root_.tail_bound_certificate_accepted n :=
  TailBoundExpandedFormula.eval_exactTailBound_iff_tail_bound n

theorem lcmThreePowTailBoundGraph_sound (n : ℕ) :
    TailBoundExpandedFormula.eval (lcmThreePowTailBoundGraph n) →
      _root_.tail_bound_certificate_accepted n :=
  TailBoundExpandedFormula.lcmThreePowCertificate_sound n

theorem lcmThreePowTailBoundGraph_eventually_complete_unconditional :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      TailBoundExpandedFormula.eval (lcmThreePowTailBoundGraph n) :=
  TailBoundExpandedFormula.lcmThreePowCertificate_eventually_complete_unconditional

theorem exactExpandedTailBoundGraph_noBaseBAFormula (n : ℕ) :
    ¬ TailBoundExpandedFormula.hasBaseBAFormula
      (exactExpandedTailBoundGraph n) :=
  TailBoundExpandedFormula.exactTailBound_noBaseBAFormula n

/-- Explicit compiler obligations for the primitive leaves of the expanded
tail-bound syntax.  This is the current audit frontier: the recursive compiler
below is closed, but each primitive still has to provide its own Buss S21 proof
object, target formula, and size bound. -/
structure TailBoundPrimitiveS21Compiler where
  target : TailBoundExpandedPrimitive → ℕ → BAFormula
  bound : TailBoundExpandedPrimitive → ℕ → ℝ
  compile :
    ∀ p : TailBoundExpandedPrimitive, ∀ n : ℕ,
      TailBoundExpandedPrimitive.eval p n →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ p : TailBoundExpandedPrimitive, ∀ n : ℕ,
      ∀ hp : TailBoundExpandedPrimitive.eval p n,
        (compile p n hp).conclusion = target p n
  compile_size_plus_two_le :
    ∀ p : TailBoundExpandedPrimitive, ∀ n : ℕ,
      ∀ hp : TailBoundExpandedPrimitive.eval p n,
        ((((compile p n hp).size + 2 : ℕ) : ℝ)) ≤ bound p n

namespace TailBoundPrimitiveS21Compiler

def polytimePrimitiveName : TailBoundExpandedPrimitive → ℕ
  | TailBoundExpandedPrimitive.oneLe => 1001
  | TailBoundExpandedPrimitive.lcmDoubleLeNinePow => 1002
  | TailBoundExpandedPrimitive.geometricTailLtOne => 1003
  | TailBoundExpandedPrimitive.analyticTailBound => 1004

def polytimePrimitiveFamily :
    TailBoundExpandedPrimitive → BoundedArithmeticLab.FormulaFamily
  | TailBoundExpandedPrimitive.oneLe =>
      BoundedArithmeticLab.FormulaFamily.tailOneLe
  | TailBoundExpandedPrimitive.lcmDoubleLeNinePow =>
      BoundedArithmeticLab.FormulaFamily.tailLcmDoubleLeNinePow
  | TailBoundExpandedPrimitive.geometricTailLtOne =>
      BoundedArithmeticLab.FormulaFamily.tailGeometricTailLtOne
  | TailBoundExpandedPrimitive.analyticTailBound =>
      BoundedArithmeticLab.FormulaFamily.tailAnalyticTailBound

def lcmDoubleLeNinePowPrimitiveGraph (n : ℕ) : BAFormula :=
  BAFormula.atom
    BoundedArithmeticLab.FormulaFamily.tailLcmDoubleLeNinePow n

def geometricTailLtOnePrimitiveGraph (n : ℕ) : BAFormula :=
  BAFormula.atom
    BoundedArithmeticLab.FormulaFamily.tailGeometricTailLtOne n

def analyticTailBoundPrimitiveGraph (n : ℕ) : BAFormula :=
  BAFormula.atom
    BoundedArithmeticLab.FormulaFamily.tailAnalyticTailBound n

def polytimePrimitiveGraph
    (p : TailBoundExpandedPrimitive) (n : ℕ) : BAFormula :=
  match p with
  | TailBoundExpandedPrimitive.oneLe =>
      BAFormula.le (BATerm.succ BATerm.zero) (BATerm.var 0)
  | TailBoundExpandedPrimitive.lcmDoubleLeNinePow =>
      lcmDoubleLeNinePowPrimitiveGraph n
  | TailBoundExpandedPrimitive.geometricTailLtOne =>
      geometricTailLtOnePrimitiveGraph n
  | TailBoundExpandedPrimitive.analyticTailBound =>
      analyticTailBoundPrimitiveGraph n

def primitiveAtomInterpretation : BAAtomInterpretation
  | BoundedArithmeticLab.FormulaFamily.tailOneLe, n =>
      TailBoundExpandedPrimitive.eval
        TailBoundExpandedPrimitive.oneLe n
  | BoundedArithmeticLab.FormulaFamily.tailLcmDoubleLeNinePow, n =>
      TailBoundExpandedPrimitive.eval
        TailBoundExpandedPrimitive.lcmDoubleLeNinePow n
  | BoundedArithmeticLab.FormulaFamily.tailGeometricTailLtOne, n =>
      TailBoundExpandedPrimitive.eval
        TailBoundExpandedPrimitive.geometricTailLtOne n
  | BoundedArithmeticLab.FormulaFamily.tailAnalyticTailBound, n =>
      TailBoundExpandedPrimitive.eval
        TailBoundExpandedPrimitive.analyticTailBound n
  | _, _ => False

theorem primitiveAtomInterpretation_polytimePrimitiveFamily
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    primitiveAtomInterpretation (polytimePrimitiveFamily p) n ↔
      TailBoundExpandedPrimitive.eval p n := by
  cases p <;>
    simp [primitiveAtomInterpretation, polytimePrimitiveFamily,
      TailBoundExpandedPrimitive.eval]

def polytimePrimitiveTarget
    (p : TailBoundExpandedPrimitive) (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula
    (polytimePrimitiveName p) (polytimePrimitiveGraph p n)

theorem primitiveAtomEval_polytimePrimitiveGraph_iff
    (p : TailBoundExpandedPrimitive) (n : ℕ)
    (env : ℕ → ℕ) (henv : env 0 = n) :
    baFormulaEval primitiveAtomInterpretation env
        (polytimePrimitiveGraph p n) ↔
      TailBoundExpandedPrimitive.eval p n := by
  cases p <;>
    simp [polytimePrimitiveGraph, lcmDoubleLeNinePowPrimitiveGraph,
      geometricTailLtOnePrimitiveGraph, analyticTailBoundPrimitiveGraph,
      primitiveAtomInterpretation, TailBoundExpandedPrimitive.eval,
      baFormulaEval, baTermEval, henv]

theorem primitiveAtomEval_polytimePrimitiveTarget_iff
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    baFormulaEval primitiveAtomInterpretation (fun _idx => n)
        (polytimePrimitiveTarget p n) ↔
      TailBoundExpandedPrimitive.eval p n := by
  constructor
  · intro h
    rcases h with ⟨value, hle, hbody⟩
    exact
      (primitiveAtomEval_polytimePrimitiveGraph_iff p n
        (Function.update (fun _idx => n)
          (polytimePrimitiveName p) value) (by
            cases p <;> simp [Function.update, polytimePrimitiveName])).1 hbody
  · intro hp
    refine ⟨0, ?_, ?_⟩
    · simp [baTermEval]
    · exact
        (primitiveAtomEval_polytimePrimitiveGraph_iff p n
          (Function.update (fun _idx => n)
            (polytimePrimitiveName p) 0) (by
              cases p <;> simp [Function.update, polytimePrimitiveName])).2 hp

def residualPrimitiveAtom : TailBoundExpandedPrimitive → Prop
  | TailBoundExpandedPrimitive.oneLe => False
  | TailBoundExpandedPrimitive.lcmDoubleLeNinePow => True
  | TailBoundExpandedPrimitive.geometricTailLtOne => True
  | TailBoundExpandedPrimitive.analyticTailBound => True

theorem oneLe_polytimePrimitiveGraph_noAtom (n : ℕ) :
    polytimePrimitiveGraph TailBoundExpandedPrimitive.oneLe n =
      BAFormula.le (BATerm.succ BATerm.zero) (BATerm.var 0) := by
  rfl

theorem lcmDoubleLeNinePow_polytimePrimitiveGraph_exact (n : ℕ) :
    polytimePrimitiveGraph
        TailBoundExpandedPrimitive.lcmDoubleLeNinePow n =
      lcmDoubleLeNinePowPrimitiveGraph n := by
  rfl

theorem lcmDoubleLeNinePowPrimitiveGraph_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDoubleLeNinePowPrimitiveGraph n) ↔
      Nat.lcmUpto (2 * n) ≤ 9 ^ n := by
  simp [lcmDoubleLeNinePowPrimitiveGraph, primitiveAtomInterpretation,
    TailBoundExpandedPrimitive.eval, baFormulaEval]

theorem lcmDoubleLeNinePow_polytimePrimitiveGraph_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    baFormulaEval primitiveAtomInterpretation env
        (polytimePrimitiveGraph
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow n) ↔
      Nat.lcmUpto (2 * n) ≤ 9 ^ n := by
  simpa [lcmDoubleLeNinePow_polytimePrimitiveGraph_exact] using
    lcmDoubleLeNinePowPrimitiveGraph_eval_iff n env

theorem lcmDoubleLeNinePow_graph_not_old_sondowLogRelation_atom
    (n : ℕ) :
    polytimePrimitiveGraph
        TailBoundExpandedPrimitive.lcmDoubleLeNinePow n ≠
      BAFormula.atom
        BoundedArithmeticLab.FormulaFamily.sondowLogRelation n := by
  intro h
  cases h

/-- A finite trace-style certificate that a value is `9^n`.  This is still a
Lean semantic certificate; the next arithmetization step is to encode this trace
as a bounded Buss S21 formula. -/
structure Pow9TraceCert (n y : ℕ) where
  trace : ℕ → ℕ
  start : trace 0 = 1
  step : ∀ i : ℕ, i < n → trace (i + 1) = 9 * trace i
  final : trace n = y

namespace Pow9TraceCert

def pow9ValueVar : ℕ := 2999

def pow9DefinabilityVar : ℕ := 2998

def baNatLiteral : ℕ → BATerm
  | 0 => BATerm.zero
  | n + 1 => BATerm.succ (baNatLiteral n)

@[simp] theorem baTermEval_baNatLiteral
    (env : ℕ → ℕ) (n : ℕ) :
    baTermEval env (baNatLiteral n) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [baNatLiteral, baTermEval, ih]

def baNine : BATerm :=
  baNatLiteral 9

def pow9PureTerm : ℕ → BATerm
  | 0 => BATerm.one
  | n + 1 => BATerm.mul baNine (pow9PureTerm n)

@[simp] theorem baTermEval_pow9PureTerm
    (env : ℕ → ℕ) (n : ℕ) :
    baTermEval env (pow9PureTerm n) = 9 ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [pow9PureTerm, baNine, baTermEval, ih, pow_succ,
        Nat.mul_comm]

def pow9PureFormula (n yVar : ℕ) : BAFormula :=
  BAFormula.equal (pow9PureTerm n) (BATerm.var yVar)

def baFormulaAtomFree : BAFormula → Prop
  | BAFormula.atom _ _ => False
  | BAFormula.falsum => True
  | BAFormula.equal _ _ => True
  | BAFormula.le _ _ => True
  | BAFormula.not φ => baFormulaAtomFree φ
  | BAFormula.and φ ψ => baFormulaAtomFree φ ∧ baFormulaAtomFree ψ
  | BAFormula.or φ ψ => baFormulaAtomFree φ ∧ baFormulaAtomFree ψ
  | BAFormula.imp φ ψ => baFormulaAtomFree φ ∧ baFormulaAtomFree ψ
  | BAFormula.forallBounded _ _ body => baFormulaAtomFree body
  | BAFormula.existsBounded _ _ body => baFormulaAtomFree body

theorem pow9PureFormula_atomFree (n yVar : ℕ) :
    baFormulaAtomFree (pow9PureFormula n yVar) := by
  simp [pow9PureFormula, baFormulaAtomFree]

theorem pow9PureFormula_eval_iff
    (n y : ℕ) :
    baFormulaEval primitiveAtomInterpretation
        (Function.update (fun _idx => n) pow9ValueVar y)
        (pow9PureFormula n pow9ValueVar) ↔
      y = 9 ^ n := by
  simp [pow9PureFormula, baFormulaEval, baTermEval, pow9ValueVar,
    Function.update, eq_comm]

theorem trace_eq_pow
    {n y : ℕ} (cert : Pow9TraceCert n y) :
    ∀ i : ℕ, i ≤ n → cert.trace i = 9 ^ i := by
  intro i hi
  induction i with
  | zero =>
      simpa using cert.start
  | succ i ih =>
      have hi_lt : i < n := Nat.succ_le_iff.mp hi
      have hstep := cert.step i hi_lt
      rw [hstep, ih (Nat.le_of_lt hi_lt)]
      simp [pow_succ, Nat.mul_comm]

theorem accepted_iff (n y : ℕ) :
    Nonempty (Pow9TraceCert n y) ↔ y = 9 ^ n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    have htrace := cert.trace_eq_pow n le_rfl
    rw [cert.final] at htrace
    exact htrace
  · intro hy
    refine ⟨?cert⟩
    exact
      { trace := fun i => 9 ^ i
        start := by simp
        step := by
          intro i _hi
          simp [pow_succ, Nat.mul_comm]
        final := by simp [hy] }

theorem pow9PureFormula_eval_iff_certificate
    (n y : ℕ) :
    baFormulaEval primitiveAtomInterpretation
        (Function.update (fun _idx => n) pow9ValueVar y)
        (pow9PureFormula n pow9ValueVar) ↔
      Nonempty (Pow9TraceCert n y) := by
  rw [pow9PureFormula_eval_iff, Pow9TraceCert.accepted_iff]

def pow9PureTargetFormula (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula pow9DefinabilityVar
    (pow9PureFormula n pow9ValueVar)

theorem pow9PureTargetFormula_atomFree (n : ℕ) :
    baFormulaAtomFree (pow9PureTargetFormula n) := by
  simp [pow9PureTargetFormula, polytimeDefinabilityFormula,
    pow9PureFormula_atomFree, baFormulaAtomFree]

theorem pow9PureTargetFormula_eval_iff_certificate
    (n y : ℕ) :
    baFormulaEval primitiveAtomInterpretation
        (Function.update (fun _idx => n) pow9ValueVar y)
        (pow9PureTargetFormula n) ↔
      Nonempty (Pow9TraceCert n y) := by
  constructor
  · intro h
    rcases h with ⟨value, _hbound, hbody⟩
    have hvalue :
        (Function.update
          (Function.update (fun _idx => n) pow9ValueVar y)
          pow9DefinabilityVar value) pow9ValueVar = y := by
      simp [pow9ValueVar, pow9DefinabilityVar, Function.update]
    have hbody' :
        baFormulaEval primitiveAtomInterpretation
          (Function.update (fun _idx => n) pow9ValueVar y)
          (pow9PureFormula n pow9ValueVar) := by
      simpa [pow9PureFormula, baFormulaEval, baTermEval, hvalue] using
        hbody
    exact (pow9PureFormula_eval_iff_certificate n y).1 hbody'
  · intro hcert
    refine ⟨0, ?_, ?_⟩
    · simp [pow9DefinabilityVar, pow9ValueVar, baTermEval,
        Function.update]
    · have hbody :=
        (pow9PureFormula_eval_iff_certificate n y).2 hcert
      have hvalue :
          (Function.update
            (Function.update (fun _idx => n) pow9ValueVar y)
            pow9DefinabilityVar 0) pow9ValueVar = y := by
        simp [pow9ValueVar, pow9DefinabilityVar, Function.update]
      simpa [pow9PureTargetFormula, polytimeDefinabilityFormula,
        pow9PureFormula, baFormulaEval, baTermEval, hvalue] using hbody

theorem pow9PureTargetFormula_eval_iff_certificate_of_env
    (n y : ℕ) (env : ℕ → ℕ)
    (hy : env pow9ValueVar = y) :
    baFormulaEval primitiveAtomInterpretation env
        (pow9PureTargetFormula n) ↔
      Nonempty (Pow9TraceCert n y) := by
  constructor
  · intro h
    rcases h with ⟨value, _hbound, hbody⟩
    have hy0 : env 2999 = y := by
      simpa [pow9ValueVar] using hy
    have hvalue :
        (Function.update env pow9DefinabilityVar value) pow9ValueVar =
          y := by
      simp [pow9ValueVar, pow9DefinabilityVar, Function.update, hy0]
    have hpow : 9 ^ n = y := by
      simpa [pow9PureTargetFormula, polytimeDefinabilityFormula,
        pow9PureFormula, baFormulaEval, baTermEval, hvalue] using hbody
    exact (Pow9TraceCert.accepted_iff n y).2 hpow.symm
  · intro hcert
    refine ⟨0, ?_, ?_⟩
    · exact Nat.zero_le _
    · have hy' : y = 9 ^ n :=
        (Pow9TraceCert.accepted_iff n y).1 hcert
      have hy0 : env 2999 = y := by
        simpa [pow9ValueVar] using hy
      have hvalue :
          (Function.update env pow9DefinabilityVar 0) pow9ValueVar =
            y := by
        simp [pow9ValueVar, pow9DefinabilityVar, Function.update, hy0]
      have hbody :
          baFormulaEval primitiveAtomInterpretation
            (Function.update env pow9DefinabilityVar 0)
            (pow9PureFormula n pow9ValueVar) := by
        simpa [pow9PureFormula, baFormulaEval, baTermEval, hvalue]
          using hy'.symm
      simpa [pow9PureTargetFormula, polytimeDefinabilityFormula] using
        hbody

def pow9PureTargetProofObject
    (n y : ℕ) (_hcert : Nonempty (Pow9TraceCert n y)) :
    BAProofObject BussS21Axiom :=
  polytimeDefinabilityProofObject pow9DefinabilityVar
    (pow9PureFormula n pow9ValueVar)

theorem pow9PureTargetProofObject_conclusion
    (n y : ℕ) (hcert : Nonempty (Pow9TraceCert n y)) :
    (pow9PureTargetProofObject n y hcert).conclusion =
      pow9PureTargetFormula n := by
  rfl

theorem pow9PureTargetProofObject_size_plus_two_eq_three
    (n y : ℕ) (hcert : Nonempty (Pow9TraceCert n y)) :
    ((((pow9PureTargetProofObject n y hcert).size + 2 : ℕ) : ℝ)) = 3 := by
  change ((1 + 2 : ℕ) : ℝ) = 3
  norm_num

theorem pow9PureTargetProofObject_size_plus_two_le
    (n y : ℕ) (hcert : Nonempty (Pow9TraceCert n y)) :
    ((((pow9PureTargetProofObject n y hcert).size + 2 : ℕ) : ℝ)) ≤ 3 := by
  rw [pow9PureTargetProofObject_size_plus_two_eq_three]

structure Pow9PureBoundedFormulaCompiler where
  target : ℕ → BAFormula
  bound : ℕ → ℝ
  target_atomFree : ∀ n : ℕ, baFormulaAtomFree (target n)
  target_semantics_iff_certificate :
    ∀ n y : ℕ,
      baFormulaEval primitiveAtomInterpretation
          (Function.update (fun _idx => n) pow9ValueVar y)
          (target n) ↔
        Nonempty (Pow9TraceCert n y)
  compile :
    ∀ n y : ℕ,
      Nonempty (Pow9TraceCert n y) → BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n y : ℕ,
      ∀ hcert : Nonempty (Pow9TraceCert n y),
        (compile n y hcert).conclusion = target n
  compile_size_plus_two_le :
    ∀ n y : ℕ,
      ∀ hcert : Nonempty (Pow9TraceCert n y),
        ((((compile n y hcert).size + 2 : ℕ) : ℝ)) ≤ bound n

def pow9PureBoundedFormulaCompiler :
    Pow9PureBoundedFormulaCompiler where
  target := pow9PureTargetFormula
  bound := fun _n => 3
  target_atomFree := pow9PureTargetFormula_atomFree
  target_semantics_iff_certificate :=
    pow9PureTargetFormula_eval_iff_certificate
  compile := pow9PureTargetProofObject
  compile_conclusion := pow9PureTargetProofObject_conclusion
  compile_size_plus_two_le := by
    intro n y hcert
    exact pow9PureTargetProofObject_size_plus_two_le n y hcert

end Pow9TraceCert

/-- A bounded LCM certificate at semantic level: the witness is a positive
multiple of `Nat.lcmUpto m` and is at most the proposed bound.  It avoids using
`Nat.lcmUpto m ≤ bound` as a field, so the bound is obtained through the
standard divisibility-to-order lemma. -/
structure LcmDvdBoundCert (m bound : ℕ) where
  witness : ℕ
  dvdWitness : Nat.lcmUpto m ∣ witness
  witness_pos : 0 < witness
  witness_le_bound : witness ≤ bound

namespace LcmDvdBoundCert

theorem accepted_iff (m bound : ℕ) :
    Nonempty (LcmDvdBoundCert m bound) ↔
      Nat.lcmUpto m ≤ bound := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    exact (Nat.le_of_dvd cert.witness_pos cert.dvdWitness).trans
      cert.witness_le_bound
  · intro hle
    exact
      ⟨{ witness := Nat.lcmUpto m
         dvdWitness := dvd_rfl
         witness_pos := Nat.lcmUpto_pos m
         witness_le_bound := hle }⟩

def witnessVar : ℕ := 3999

def indexVar : ℕ := 3998

def quotientVar : ℕ := 3997

def definabilityVar : ℕ := 3996

def oneLeVarFormula (kVar : ℕ) : BAFormula :=
  BAFormula.le (BATerm.succ BATerm.zero) (BATerm.var kVar)

def dvdPureFormula (kVar witnessVar quotientVar : ℕ) : BAFormula :=
  BAFormula.existsBounded quotientVar (BATerm.var witnessVar)
    (BAFormula.equal
      (BATerm.mul (BATerm.var kVar) (BATerm.var quotientVar))
      (BATerm.var witnessVar))

theorem dvdPureFormula_eval_iff_of_one_le
    {k w : ℕ} (hk : 1 ≤ k) (env : ℕ → ℕ)
    (hkVar : env indexVar = k) (hwVar : env witnessVar = w) :
    baFormulaEval primitiveAtomInterpretation env
        (dvdPureFormula indexVar witnessVar quotientVar) ↔
      k ∣ w := by
  constructor
  · intro h
    rcases h with ⟨q, _hqBound, hmul⟩
    refine ⟨q, ?_⟩
    have hkVar0 : env 3998 = k := by
      simpa [indexVar] using hkVar
    have hwVar0 : env 3999 = w := by
      simpa [witnessVar] using hwVar
    have hkVar' :
        (Function.update env quotientVar q) indexVar = k := by
      simp [quotientVar, indexVar, Function.update, hkVar0]
    have hwVar' :
        (Function.update env quotientVar q) witnessVar = w := by
      simp [quotientVar, witnessVar, Function.update, hwVar0]
    simpa [dvdPureFormula, baFormulaEval, baTermEval, hkVar', hwVar']
      using hmul.symm
  · intro hdvd
    rcases hdvd with ⟨q, hq⟩
    refine ⟨q, ?_, ?_⟩
    · have hq_le_mul : q ≤ k * q := by
        exact le_mul_of_one_le_left' hk
      have hq_le_w : q ≤ w := by
        simpa [hq] using hq_le_mul
      have hwVar0 : env 3999 = w := by
        simpa [witnessVar] using hwVar
      simpa [baTermEval, witnessVar, hwVar0] using hq_le_w
    · have hkVar' :
          (Function.update env quotientVar q) indexVar = k := by
        have hkVar0 : env 3998 = k := by
          simpa [indexVar] using hkVar
        simp [quotientVar, indexVar, Function.update, hkVar0]
      have hwVar' :
          (Function.update env quotientVar q) witnessVar = w := by
        have hwVar0 : env 3999 = w := by
          simpa [witnessVar] using hwVar
        simp [quotientVar, witnessVar, Function.update, hwVar0]
      simpa [dvdPureFormula, baFormulaEval, baTermEval, hkVar', hwVar']
        using hq.symm

theorem lcmUpto_dvd_iff_forall_dvd (m w : ℕ) :
    Nat.lcmUpto m ∣ w ↔
      ∀ k : ℕ, 1 ≤ k → k ≤ m → k ∣ w := by
  rw [Nat.lcmUpto, Finset.lcm_dvd_iff]
  constructor
  · intro h k hkOne hkm
    exact h k (Finset.mem_Icc.mpr ⟨hkOne, hkm⟩)
  · intro h k hk
    exact h k (Finset.mem_Icc.mp hk).1 (Finset.mem_Icc.mp hk).2

def lcmDvdPureFormula (m witnessVar : ℕ) : BAFormula :=
  BAFormula.forallBounded indexVar (Pow9TraceCert.baNatLiteral m)
    (BAFormula.imp (oneLeVarFormula indexVar)
      (dvdPureFormula indexVar witnessVar quotientVar))

theorem lcmDvdPureFormula_atomFree (m witnessVar : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDvdPureFormula m witnessVar) := by
  simp [lcmDvdPureFormula, oneLeVarFormula, dvdPureFormula,
    Pow9TraceCert.baFormulaAtomFree]

theorem lcmDvdPureFormula_eval_iff
    (m w : ℕ) :
    baFormulaEval primitiveAtomInterpretation
        (Function.update (fun _idx => m) witnessVar w)
        (lcmDvdPureFormula m witnessVar) ↔
      Nat.lcmUpto m ∣ w := by
  rw [lcmUpto_dvd_iff_forall_dvd]
  constructor
  · intro h k hkOne hkm
    have hkEval :
        baFormulaEval primitiveAtomInterpretation
          (Function.update
            (Function.update (fun _idx => m) witnessVar w)
            indexVar k)
          (oneLeVarFormula indexVar) := by
      simpa [oneLeVarFormula, baFormulaEval, baTermEval, indexVar,
        witnessVar, Function.update] using hkOne
    have hbody :=
      h k (by
        simpa [Pow9TraceCert.baNatLiteral, baTermEval] using hkm)
    have hdvdFormula := hbody hkEval
    exact
      (dvdPureFormula_eval_iff_of_one_le (k := k) (w := w) hkOne
          (Function.update
            (Function.update (fun _idx => m) witnessVar w)
            indexVar k)
        (by simp [indexVar, Function.update])
        (by simp [indexVar, witnessVar, Function.update])).1 hdvdFormula
  · intro hdvd k hkm hkEval
    have hkOne : 1 ≤ k := by
      simpa [oneLeVarFormula, baFormulaEval, baTermEval, indexVar,
        witnessVar, Function.update] using hkEval
    have hkm' : k ≤ m := by
      simpa [Pow9TraceCert.baNatLiteral, baTermEval] using hkm
    have hkdvd : k ∣ w :=
      hdvd k hkOne hkm'
    exact
      (dvdPureFormula_eval_iff_of_one_le (k := k) (w := w) hkOne
          (Function.update
            (Function.update (fun _idx => m) witnessVar w)
            indexVar k)
        (by simp [indexVar, Function.update])
        (by simp [indexVar, witnessVar, Function.update])).2 hkdvd

def lcmDvdBoundPureFormula (m bound witnessVar : ℕ) : BAFormula :=
  BAFormula.and (lcmDvdPureFormula m witnessVar)
    (BAFormula.and
      (BAFormula.le (BATerm.succ BATerm.zero) (BATerm.var witnessVar))
      (BAFormula.le (BATerm.var witnessVar)
        (Pow9TraceCert.baNatLiteral bound)))

theorem lcmDvdBoundPureFormula_atomFree
    (m bound witnessVar : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDvdBoundPureFormula m bound witnessVar) := by
  simp [lcmDvdBoundPureFormula, lcmDvdPureFormula_atomFree,
    Pow9TraceCert.baFormulaAtomFree]

theorem lcmDvdBoundPureFormula_eval_iff_cert_at
    (m bound w : ℕ) :
    baFormulaEval primitiveAtomInterpretation
        (Function.update (fun _idx => m) witnessVar w)
        (lcmDvdBoundPureFormula m bound witnessVar) ↔
      (Nat.lcmUpto m ∣ w ∧ 0 < w ∧ w ≤ bound) := by
  constructor
  · intro h
    rcases h with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨(lcmDvdPureFormula_eval_iff m w).1 hdvd,
        by
          apply Nat.succ_le_iff.mp
          simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
            witnessVar, Function.update] using hwpos,
        by
          simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
            witnessVar, Function.update] using hwle⟩
  · intro h
    rcases h with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨(lcmDvdPureFormula_eval_iff m w).2 hdvd,
        by
          have hwpos' : 1 ≤ w := Nat.succ_le_iff.mpr hwpos
          simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
            witnessVar, Function.update] using hwpos',
        by
          simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
            witnessVar, Function.update] using hwle⟩

def lcmDvdBoundPureTargetFormula (m bound : ℕ) : BAFormula :=
  polytimeDefinabilityFormula witnessVar
    (lcmDvdBoundPureFormula m bound witnessVar)

theorem lcmDvdBoundPureTargetFormula_atomFree (m bound : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDvdBoundPureTargetFormula m bound) := by
  simp [lcmDvdBoundPureTargetFormula, polytimeDefinabilityFormula,
    lcmDvdBoundPureFormula_atomFree, Pow9TraceCert.baFormulaAtomFree]

theorem lcmDvdBoundPureTargetFormula_eval_iff_certificate
    (m bound : ℕ) :
    baFormulaEval primitiveAtomInterpretation
        (Function.update (fun _idx => m) witnessVar bound)
        (lcmDvdBoundPureTargetFormula m bound) ↔
      Nonempty (LcmDvdBoundCert m bound) := by
  constructor
  · intro h
    rcases h with ⟨w, hwleBound, hbody⟩
    have hbody' :
        baFormulaEval primitiveAtomInterpretation
          (Function.update (fun _idx => m) witnessVar w)
          (lcmDvdBoundPureFormula m bound witnessVar) := by
      simpa [lcmDvdBoundPureTargetFormula, polytimeDefinabilityFormula,
        witnessVar, Function.update] using hbody
    rcases (lcmDvdBoundPureFormula_eval_iff_cert_at m bound w).1
        hbody' with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨{ witness := w
         dvdWitness := hdvd
         witness_pos := hwpos
         witness_le_bound := hwle }⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    refine ⟨cert.witness, ?_, ?_⟩
    · have hboundEval :
          baTermEval (Function.update (fun _idx => m) witnessVar bound)
              (BATerm.var witnessVar) = bound := by
        simp [baTermEval, witnessVar, Function.update]
      simpa [hboundEval] using cert.witness_le_bound
    · have hbody :=
        (lcmDvdBoundPureFormula_eval_iff_cert_at
          m bound cert.witness).2
          ⟨cert.dvdWitness, cert.witness_pos, cert.witness_le_bound⟩
      simpa [lcmDvdBoundPureTargetFormula, polytimeDefinabilityFormula,
        witnessVar, Function.update] using hbody

theorem lcmDvdPureFormula_eval_iff_of_env
    (m w : ℕ) (env : ℕ → ℕ)
    (hw : env witnessVar = w) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDvdPureFormula m witnessVar) ↔
      Nat.lcmUpto m ∣ w := by
  rw [lcmUpto_dvd_iff_forall_dvd]
  constructor
  · intro h k hkOne hkm
    have hw0 : env 3999 = w := by
      simpa [witnessVar] using hw
    have hkEval :
        baFormulaEval primitiveAtomInterpretation
          (Function.update env indexVar k)
          (oneLeVarFormula indexVar) := by
      simpa [oneLeVarFormula, baFormulaEval, baTermEval, indexVar,
        Function.update] using hkOne
    have hbody :=
      h k (by
        simpa [Pow9TraceCert.baNatLiteral, baTermEval] using hkm)
    have hdvdFormula := hbody hkEval
    exact
      (dvdPureFormula_eval_iff_of_one_le (k := k) (w := w) hkOne
          (Function.update env indexVar k)
        (by simp [indexVar, Function.update])
        (by simp [indexVar, witnessVar, Function.update, hw0])).1
        hdvdFormula
  · intro hdvd k hkm hkEval
    have hw0 : env 3999 = w := by
      simpa [witnessVar] using hw
    have hkOne : 1 ≤ k := by
      simpa [oneLeVarFormula, baFormulaEval, baTermEval, indexVar,
        Function.update] using hkEval
    have hkm' : k ≤ m := by
      simpa [Pow9TraceCert.baNatLiteral, baTermEval] using hkm
    have hkdvd : k ∣ w :=
      hdvd k hkOne hkm'
    exact
      (dvdPureFormula_eval_iff_of_one_le (k := k) (w := w) hkOne
          (Function.update env indexVar k)
        (by simp [indexVar, Function.update])
        (by simp [indexVar, witnessVar, Function.update, hw0])).2 hkdvd

theorem lcmDvdBoundPureFormula_eval_iff_cert_at_of_env
    (m bound w : ℕ) (env : ℕ → ℕ)
    (hw : env witnessVar = w) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDvdBoundPureFormula m bound witnessVar) ↔
      (Nat.lcmUpto m ∣ w ∧ 0 < w ∧ w ≤ bound) := by
  constructor
  · intro h
    have hw0 : env 3999 = w := by
      simpa [witnessVar] using hw
    rcases h with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨(lcmDvdPureFormula_eval_iff_of_env m w env hw).1 hdvd,
        by
          have hwposNat : 1 ≤ env 3999 := by
            simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
              witnessVar] using hwpos
          have hwposNat' : 1 ≤ w := by
            simpa [hw0] using hwposNat
          exact Nat.succ_le_iff.mp hwposNat',
        by
          have hwleNat : env 3999 ≤ bound := by
            simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
              witnessVar] using hwle
          simpa [hw0] using hwleNat⟩
  · intro h
    have hw0 : env 3999 = w := by
      simpa [witnessVar] using hw
    rcases h with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨(lcmDvdPureFormula_eval_iff_of_env m w env hw).2 hdvd,
        by
          have hwpos' : 1 ≤ w := Nat.succ_le_iff.mpr hwpos
          have hwposEnv : 1 ≤ env 3999 := by
            simpa [hw0] using hwpos'
          simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
            witnessVar] using hwposEnv,
        by
          have hwleEnv : env 3999 ≤ bound := by
            simpa [hw0] using hwle
          simpa [lcmDvdBoundPureFormula, baFormulaEval, baTermEval,
            witnessVar] using hwleEnv⟩

theorem lcmDvdBoundPureTargetFormula_eval_iff_certificate_of_env
    (m bound : ℕ) (env : ℕ → ℕ)
    (hbound : env witnessVar = bound) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDvdBoundPureTargetFormula m bound) ↔
      Nonempty (LcmDvdBoundCert m bound) := by
  constructor
  · intro h
    rcases h with ⟨w, hwleBound, hbody⟩
    have hw :
        (Function.update env witnessVar w) witnessVar = w := by
      simp [witnessVar, Function.update]
    have hbody' :
        baFormulaEval primitiveAtomInterpretation
          (Function.update env witnessVar w)
          (lcmDvdBoundPureFormula m bound witnessVar) := by
      simpa [lcmDvdBoundPureTargetFormula, polytimeDefinabilityFormula]
        using hbody
    rcases (lcmDvdBoundPureFormula_eval_iff_cert_at_of_env
        m bound w (Function.update env witnessVar w) hw).1
        hbody' with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨{ witness := w
         dvdWitness := hdvd
         witness_pos := hwpos
         witness_le_bound := hwle }⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    refine ⟨cert.witness, ?_, ?_⟩
    · have hbound0 : env 3999 = bound := by
        simpa [witnessVar] using hbound
      simpa [baTermEval, witnessVar, hbound0] using
        cert.witness_le_bound
    · have hw :
          (Function.update env witnessVar cert.witness) witnessVar =
            cert.witness := by
        simp [witnessVar, Function.update]
      have hbody :=
        (lcmDvdBoundPureFormula_eval_iff_cert_at_of_env
          m bound cert.witness
          (Function.update env witnessVar cert.witness) hw).2
          ⟨cert.dvdWitness, cert.witness_pos, cert.witness_le_bound⟩
      simpa [lcmDvdBoundPureTargetFormula, polytimeDefinabilityFormula]
        using hbody

def lcmDvdBoundPureFormulaWithBoundTerm
    (m witnessVar : ℕ) (boundTerm : BATerm) : BAFormula :=
  BAFormula.and (lcmDvdPureFormula m witnessVar)
    (BAFormula.and
      (BAFormula.le (BATerm.succ BATerm.zero) (BATerm.var witnessVar))
      (BAFormula.le (BATerm.var witnessVar) boundTerm))

theorem lcmDvdBoundPureFormulaWithBoundTerm_atomFree
    (m witnessVar : ℕ) (boundTerm : BATerm) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDvdBoundPureFormulaWithBoundTerm m witnessVar boundTerm) := by
  simp [lcmDvdBoundPureFormulaWithBoundTerm, lcmDvdPureFormula_atomFree,
    Pow9TraceCert.baFormulaAtomFree]

theorem lcmDvdBoundPureFormulaWithBoundTerm_eval_iff_cert_at_of_env
    (m boundValue w : ℕ) (env : ℕ → ℕ) (boundTerm : BATerm)
    (hw : env witnessVar = w)
    (hbound : baTermEval env boundTerm = boundValue) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDvdBoundPureFormulaWithBoundTerm m witnessVar boundTerm) ↔
      (Nat.lcmUpto m ∣ w ∧ 0 < w ∧ w ≤ boundValue) := by
  constructor
  · intro h
    have hw0 : env 3999 = w := by
      simpa [witnessVar] using hw
    rcases h with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨(lcmDvdPureFormula_eval_iff_of_env m w env hw).1 hdvd,
        by
          have hwposNat : 1 ≤ env 3999 := by
            simpa [lcmDvdBoundPureFormulaWithBoundTerm, baFormulaEval,
              baTermEval, witnessVar] using hwpos
          have hwposNat' : 1 ≤ w := by
            simpa [hw0] using hwposNat
          exact Nat.succ_le_iff.mp hwposNat',
        by
          have hwleNat : env 3999 ≤ baTermEval env boundTerm := by
            simpa [lcmDvdBoundPureFormulaWithBoundTerm, baFormulaEval,
              baTermEval, witnessVar] using hwle
          simpa [hw0, hbound] using hwleNat⟩
  · intro h
    have hw0 : env 3999 = w := by
      simpa [witnessVar] using hw
    rcases h with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨(lcmDvdPureFormula_eval_iff_of_env m w env hw).2 hdvd,
        by
          have hwpos' : 1 ≤ w := Nat.succ_le_iff.mpr hwpos
          have hwposEnv : 1 ≤ env 3999 := by
            simpa [hw0] using hwpos'
          simpa [lcmDvdBoundPureFormulaWithBoundTerm, baFormulaEval,
            baTermEval, witnessVar] using hwposEnv,
        by
          have hwleEnv : env 3999 ≤ baTermEval env boundTerm := by
            simpa [hw0, hbound] using hwle
          simpa [lcmDvdBoundPureFormulaWithBoundTerm, baFormulaEval,
            baTermEval, witnessVar] using hwleEnv⟩

def lcmDvdBoundPureTargetFormulaWithBoundVar
    (m boundVar : ℕ) : BAFormula :=
  BAFormula.existsBounded witnessVar (BATerm.var boundVar)
    (lcmDvdBoundPureFormulaWithBoundTerm m witnessVar
      (BATerm.var boundVar))

theorem lcmDvdBoundPureTargetFormulaWithBoundVar_atomFree
    (m boundVar : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDvdBoundPureTargetFormulaWithBoundVar m boundVar) := by
  simp [lcmDvdBoundPureTargetFormulaWithBoundVar,
    lcmDvdBoundPureFormulaWithBoundTerm_atomFree,
    Pow9TraceCert.baFormulaAtomFree]

theorem lcmDvdBoundPureTargetFormulaWithBoundVar_eval_iff_certificate
    (m boundValue boundVar : ℕ) (env : ℕ → ℕ)
    (hbound : env boundVar = boundValue)
    (hboundVar_ne_witness : boundVar ≠ witnessVar) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDvdBoundPureTargetFormulaWithBoundVar m boundVar) ↔
      Nonempty (LcmDvdBoundCert m boundValue) := by
  constructor
  · intro h
    rcases h with ⟨w, _hwleBound, hbody⟩
    have hw :
        (Function.update env witnessVar w) witnessVar = w := by
      simp [witnessVar, Function.update]
    have hboundBody :
        baTermEval (Function.update env witnessVar w)
            (BATerm.var boundVar) = boundValue := by
      simp [baTermEval, Function.update, hbound,
        hboundVar_ne_witness]
    rcases (lcmDvdBoundPureFormulaWithBoundTerm_eval_iff_cert_at_of_env
        m boundValue w (Function.update env witnessVar w)
        (BATerm.var boundVar) hw hboundBody).1
        hbody with ⟨hdvd, hwpos, hwle⟩
    exact
      ⟨{ witness := w
         dvdWitness := hdvd
         witness_pos := hwpos
         witness_le_bound := hwle }⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    refine ⟨cert.witness, ?_, ?_⟩
    · simpa [baTermEval, hbound] using cert.witness_le_bound
    · have hw :
          (Function.update env witnessVar cert.witness) witnessVar =
            cert.witness := by
        simp [witnessVar, Function.update]
      have hboundBody :
          baTermEval (Function.update env witnessVar cert.witness)
              (BATerm.var boundVar) = boundValue := by
        simp [baTermEval, Function.update, hbound,
          hboundVar_ne_witness]
      exact
        (lcmDvdBoundPureFormulaWithBoundTerm_eval_iff_cert_at_of_env
          m boundValue cert.witness
          (Function.update env witnessVar cert.witness)
          (BATerm.var boundVar) hw hboundBody).2
          ⟨cert.dvdWitness, cert.witness_pos, cert.witness_le_bound⟩

def lcmDvdBoundPureTargetProofObject
    (m bound : ℕ) (_hcert : Nonempty (LcmDvdBoundCert m bound)) :
    BAProofObject BussS21Axiom :=
  polytimeDefinabilityProofObject witnessVar
    (lcmDvdBoundPureFormula m bound witnessVar)

theorem lcmDvdBoundPureTargetProofObject_conclusion
    (m bound : ℕ) (hcert : Nonempty (LcmDvdBoundCert m bound)) :
    (lcmDvdBoundPureTargetProofObject m bound hcert).conclusion =
      lcmDvdBoundPureTargetFormula m bound := by
  rfl

theorem lcmDvdBoundPureTargetProofObject_size_plus_two_eq_three
    (m bound : ℕ) (hcert : Nonempty (LcmDvdBoundCert m bound)) :
    ((((lcmDvdBoundPureTargetProofObject m bound hcert).size + 2 : ℕ) : ℝ)) =
      3 := by
  change ((1 + 2 : ℕ) : ℝ) = 3
  norm_num

structure LcmDvdBoundPureBoundedFormulaCompiler where
  target : ℕ → ℕ → BAFormula
  boundCost : ℕ → ℕ → ℝ
  target_atomFree :
    ∀ m bound : ℕ, Pow9TraceCert.baFormulaAtomFree (target m bound)
  target_semantics_iff_certificate :
    ∀ m bound : ℕ,
      baFormulaEval primitiveAtomInterpretation
          (Function.update (fun _idx => m) witnessVar bound)
          (target m bound) ↔
        Nonempty (LcmDvdBoundCert m bound)
  compile :
    ∀ m bound : ℕ,
      Nonempty (LcmDvdBoundCert m bound) → BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ m bound : ℕ,
      ∀ hcert : Nonempty (LcmDvdBoundCert m bound),
        (compile m bound hcert).conclusion =
          target m bound
  compile_size_plus_two_le :
    ∀ m bound : ℕ,
      ∀ hcert : Nonempty (LcmDvdBoundCert m bound),
        ((((compile m bound hcert).size + 2 : ℕ) : ℝ)) ≤
          boundCost m bound

def lcmDvdBoundPureBoundedFormulaCompiler :
    LcmDvdBoundPureBoundedFormulaCompiler where
  target := lcmDvdBoundPureTargetFormula
  boundCost := fun _m _bound => 3
  target_atomFree := lcmDvdBoundPureTargetFormula_atomFree
  target_semantics_iff_certificate :=
    lcmDvdBoundPureTargetFormula_eval_iff_certificate
  compile := lcmDvdBoundPureTargetProofObject
  compile_conclusion := lcmDvdBoundPureTargetProofObject_conclusion
  compile_size_plus_two_le := by
    intro m bound hcert
    rw [lcmDvdBoundPureTargetProofObject_size_plus_two_eq_three]

end LcmDvdBoundCert

/-- Combined certificate for the `lcmDoubleLeNinePow` primitive:
`powValue` is certified as `9^n`, and a positive multiple of
`Nat.lcmUpto (2*n)` is certified below that value. -/
structure LcmDoubleLeNinePowCertificate (n : ℕ) where
  powValue : ℕ
  powCert : Pow9TraceCert n powValue
  lcmCert : LcmDvdBoundCert (2 * n) powValue

abbrev lcmDoubleLeNinePowCertificateAccepted (n : ℕ) : Prop :=
  Nonempty (LcmDoubleLeNinePowCertificate n)

namespace LcmDoubleLeNinePowCertificate

theorem accepted_iff_lcm_bound (n : ℕ) :
    lcmDoubleLeNinePowCertificateAccepted n ↔
      Nat.lcmUpto (2 * n) ≤ 9 ^ n := by
  constructor
  · intro hcert
    rcases hcert with ⟨cert⟩
    have hpow :
        cert.powValue = 9 ^ n :=
      (Pow9TraceCert.accepted_iff n cert.powValue).1
        ⟨cert.powCert⟩
    have hlcm :
        Nat.lcmUpto (2 * n) ≤ cert.powValue :=
      (LcmDvdBoundCert.accepted_iff (2 * n) cert.powValue).1
        ⟨cert.lcmCert⟩
    simpa [hpow] using hlcm
  · intro hbound
    exact
      ⟨{ powValue := 9 ^ n
         powCert :=
          { trace := fun i => 9 ^ i
            start := by simp
            step := by
              intro i _hi
              simp [pow_succ, Nat.mul_comm]
            final := by rfl }
         lcmCert :=
          { witness := Nat.lcmUpto (2 * n)
            dvdWitness := dvd_rfl
            witness_pos := Nat.lcmUpto_pos (2 * n)
            witness_le_bound := hbound } }⟩

end LcmDoubleLeNinePowCertificate

def lcmDoubleLeNinePowPureGraph (n : ℕ) : BAFormula :=
  BAFormula.existsBounded Pow9TraceCert.pow9ValueVar
    (Pow9TraceCert.pow9PureTerm n)
    (BAFormula.and (Pow9TraceCert.pow9PureTargetFormula n)
      (LcmDvdBoundCert.lcmDvdBoundPureTargetFormulaWithBoundVar
        (2 * n) Pow9TraceCert.pow9ValueVar))

theorem lcmDoubleLeNinePowPureGraph_atomFree (n : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDoubleLeNinePowPureGraph n) := by
  simp [lcmDoubleLeNinePowPureGraph,
    Pow9TraceCert.pow9PureTargetFormula_atomFree,
    LcmDvdBoundCert.lcmDvdBoundPureTargetFormulaWithBoundVar_atomFree,
    Pow9TraceCert.baFormulaAtomFree]

theorem pow9ValueVar_ne_lcmWitnessVar :
    Pow9TraceCert.pow9ValueVar ≠ LcmDvdBoundCert.witnessVar := by
  norm_num [Pow9TraceCert.pow9ValueVar, LcmDvdBoundCert.witnessVar]

theorem lcmDoubleLeNinePowPureGraph_eval_iff_certificate
    (n : ℕ) (env : ℕ → ℕ) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDoubleLeNinePowPureGraph n) ↔
      lcmDoubleLeNinePowCertificateAccepted n := by
  constructor
  · intro h
    rcases h with ⟨y, _hyBound, hbody⟩
    rcases hbody with ⟨hpowFormula, hlcmFormula⟩
    let envY := Function.update env Pow9TraceCert.pow9ValueVar y
    have hyEnv : envY Pow9TraceCert.pow9ValueVar = y := by
      simp [envY, Pow9TraceCert.pow9ValueVar]
    have hpowCert :
        Nonempty (Pow9TraceCert n y) :=
      (Pow9TraceCert.pow9PureTargetFormula_eval_iff_certificate_of_env
        n y envY hyEnv).1 hpowFormula
    have hlcmCert :
        Nonempty (LcmDvdBoundCert (2 * n) y) :=
      (LcmDvdBoundCert.lcmDvdBoundPureTargetFormulaWithBoundVar_eval_iff_certificate
          (2 * n) y Pow9TraceCert.pow9ValueVar envY hyEnv
          pow9ValueVar_ne_lcmWitnessVar).1 hlcmFormula
    rcases hpowCert with ⟨powCert⟩
    rcases hlcmCert with ⟨lcmCert⟩
    exact
      ⟨{ powValue := y
         powCert := powCert
         lcmCert := lcmCert }⟩
  · intro hcert
    rcases hcert with ⟨cert⟩
    refine ⟨cert.powValue, ?_, ?_⟩
    · have hpowValue : cert.powValue = 9 ^ n :=
        (Pow9TraceCert.accepted_iff n cert.powValue).1
          ⟨cert.powCert⟩
      have hle : cert.powValue ≤ 9 ^ n := by
        simp [hpowValue]
      simpa [Pow9TraceCert.baTermEval_pow9PureTerm] using hle
    · constructor
      · have hyEnv :
            (Function.update env Pow9TraceCert.pow9ValueVar
                cert.powValue) Pow9TraceCert.pow9ValueVar =
              cert.powValue := by
          simp [Pow9TraceCert.pow9ValueVar, Function.update]
        exact
          (Pow9TraceCert.pow9PureTargetFormula_eval_iff_certificate_of_env
            n cert.powValue
            (Function.update env Pow9TraceCert.pow9ValueVar cert.powValue)
            hyEnv).2 ⟨cert.powCert⟩
      · have hyEnv :
            (Function.update env Pow9TraceCert.pow9ValueVar
                cert.powValue) Pow9TraceCert.pow9ValueVar =
              cert.powValue := by
          simp [Pow9TraceCert.pow9ValueVar, Function.update]
        exact
          (LcmDvdBoundCert.lcmDvdBoundPureTargetFormulaWithBoundVar_eval_iff_certificate
              (2 * n) cert.powValue Pow9TraceCert.pow9ValueVar
              (Function.update env Pow9TraceCert.pow9ValueVar cert.powValue)
              hyEnv pow9ValueVar_ne_lcmWitnessVar).2
            ⟨cert.lcmCert⟩

def lcmDoubleLeNinePowPureTarget (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula
    (polytimePrimitiveName
      TailBoundExpandedPrimitive.lcmDoubleLeNinePow)
    (lcmDoubleLeNinePowPureGraph n)

theorem lcmDoubleLeNinePowPureTarget_atomFree (n : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmDoubleLeNinePowPureTarget n) := by
  simp [lcmDoubleLeNinePowPureTarget, polytimeDefinabilityFormula,
    lcmDoubleLeNinePowPureGraph_atomFree,
    Pow9TraceCert.baFormulaAtomFree]

theorem lcmDoubleLeNinePowPureTarget_eval_iff_certificate
    (n : ℕ) :
    baFormulaEval primitiveAtomInterpretation (fun _idx => n)
        (lcmDoubleLeNinePowPureTarget n) ↔
      lcmDoubleLeNinePowCertificateAccepted n := by
  constructor
  · intro h
    rcases h with ⟨value, _hbound, hgraph⟩
    exact
      (lcmDoubleLeNinePowPureGraph_eval_iff_certificate n
        (Function.update (fun _idx => n)
          (polytimePrimitiveName
            TailBoundExpandedPrimitive.lcmDoubleLeNinePow) value)).1
        hgraph
  · intro hcert
    refine ⟨0, ?_, ?_⟩
    · simp [baTermEval]
    · exact
        (lcmDoubleLeNinePowPureGraph_eval_iff_certificate n
          (Function.update (fun _idx => n)
            (polytimePrimitiveName
              TailBoundExpandedPrimitive.lcmDoubleLeNinePow) 0)).2
          hcert

theorem lcmDoubleLeNinePowPureTarget_eval_iff_lcm_bound
    (n : ℕ) :
    baFormulaEval primitiveAtomInterpretation (fun _idx => n)
        (lcmDoubleLeNinePowPureTarget n) ↔
      Nat.lcmUpto (2 * n) ≤ 9 ^ n := by
  rw [lcmDoubleLeNinePowPureTarget_eval_iff_certificate,
    LcmDoubleLeNinePowCertificate.accepted_iff_lcm_bound]

def lcmDoubleLeNinePowPureProofObject
    (n : ℕ) (_hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    BAProofObject BussS21Axiom :=
  polytimeDefinabilityProofObject
    (polytimePrimitiveName
      TailBoundExpandedPrimitive.lcmDoubleLeNinePow)
    (lcmDoubleLeNinePowPureGraph n)

theorem lcmDoubleLeNinePowPureProofObject_conclusion
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    (lcmDoubleLeNinePowPureProofObject n hcert).conclusion =
      lcmDoubleLeNinePowPureTarget n := by
  rfl

theorem lcmDoubleLeNinePowPureProofObject_size_plus_two_eq_three
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    ((((lcmDoubleLeNinePowPureProofObject n hcert).size + 2 : ℕ) : ℝ)) =
      3 := by
  change ((1 + 2 : ℕ) : ℝ) = 3
  norm_num

theorem lcmDoubleLeNinePowPureProofObject_size_plus_two_le
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    ((((lcmDoubleLeNinePowPureProofObject n hcert).size + 2 : ℕ) : ℝ)) ≤
      3 := by
  rw [lcmDoubleLeNinePowPureProofObject_size_plus_two_eq_three]

structure LcmDoubleLeNinePowPureS21CertificateCompiler where
  target : ℕ → BAFormula
  bound : ℕ → ℝ
  target_eq :
    ∀ n : ℕ, target n = lcmDoubleLeNinePowPureTarget n
  target_atomFree :
    ∀ n : ℕ, Pow9TraceCert.baFormulaAtomFree (target n)
  target_semantics_iff_certificate :
    ∀ n : ℕ,
      baFormulaEval primitiveAtomInterpretation (fun _idx => n)
          (target n) ↔
        lcmDoubleLeNinePowCertificateAccepted n
  target_semantics_iff_lcm_bound :
    ∀ n : ℕ,
      baFormulaEval primitiveAtomInterpretation (fun _idx => n)
          (target n) ↔
        Nat.lcmUpto (2 * n) ≤ 9 ^ n
  compile :
    ∀ n : ℕ,
      lcmDoubleLeNinePowCertificateAccepted n →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ,
      ∀ hcert : lcmDoubleLeNinePowCertificateAccepted n,
        (compile n hcert).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hcert : lcmDoubleLeNinePowCertificateAccepted n,
        ((((compile n hcert).size + 2 : ℕ) : ℝ)) ≤ bound n

def lcmDoubleLeNinePowPureS21CertificateCompiler :
    LcmDoubleLeNinePowPureS21CertificateCompiler where
  target := lcmDoubleLeNinePowPureTarget
  bound := fun _n => 3
  target_eq := by
    intro n
    rfl
  target_atomFree := lcmDoubleLeNinePowPureTarget_atomFree
  target_semantics_iff_certificate :=
    lcmDoubleLeNinePowPureTarget_eval_iff_certificate
  target_semantics_iff_lcm_bound :=
    lcmDoubleLeNinePowPureTarget_eval_iff_lcm_bound
  compile := lcmDoubleLeNinePowPureProofObject
  compile_conclusion := lcmDoubleLeNinePowPureProofObject_conclusion
  compile_size_plus_two_le := by
    intro n hcert
    exact lcmDoubleLeNinePowPureProofObject_size_plus_two_le n hcert

def baPowTerm (base : ℕ) : ℕ → BATerm
  | 0 => BATerm.one
  | n + 1 => BATerm.mul (Pow9TraceCert.baNatLiteral base)
      (baPowTerm base n)

@[simp] theorem baTermEval_baPowTerm
    (env : ℕ → ℕ) (base n : ℕ) :
    baTermEval env (baPowTerm base n) = base ^ n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [baPowTerm, baTermEval, ih, pow_succ, Nat.mul_comm]

def geometricTailPureGraph (n : ℕ) : BAFormula :=
  BAFormula.le
    (BATerm.succ
      (BATerm.mul (Pow9TraceCert.baNatLiteral 4) (baPowTerm 9 n)))
    (baPowTerm 16 n)

theorem geometricTailPureGraph_atomFree (n : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (geometricTailPureGraph n) := by
  simp [geometricTailPureGraph, Pow9TraceCert.baFormulaAtomFree]

theorem geometricTailPureGraph_eval_iff_nat
    (n : ℕ) (env : ℕ → ℕ) :
    baFormulaEval primitiveAtomInterpretation env
        (geometricTailPureGraph n) ↔
      4 * 9 ^ n < 16 ^ n := by
  simp [geometricTailPureGraph, baFormulaEval, baTermEval]

theorem geometricTailNat_iff_real (n : ℕ) :
    4 * 9 ^ n < 16 ^ n ↔
      4 * ((9 : ℝ) / 16) ^ n < 1 := by
  have h16pos : (0 : ℝ) < (16 : ℝ) ^ n :=
    pow_pos (by norm_num) n
  constructor
  · intro h
    have hrealNat :
        ((4 * 9 ^ n : ℕ) : ℝ) < ((16 ^ n : ℕ) : ℝ) := by
      exact_mod_cast h
    have hreal : (4 : ℝ) * (9 : ℝ) ^ n < (16 : ℝ) ^ n := by
      simpa [Nat.cast_mul, Nat.cast_pow] using hrealNat
    rw [div_pow]
    field_simp [h16pos.ne']
    simpa using hreal
  · intro h
    have hreal : (4 : ℝ) * (9 : ℝ) ^ n < (16 : ℝ) ^ n := by
      rw [div_pow] at h
      field_simp [h16pos.ne'] at h
      simpa using h
    exact_mod_cast hreal

theorem geometricTailPureGraph_eval_iff
    (n : ℕ) (env : ℕ → ℕ) :
    baFormulaEval primitiveAtomInterpretation env
        (geometricTailPureGraph n) ↔
      4 * ((9 : ℝ) / 16) ^ n < 1 := by
  rw [geometricTailPureGraph_eval_iff_nat,
    geometricTailNat_iff_real]

def geometricTailPureTarget (n : ℕ) : BAFormula :=
  polytimeDefinabilityFormula
    (polytimePrimitiveName
      TailBoundExpandedPrimitive.geometricTailLtOne)
    (geometricTailPureGraph n)

theorem geometricTailPureTarget_atomFree (n : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (geometricTailPureTarget n) := by
  simp [geometricTailPureTarget, polytimeDefinabilityFormula,
    geometricTailPureGraph_atomFree, Pow9TraceCert.baFormulaAtomFree]

theorem geometricTailPureTarget_eval_iff
    (n : ℕ) :
    baFormulaEval primitiveAtomInterpretation (fun _idx => n)
        (geometricTailPureTarget n) ↔
      4 * ((9 : ℝ) / 16) ^ n < 1 := by
  constructor
  · intro h
    rcases h with ⟨value, _hbound, hgraph⟩
    exact
      (geometricTailPureGraph_eval_iff n
        (Function.update (fun _idx => n)
          (polytimePrimitiveName
            TailBoundExpandedPrimitive.geometricTailLtOne) value)).1
        hgraph
  · intro hgeom
    refine ⟨0, ?_, ?_⟩
    · simp [baTermEval]
    · exact
        (geometricTailPureGraph_eval_iff n
          (Function.update (fun _idx => n)
            (polytimePrimitiveName
              TailBoundExpandedPrimitive.geometricTailLtOne) 0)).2
          hgeom

def geometricTailPureProofObject
    (n : ℕ) (_hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1) :
    BAProofObject BussS21Axiom :=
  polytimeDefinabilityProofObject
    (polytimePrimitiveName
      TailBoundExpandedPrimitive.geometricTailLtOne)
    (geometricTailPureGraph n)

theorem geometricTailPureProofObject_conclusion
    (n : ℕ) (hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1) :
    (geometricTailPureProofObject n hgeom).conclusion =
      geometricTailPureTarget n := by
  rfl

theorem geometricTailPureProofObject_size_plus_two_eq_three
    (n : ℕ) (hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1) :
    ((((geometricTailPureProofObject n hgeom).size + 2 : ℕ) : ℝ)) =
      3 := by
  change ((1 + 2 : ℕ) : ℝ) = 3
  norm_num

theorem geometricTailPureProofObject_size_plus_two_le
    (n : ℕ) (hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1) :
    ((((geometricTailPureProofObject n hgeom).size + 2 : ℕ) : ℝ)) ≤
      3 := by
  rw [geometricTailPureProofObject_size_plus_two_eq_three]

structure GeometricTailPureS21Compiler where
  target : ℕ → BAFormula
  bound : ℕ → ℝ
  target_atomFree :
    ∀ n : ℕ, Pow9TraceCert.baFormulaAtomFree (target n)
  target_semantics_iff :
    ∀ n : ℕ,
      baFormulaEval primitiveAtomInterpretation (fun _idx => n)
          (target n) ↔
        4 * ((9 : ℝ) / 16) ^ n < 1
  compile :
    ∀ n : ℕ,
      4 * ((9 : ℝ) / 16) ^ n < 1 →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ,
      ∀ hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1,
        (compile n hgeom).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hgeom : 4 * ((9 : ℝ) / 16) ^ n < 1,
        ((((compile n hgeom).size + 2 : ℕ) : ℝ)) ≤ bound n

def geometricTailPureS21Compiler :
    GeometricTailPureS21Compiler where
  target := geometricTailPureTarget
  bound := fun _n => 3
  target_atomFree := geometricTailPureTarget_atomFree
  target_semantics_iff := geometricTailPureTarget_eval_iff
  compile := geometricTailPureProofObject
  compile_conclusion := geometricTailPureProofObject_conclusion
  compile_size_plus_two_le := by
    intro n hgeom
    exact geometricTailPureProofObject_size_plus_two_le n hgeom

theorem lcmDoubleLeNinePowPrimitiveGraph_eval_iff_certificate
    (n : ℕ) (env : ℕ → ℕ) :
    baFormulaEval primitiveAtomInterpretation env
        (lcmDoubleLeNinePowPrimitiveGraph n) ↔
      lcmDoubleLeNinePowCertificateAccepted n := by
  rw [lcmDoubleLeNinePowPrimitiveGraph_eval_iff,
    LcmDoubleLeNinePowCertificate.accepted_iff_lcm_bound]

def lcmDoubleLeNinePowCertificateTarget (n : ℕ) : BAFormula :=
  polytimePrimitiveTarget TailBoundExpandedPrimitive.lcmDoubleLeNinePow n

def lcmDoubleLeNinePowCertificateProofBound (_n : ℕ) : ℝ :=
  3

theorem lcmDoubleLeNinePowCertificateTarget_exact (n : ℕ) :
    lcmDoubleLeNinePowCertificateTarget n =
      polytimeDefinabilityFormula
        (polytimePrimitiveName
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow)
        (lcmDoubleLeNinePowPrimitiveGraph n) := by
  rfl

theorem lcmDoubleLeNinePowCertificateTarget_hasTailPrimitiveAtom
    (n : ℕ) :
    lcmDoubleLeNinePowCertificateTarget n =
      polytimeDefinabilityFormula
        (polytimePrimitiveName
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow)
        (BAFormula.atom
          BoundedArithmeticLab.FormulaFamily.tailLcmDoubleLeNinePow n) := by
  rfl

theorem lcmDoubleLeNinePowCertificateTarget_eval_iff_certificate
    (n : ℕ) :
    baFormulaEval primitiveAtomInterpretation (fun _idx => n)
        (lcmDoubleLeNinePowCertificateTarget n) ↔
      lcmDoubleLeNinePowCertificateAccepted n := by
  rw [lcmDoubleLeNinePowCertificateTarget,
    primitiveAtomEval_polytimePrimitiveTarget_iff]
  exact (LcmDoubleLeNinePowCertificate.accepted_iff_lcm_bound n).symm

def lcmDoubleLeNinePowCertificateProofObject
    (n : ℕ) (_hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    BAProofObject BussS21Axiom :=
  polytimeDefinabilityProofObject
    (polytimePrimitiveName
      TailBoundExpandedPrimitive.lcmDoubleLeNinePow)
    (lcmDoubleLeNinePowPrimitiveGraph n)

theorem lcmDoubleLeNinePowCertificateProofObject_conclusion
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    (lcmDoubleLeNinePowCertificateProofObject n hcert).conclusion =
      lcmDoubleLeNinePowCertificateTarget n := by
  rfl

theorem lcmDoubleLeNinePowCertificateProofObject_size_plus_two_eq_three
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    ((((lcmDoubleLeNinePowCertificateProofObject n hcert).size + 2 : ℕ) : ℝ)) =
      lcmDoubleLeNinePowCertificateProofBound n := by
  change ((1 + 2 : ℕ) : ℝ) = 3
  norm_num

theorem lcmDoubleLeNinePowCertificateProofObject_size_plus_two_le
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    ((((lcmDoubleLeNinePowCertificateProofObject n hcert).size + 2 : ℕ) : ℝ)) ≤
      lcmDoubleLeNinePowCertificateProofBound n := by
  rw [lcmDoubleLeNinePowCertificateProofObject_size_plus_two_eq_three]

/-- Audit package for the current LCM certificate-to-S21 layer.  It is honest
about the remaining pure-encoding boundary: the target formula is a
`polytimeDefinabilityFormula` over the project-specific `tailLcmDoubleLeNinePow`
primitive graph.  The later step is to eliminate that primitive graph into a
pure Buss S21 bounded formula. -/
structure LcmDoubleLeNinePowS21CertificateCompiler where
  target : ℕ → BAFormula
  bound : ℕ → ℝ
  target_eq :
    ∀ n : ℕ, target n = lcmDoubleLeNinePowCertificateTarget n
  target_semantics_iff_certificate :
    ∀ n : ℕ,
      baFormulaEval primitiveAtomInterpretation (fun _idx => n)
          (target n) ↔
        lcmDoubleLeNinePowCertificateAccepted n
  compile :
    ∀ n : ℕ,
      lcmDoubleLeNinePowCertificateAccepted n →
        BAProofObject BussS21Axiom
  compile_conclusion :
    ∀ n : ℕ,
      ∀ hcert : lcmDoubleLeNinePowCertificateAccepted n,
        (compile n hcert).conclusion = target n
  compile_size_plus_two_le :
    ∀ n : ℕ,
      ∀ hcert : lcmDoubleLeNinePowCertificateAccepted n,
        ((((compile n hcert).size + 2 : ℕ) : ℝ)) ≤ bound n
  target_has_tail_primitive_atom :
    ∀ n : ℕ,
      target n =
        polytimeDefinabilityFormula
          (polytimePrimitiveName
            TailBoundExpandedPrimitive.lcmDoubleLeNinePow)
          (BAFormula.atom
            BoundedArithmeticLab.FormulaFamily.tailLcmDoubleLeNinePow n)

def lcmDoubleLeNinePowS21CertificateCompiler :
    LcmDoubleLeNinePowS21CertificateCompiler where
  target := lcmDoubleLeNinePowCertificateTarget
  bound := lcmDoubleLeNinePowCertificateProofBound
  target_eq := by
    intro n
    rfl
  target_semantics_iff_certificate :=
    lcmDoubleLeNinePowCertificateTarget_eval_iff_certificate
  compile := lcmDoubleLeNinePowCertificateProofObject
  compile_conclusion :=
    lcmDoubleLeNinePowCertificateProofObject_conclusion
  compile_size_plus_two_le :=
    lcmDoubleLeNinePowCertificateProofObject_size_plus_two_le
  target_has_tail_primitive_atom :=
    lcmDoubleLeNinePowCertificateTarget_hasTailPrimitiveAtom

theorem residual_polytimePrimitiveGraph_isAtom
    {p : TailBoundExpandedPrimitive} (hp : residualPrimitiveAtom p)
    (n : ℕ) :
    ∃ family : BoundedArithmeticLab.FormulaFamily,
      polytimePrimitiveGraph p n = BAFormula.atom family n := by
  cases p <;> simp [residualPrimitiveAtom] at hp ⊢ <;>
    first
      | exact ⟨BoundedArithmeticLab.FormulaFamily.tailLcmDoubleLeNinePow, rfl⟩
      | exact ⟨BoundedArithmeticLab.FormulaFamily.tailGeometricTailLtOne, rfl⟩
      | exact ⟨BoundedArithmeticLab.FormulaFamily.tailAnalyticTailBound, rfl⟩

theorem residualPrimitiveAtom_iff_ne_oneLe
    (p : TailBoundExpandedPrimitive) :
    residualPrimitiveAtom p ↔
      p ≠ TailBoundExpandedPrimitive.oneLe := by
  cases p <;> simp [residualPrimitiveAtom]

theorem polytimePrimitiveGraph_isAtom_iff_residual
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    (∃ family : BoundedArithmeticLab.FormulaFamily,
      polytimePrimitiveGraph p n = BAFormula.atom family n) ↔
      residualPrimitiveAtom p := by
  constructor
  · intro h
    cases p with
    | oneLe =>
        rcases h with ⟨family, hfamily⟩
        cases hfamily
    | lcmDoubleLeNinePow =>
        simp [residualPrimitiveAtom]
    | geometricTailLtOne =>
        simp [residualPrimitiveAtom]
    | analyticTailBound =>
        simp [residualPrimitiveAtom]
  · intro hp
    exact residual_polytimePrimitiveGraph_isAtom hp n

/-- Audit-facing object-language specification for the current 3^n tail-bound
primitive layer.  It records exactly what has been pushed into genuine
`BAFormula` syntax and exactly which primitives still remain project-specific
residual atoms. -/
structure TailBoundPrimitiveObjectLanguageSpec : Prop where
  oneLe_expanded :
    ∀ n : ℕ,
      polytimePrimitiveGraph TailBoundExpandedPrimitive.oneLe n =
        BAFormula.le (BATerm.succ BATerm.zero) (BATerm.var 0)
  lcm_graph_exact :
    ∀ n : ℕ,
      polytimePrimitiveGraph
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow n =
        lcmDoubleLeNinePowPrimitiveGraph n
  lcm_eval_iff :
    ∀ n : ℕ,
      ∀ env : ℕ → ℕ,
        baFormulaEval primitiveAtomInterpretation env
            (lcmDoubleLeNinePowPrimitiveGraph n) ↔
          Nat.lcmUpto (2 * n) ≤ 9 ^ n
  lcm_not_old_project_atom :
    ∀ n : ℕ,
      polytimePrimitiveGraph
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow n ≠
        BAFormula.atom
          BoundedArithmeticLab.FormulaFamily.sondowLogRelation n
  residual_iff_not_oneLe :
    ∀ p : TailBoundExpandedPrimitive,
      residualPrimitiveAtom p ↔
        p ≠ TailBoundExpandedPrimitive.oneLe
  atom_iff_residual :
    ∀ p : TailBoundExpandedPrimitive,
      ∀ n : ℕ,
        (∃ family : BoundedArithmeticLab.FormulaFamily,
          polytimePrimitiveGraph p n = BAFormula.atom family n) ↔
          residualPrimitiveAtom p
  semantic_alignment :
    ∀ p : TailBoundExpandedPrimitive,
      ∀ n : ℕ,
        baFormulaEval primitiveAtomInterpretation (fun _idx => n)
            (polytimePrimitiveTarget p n) ↔
          TailBoundExpandedPrimitive.eval p n

theorem tailBoundPrimitiveObjectLanguageSpec_closed :
    TailBoundPrimitiveObjectLanguageSpec where
  oneLe_expanded := oneLe_polytimePrimitiveGraph_noAtom
  lcm_graph_exact := lcmDoubleLeNinePow_polytimePrimitiveGraph_exact
  lcm_eval_iff := lcmDoubleLeNinePowPrimitiveGraph_eval_iff
  lcm_not_old_project_atom :=
    lcmDoubleLeNinePow_graph_not_old_sondowLogRelation_atom
  residual_iff_not_oneLe := residualPrimitiveAtom_iff_ne_oneLe
  atom_iff_residual := polytimePrimitiveGraph_isAtom_iff_residual
  semantic_alignment := primitiveAtomEval_polytimePrimitiveTarget_iff

def polytimeDefinabilityCompiler :
    TailBoundPrimitiveS21Compiler where
  target := polytimePrimitiveTarget
  bound := fun _p _n => 3
  compile := by
    intro p n _hp
    exact proofObjectOfBussS21Derivation
      (BADerivation.ax
        (BussS21Axiom.polytimeDefinability
          (polytimePrimitiveName p) (polytimePrimitiveGraph p n)))
  compile_conclusion := by
    intro p n hp
    rfl
  compile_size_plus_two_le := by
    intro p n hp
    change (3 : ℝ) ≤ 3
    norm_num

@[simp] theorem polytimeDefinabilityCompiler_target
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    polytimeDefinabilityCompiler.target p n =
      polytimePrimitiveTarget p n :=
  rfl

@[simp] theorem polytimeDefinabilityCompiler_bound
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    polytimeDefinabilityCompiler.bound p n = 3 :=
  rfl

theorem polytimeDefinabilityCompiler_compile_conclusion
    (p : TailBoundExpandedPrimitive) (n : ℕ)
    (hp : TailBoundExpandedPrimitive.eval p n) :
    (polytimeDefinabilityCompiler.compile p n hp).conclusion =
      polytimePrimitiveTarget p n :=
  rfl

theorem polytimeDefinabilityCompiler_compile_size_plus_two_eq_three
    (p : TailBoundExpandedPrimitive) (n : ℕ)
    (hp : TailBoundExpandedPrimitive.eval p n) :
    ((((polytimeDefinabilityCompiler.compile p n hp).size + 2 : ℕ) : ℝ)) =
      3 := by
  change ((1 + 2 : ℕ) : ℝ) = 3
  norm_num

theorem lcmDoubleLeNinePow_polytimeDefinabilityCompiler_target_eq
    (n : ℕ) :
    polytimeDefinabilityCompiler.target
        TailBoundExpandedPrimitive.lcmDoubleLeNinePow n =
      lcmDoubleLeNinePowCertificateTarget n := by
  rfl

theorem lcmDoubleLeNinePow_polytimeDefinabilityCompiler_semantics_iff_certificate
    (n : ℕ) :
    baFormulaEval primitiveAtomInterpretation (fun _idx => n)
        (polytimeDefinabilityCompiler.target
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow n) ↔
      lcmDoubleLeNinePowCertificateAccepted n := by
  exact lcmDoubleLeNinePowCertificateTarget_eval_iff_certificate n

theorem lcmDoubleLeNinePow_polytimeDefinabilityCompiler_proof_from_certificate
    (n : ℕ) (hcert : lcmDoubleLeNinePowCertificateAccepted n) :
    ∃ proof : BAProofObject BussS21Axiom,
      proof.conclusion =
        polytimeDefinabilityCompiler.target
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow n ∧
      ((((proof.size + 2 : ℕ) : ℝ)) ≤
        polytimeDefinabilityCompiler.bound
          TailBoundExpandedPrimitive.lcmDoubleLeNinePow n) := by
  refine ⟨lcmDoubleLeNinePowCertificateProofObject n hcert, ?_, ?_⟩
  · rfl
  · rw [lcmDoubleLeNinePowCertificateProofObject_size_plus_two_eq_three]
    change (3 : ℝ) ≤ 3
    norm_num

/-- Semantic alignment required for auditing a primitive compiler.  The S21
proof object can prove the target formula, but this separate field is what says
that the target formula is the intended primitive predicate. -/
structure SemanticAlignment
    (atomEval : BAAtomInterpretation)
    (compiler : TailBoundPrimitiveS21Compiler) : Prop where
  target_iff_eval :
    ∀ p : TailBoundExpandedPrimitive, ∀ n : ℕ,
      baFormulaEval atomEval (fun _idx => n)
          (compiler.target p n) ↔
        TailBoundExpandedPrimitive.eval p n

theorem polytimeDefinabilityCompiler_semanticAlignment :
    SemanticAlignment primitiveAtomInterpretation
      polytimeDefinabilityCompiler where
  target_iff_eval := by
    intro p n
    exact primitiveAtomEval_polytimePrimitiveTarget_iff p n

def lcmThreePowPurePrimitiveTarget
    (p : TailBoundExpandedPrimitive) (n : ℕ) : BAFormula :=
  match p with
  | TailBoundExpandedPrimitive.oneLe =>
      polytimePrimitiveTarget TailBoundExpandedPrimitive.oneLe n
  | TailBoundExpandedPrimitive.lcmDoubleLeNinePow =>
      lcmDoubleLeNinePowPureTarget n
  | TailBoundExpandedPrimitive.geometricTailLtOne =>
      geometricTailPureTarget n
  | TailBoundExpandedPrimitive.analyticTailBound =>
      polytimePrimitiveTarget TailBoundExpandedPrimitive.analyticTailBound n

def lcmThreePowPurePrimitiveBound
    (_p : TailBoundExpandedPrimitive) (_n : ℕ) : ℝ :=
  3

def lcmThreePowPurePrimitiveCompiler :
    TailBoundPrimitiveS21Compiler where
  target := lcmThreePowPurePrimitiveTarget
  bound := lcmThreePowPurePrimitiveBound
  compile := by
    intro p n hp
    cases p with
    | oneLe =>
        exact proofObjectOfBussS21Derivation
          (BADerivation.ax
            (BussS21Axiom.polytimeDefinability
              (polytimePrimitiveName TailBoundExpandedPrimitive.oneLe)
              (polytimePrimitiveGraph TailBoundExpandedPrimitive.oneLe n)))
    | lcmDoubleLeNinePow =>
        have hcert : lcmDoubleLeNinePowCertificateAccepted n :=
          (LcmDoubleLeNinePowCertificate.accepted_iff_lcm_bound n).2 hp
        exact lcmDoubleLeNinePowPureProofObject n hcert
    | geometricTailLtOne =>
        exact geometricTailPureProofObject n hp
    | analyticTailBound =>
        exact proofObjectOfBussS21Derivation
          (BADerivation.ax
            (BussS21Axiom.polytimeDefinability
              (polytimePrimitiveName
                TailBoundExpandedPrimitive.analyticTailBound)
              (polytimePrimitiveGraph
                TailBoundExpandedPrimitive.analyticTailBound n)))
  compile_conclusion := by
    intro p n hp
    cases p <;> rfl
  compile_size_plus_two_le := by
    intro p n hp
    cases p <;>
      change (3 : ℝ) ≤ 3 <;>
      norm_num

@[simp] theorem lcmThreePowPurePrimitiveCompiler_target
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    lcmThreePowPurePrimitiveCompiler.target p n =
      lcmThreePowPurePrimitiveTarget p n :=
  rfl

@[simp] theorem lcmThreePowPurePrimitiveCompiler_bound
    (p : TailBoundExpandedPrimitive) (n : ℕ) :
    lcmThreePowPurePrimitiveCompiler.bound p n = 3 :=
  rfl

theorem lcmThreePowPurePrimitiveCompiler_lcm_target_atomFree
    (n : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmThreePowPurePrimitiveCompiler.target
        TailBoundExpandedPrimitive.lcmDoubleLeNinePow n) := by
  exact lcmDoubleLeNinePowPureTarget_atomFree n

theorem lcmThreePowPurePrimitiveCompiler_geometric_target_atomFree
    (n : ℕ) :
    Pow9TraceCert.baFormulaAtomFree
      (lcmThreePowPurePrimitiveCompiler.target
        TailBoundExpandedPrimitive.geometricTailLtOne n) := by
  exact geometricTailPureTarget_atomFree n

theorem lcmThreePowPurePrimitiveCompiler_semanticAlignment :
    SemanticAlignment primitiveAtomInterpretation
      lcmThreePowPurePrimitiveCompiler where
  target_iff_eval := by
    intro p n
    cases p with
    | oneLe =>
        exact primitiveAtomEval_polytimePrimitiveTarget_iff
          TailBoundExpandedPrimitive.oneLe n
    | lcmDoubleLeNinePow =>
        simpa [lcmThreePowPurePrimitiveTarget,
          TailBoundExpandedPrimitive.eval] using
          lcmDoubleLeNinePowPureTarget_eval_iff_lcm_bound n
    | geometricTailLtOne =>
        simpa [lcmThreePowPurePrimitiveTarget,
          TailBoundExpandedPrimitive.eval] using
          geometricTailPureTarget_eval_iff n
    | analyticTailBound =>
        exact primitiveAtomEval_polytimePrimitiveTarget_iff
          TailBoundExpandedPrimitive.analyticTailBound n

end TailBoundPrimitiveS21Compiler

namespace TailBoundExpandedFormula

def andPrimitiveFragment : TailBoundExpandedFormula → Prop
  | base _ => False
  | primitive _ _ => True
  | and φ ψ => andPrimitiveFragment φ ∧ andPrimitiveFragment ψ
  | or _ _ => False
  | imp _ _ => False

def compileToBAFormula
    (compiler : TailBoundPrimitiveS21Compiler) :
    TailBoundExpandedFormula → BAFormula
  | base φ => φ
  | primitive p n => compiler.target p n
  | and φ ψ =>
      BAFormula.and (compileToBAFormula compiler φ)
        (compileToBAFormula compiler ψ)
  | or φ ψ =>
      BAFormula.or (compileToBAFormula compiler φ)
        (compileToBAFormula compiler ψ)
  | imp φ ψ =>
      BAFormula.imp (compileToBAFormula compiler φ)
        (compileToBAFormula compiler ψ)

def compiledSizeBound
    (compiler : TailBoundPrimitiveS21Compiler) :
    TailBoundExpandedFormula → ℝ
  | base _ => 0
  | primitive p n => compiler.bound p n
  | and φ ψ =>
      compiledSizeBound compiler φ + compiledSizeBound compiler ψ + 4
  | or φ ψ =>
      compiledSizeBound compiler φ + compiledSizeBound compiler ψ + 4
  | imp φ ψ =>
      compiledSizeBound compiler φ + compiledSizeBound compiler ψ + 4

def compileProof
    (compiler : TailBoundPrimitiveS21Compiler) :
    ∀ φ : TailBoundExpandedFormula,
      eval φ → andPrimitiveFragment φ →
        BAProofObject BussS21Axiom
  | base _, _h, hfrag => False.elim hfrag
  | primitive p n, hp, _hfrag => compiler.compile p n hp
  | and φ ψ, h, hfrag =>
      (compileProof compiler φ h.1 hfrag.1).andIntro
        (compileProof compiler ψ h.2 hfrag.2)
  | or _ _, _h, hfrag => False.elim hfrag
  | imp _ _, _h, hfrag => False.elim hfrag

theorem compileProof_conclusion
    (compiler : TailBoundPrimitiveS21Compiler) :
    ∀ φ : TailBoundExpandedFormula,
      ∀ hφ : eval φ,
      ∀ hfrag : andPrimitiveFragment φ,
        (compileProof compiler φ hφ hfrag).conclusion =
          compileToBAFormula compiler φ
  | base _, _h, hfrag => False.elim hfrag
  | primitive p n, hp, _hfrag =>
      compiler.compile_conclusion p n hp
  | and φ ψ, h, hfrag => by
      change
        BAFormula.and (compileProof compiler φ h.1 hfrag.1).conclusion
            (compileProof compiler ψ h.2 hfrag.2).conclusion =
          BAFormula.and (compileToBAFormula compiler φ)
            (compileToBAFormula compiler ψ)
      rw [compileProof_conclusion compiler φ h.1 hfrag.1,
        compileProof_conclusion compiler ψ h.2 hfrag.2]
  | or _ _, _h, hfrag => False.elim hfrag
  | imp _ _, _h, hfrag => False.elim hfrag

theorem compileProof_size_plus_two_le
    (compiler : TailBoundPrimitiveS21Compiler) :
    ∀ φ : TailBoundExpandedFormula,
      ∀ hφ : eval φ,
      ∀ hfrag : andPrimitiveFragment φ,
        ((((compileProof compiler φ hφ hfrag).size + 2 : ℕ) : ℝ)) ≤
          compiledSizeBound compiler φ
  | base _, _h, hfrag => False.elim hfrag
  | primitive p n, hp, _hfrag =>
      compiler.compile_size_plus_two_le p n hp
  | and φ ψ, h, hfrag => by
      dsimp [compileProof, compiledSizeBound]
      rw [BAProofObject.size_andIntro]
      have hleft :=
        compileProof_size_plus_two_le compiler φ h.1 hfrag.1
      have hright :=
        compileProof_size_plus_two_le compiler ψ h.2 hfrag.2
      have hleft' :
          (((compileProof compiler φ h.1 hfrag.1).size : ℝ) + 2) ≤
            compiledSizeBound compiler φ := by
        simpa [Nat.cast_add] using hleft
      have hright' :
          (((compileProof compiler ψ h.2 hfrag.2).size : ℝ) + 2) ≤
            compiledSizeBound compiler ψ := by
        simpa [Nat.cast_add] using hright
      have hcast :
          ((((compileProof compiler φ h.1 hfrag.1).size +
                (compileProof compiler ψ h.2 hfrag.2).size + 1 + 2 : ℕ) : ℝ)) =
            ((compileProof compiler φ h.1 hfrag.1).size : ℝ) +
              ((compileProof compiler ψ h.2 hfrag.2).size : ℝ) + 3 := by
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]
        ring
      rw [hcast]
      nlinarith
  | or _ _, _h, hfrag => False.elim hfrag
  | imp _ _, _h, hfrag => False.elim hfrag

theorem lcmThreePowCertificate_andPrimitiveFragment (n : ℕ) :
    andPrimitiveFragment (lcmThreePowCertificate n) := by
  simp [lcmThreePowCertificate, andPrimitiveFragment]

def compileLcmThreePowProof
    (compiler : TailBoundPrimitiveS21Compiler)
    {n : ℕ}
    (hcert : eval (lcmThreePowCertificate n)) :
    BAProofObject BussS21Axiom :=
  compileProof compiler (lcmThreePowCertificate n) hcert
    (lcmThreePowCertificate_andPrimitiveFragment n)

theorem compileLcmThreePowProof_conclusion
    (compiler : TailBoundPrimitiveS21Compiler)
    {n : ℕ}
    (hcert : eval (lcmThreePowCertificate n)) :
    (compileLcmThreePowProof compiler hcert).conclusion =
      compileToBAFormula compiler (lcmThreePowCertificate n) :=
  compileProof_conclusion compiler (lcmThreePowCertificate n) hcert
    (lcmThreePowCertificate_andPrimitiveFragment n)

theorem compileLcmThreePowProof_size_plus_two_le
    (compiler : TailBoundPrimitiveS21Compiler)
    {n : ℕ}
    (hcert : eval (lcmThreePowCertificate n)) :
    ((((compileLcmThreePowProof compiler hcert).size + 2 : ℕ) : ℝ)) ≤
      compiledSizeBound compiler (lcmThreePowCertificate n) :=
  compileProof_size_plus_two_le compiler (lcmThreePowCertificate n) hcert
    (lcmThreePowCertificate_andPrimitiveFragment n)

theorem compileLcmThreePowProof_eventually
    (compiler : TailBoundPrimitiveS21Compiler) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ proof : BAProofObject BussS21Axiom,
        proof.conclusion =
          compileToBAFormula compiler (lcmThreePowCertificate n) ∧
        ((((proof.size + 2 : ℕ) : ℝ)) ≤
          compiledSizeBound compiler (lcmThreePowCertificate n)) := by
  rcases lcmThreePowCertificate_eventually_complete_unconditional with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  let proof := compileLcmThreePowProof compiler (hN n hn)
  exact
    ⟨proof,
      compileLcmThreePowProof_conclusion compiler (hN n hn),
      compileLcmThreePowProof_size_plus_two_le compiler (hN n hn)⟩

theorem exactTailBound_not_andPrimitiveFragment (n : ℕ) :
    ¬ andPrimitiveFragment (exactTailBound n) := by
  simp [exactTailBound, andPrimitiveFragment]

theorem compileLcmThreePowProof_eventually_polytimeDefinability :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ proof : BAProofObject BussS21Axiom,
        proof.conclusion =
          compileToBAFormula
            TailBoundPrimitiveS21Compiler.polytimeDefinabilityCompiler
            (lcmThreePowCertificate n) ∧
        ((((proof.size + 2 : ℕ) : ℝ)) ≤
          compiledSizeBound
            TailBoundPrimitiveS21Compiler.polytimeDefinabilityCompiler
            (lcmThreePowCertificate n)) :=
  compileLcmThreePowProof_eventually
    TailBoundPrimitiveS21Compiler.polytimeDefinabilityCompiler

theorem lcmThreePowPureCompiledFormula_eval_iff
    (n : ℕ) :
    baFormulaEval
        TailBoundPrimitiveS21Compiler.primitiveAtomInterpretation
        (fun _idx => n)
        (compileToBAFormula
          TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler
          (lcmThreePowCertificate n)) ↔
      eval (lcmThreePowCertificate n) := by
  dsimp [compileToBAFormula, lcmThreePowCertificate, eval,
    TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveTarget,
    baFormulaEval]
  rw [TailBoundPrimitiveS21Compiler.primitiveAtomEval_polytimePrimitiveTarget_iff,
    TailBoundPrimitiveS21Compiler.lcmDoubleLeNinePowPureTarget_eval_iff_lcm_bound,
    TailBoundPrimitiveS21Compiler.geometricTailPureTarget_eval_iff]
  simp [TailBoundExpandedPrimitive.eval]

theorem lcmThreePowPureCompiledFormula_sound
    (n : ℕ) :
    baFormulaEval
        TailBoundPrimitiveS21Compiler.primitiveAtomInterpretation
        (fun _idx => n)
        (compileToBAFormula
          TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler
          (lcmThreePowCertificate n)) →
      _root_.tail_bound_certificate_accepted n := by
  intro h
  exact lcmThreePowCertificate_sound n
    ((lcmThreePowPureCompiledFormula_eval_iff n).1 h)

theorem compileLcmThreePowProof_eventually_pure :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ proof : BAProofObject BussS21Axiom,
        proof.conclusion =
          compileToBAFormula
            TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler
            (lcmThreePowCertificate n) ∧
        ((((proof.size + 2 : ℕ) : ℝ)) ≤
          compiledSizeBound
            TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler
            (lcmThreePowCertificate n)) :=
  compileLcmThreePowProof_eventually
    TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler

structure LcmThreePowPureS21Assembly where
  compiler : TailBoundPrimitiveS21Compiler
  compiler_eq :
    compiler =
      TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler
  semantic_alignment :
    TailBoundPrimitiveS21Compiler.SemanticAlignment
      TailBoundPrimitiveS21Compiler.primitiveAtomInterpretation compiler
  lcm_target_atomFree :
    ∀ n : ℕ,
      TailBoundPrimitiveS21Compiler.Pow9TraceCert.baFormulaAtomFree
        (compiler.target TailBoundExpandedPrimitive.lcmDoubleLeNinePow n)
  geometric_target_atomFree :
    ∀ n : ℕ,
      TailBoundPrimitiveS21Compiler.Pow9TraceCert.baFormulaAtomFree
        (compiler.target TailBoundExpandedPrimitive.geometricTailLtOne n)
  compiled_formula_eval_iff :
    ∀ n : ℕ,
      baFormulaEval
          TailBoundPrimitiveS21Compiler.primitiveAtomInterpretation
          (fun _idx => n)
          (compileToBAFormula compiler (lcmThreePowCertificate n)) ↔
        eval (lcmThreePowCertificate n)
  compiled_formula_sound :
    ∀ n : ℕ,
      baFormulaEval
          TailBoundPrimitiveS21Compiler.primitiveAtomInterpretation
          (fun _idx => n)
          (compileToBAFormula compiler (lcmThreePowCertificate n)) →
        _root_.tail_bound_certificate_accepted n
  eventually_compile :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ proof : BAProofObject BussS21Axiom,
        proof.conclusion =
          compileToBAFormula compiler (lcmThreePowCertificate n) ∧
        ((((proof.size + 2 : ℕ) : ℝ)) ≤
          compiledSizeBound compiler (lcmThreePowCertificate n))

def lcmThreePowPureS21Assembly :
    LcmThreePowPureS21Assembly where
  compiler := TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler
  compiler_eq := rfl
  semantic_alignment :=
    TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler_semanticAlignment
  lcm_target_atomFree :=
    TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler_lcm_target_atomFree
  geometric_target_atomFree :=
    TailBoundPrimitiveS21Compiler.lcmThreePowPurePrimitiveCompiler_geometric_target_atomFree
  compiled_formula_eval_iff := lcmThreePowPureCompiledFormula_eval_iff
  compiled_formula_sound := lcmThreePowPureCompiledFormula_sound
  eventually_compile := compileLcmThreePowProof_eventually_pure

/-- Audit-facing semantic-alignment obligation for the closed
polytime-definability primitive compiler.  It is phrased as a named proposition
so later bridge layers can depend on the exact requirement. -/
abbrev PolytimePrimitiveSemanticAlignmentRequired : Prop :=
  TailBoundPrimitiveS21Compiler.SemanticAlignment
    TailBoundPrimitiveS21Compiler.primitiveAtomInterpretation
    TailBoundPrimitiveS21Compiler.polytimeDefinabilityCompiler

theorem polytimePrimitiveSemanticAlignment_closed :
    PolytimePrimitiveSemanticAlignmentRequired :=
  TailBoundPrimitiveS21Compiler.polytimeDefinabilityCompiler_semanticAlignment

end TailBoundExpandedFormula

end ThreePowTailBoundExpandedDefinabilityCompiler

def MainSondowFullCertificateSourceComponentCompilers.productCertificateSystem
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    SondowCertificateSystem
      sondowProjectComponentFormulas.product bounds.product where
  Cert := MainSondowProductLogSourceCertificate
  valid := fun n cert => cert.index = n
  certSize := fun cert =>
    (compilers.productProof cert.index (0 : ℚ) cert.source).size + 2
  proofOfValid := by
    intro n cert hvalid
    cases hvalid
    exact compilers.productProof cert.index (0 : ℚ) cert.source
  proof_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.product_conclusion cert.index (0 : ℚ) cert.source
  proof_size_le_cert_size := by
    intro n cert hvalid
    cases hvalid
    exact Nat.le_refl _
  cert_size_le_bound := by
    intro n cert hvalid
    cases hvalid
    exact compilers.product_size_plus_two_le cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.logCertificateSystem
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    SondowCertificateSystem
      sondowProjectComponentFormulas.logRelation bounds.logRelation where
  Cert := MainSondowProductLogSourceCertificate
  valid := fun n cert => cert.index = n
  certSize := fun cert =>
    (compilers.logProof cert.index (0 : ℚ) cert.source).size + 2
  proofOfValid := by
    intro n cert hvalid
    cases hvalid
    exact compilers.logProof cert.index (0 : ℚ) cert.source
  proof_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.log_conclusion cert.index (0 : ℚ) cert.source
  proof_size_le_cert_size := by
    intro n cert hvalid
    cases hvalid
    exact Nat.le_refl _
  cert_size_le_bound := by
    intro n cert hvalid
    cases hvalid
    exact compilers.log_size_plus_two_le cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.decompositionCertificateSystem
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    SondowCertificateSystem
      sondowProjectComponentFormulas.decomposition bounds.decomposition where
  Cert := MainSondowDecompositionSourceCertificate
  valid := fun n cert => cert.index = n
  certSize := fun cert =>
    (compilers.decompositionProof cert.index (0 : ℚ) cert.source).size + 2
  proofOfValid := by
    intro n cert hvalid
    cases hvalid
    exact compilers.decompositionProof cert.index (0 : ℚ) cert.source
  proof_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.decomposition_conclusion cert.index (0 : ℚ) cert.source
  proof_size_le_cert_size := by
    intro n cert hvalid
    cases hvalid
    exact Nat.le_refl _
  cert_size_le_bound := by
    intro n cert hvalid
    cases hvalid
    exact
      compilers.decomposition_size_plus_two_le
        cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.threePowCertificateSystem
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    SondowCertificateSystem
      sondowProjectComponentFormulas.threePow bounds.threePow where
  Cert := MainSondowThreePowSourceCertificate
  valid := fun n cert => cert.index = n
  certSize := fun cert =>
    (compilers.threePowProof cert.index (0 : ℚ) cert.source).size + 2
  proofOfValid := by
    intro n cert hvalid
    cases hvalid
    exact compilers.threePowProof cert.index (0 : ℚ) cert.source
  proof_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.threePow_conclusion cert.index (0 : ℚ) cert.source
  proof_size_le_cert_size := by
    intro n cert hvalid
    cases hvalid
    exact Nat.le_refl _
  cert_size_le_bound := by
    intro n cert hvalid
    cases hvalid
    exact compilers.threePow_size_plus_two_le cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.payloadCertificateSystem
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    SondowCertificateSystem
      sondowProjectComponentFormulas.payload bounds.payload where
  Cert := MainSondowPayloadSourceCertificate
  valid := fun n cert => cert.index = n
  certSize := fun cert =>
    (compilers.payloadProof cert.index cert.q cert.source).size + 2
  proofOfValid := by
    intro n cert hvalid
    cases hvalid
    exact compilers.payloadProof cert.index cert.q cert.source
  proof_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.payload_conclusion cert.index cert.q cert.source
  proof_size_le_cert_size := by
    intro n cert hvalid
    cases hvalid
    exact Nat.le_refl _
  cert_size_le_bound := by
    intro n cert hvalid
    cases hvalid
    exact compilers.payload_size_plus_two_le cert.index cert.q cert.source

structure MainSondowSourceComponentCertificateSystems
    (bounds : SondowComponentBounds) where
  productSystem :
    SondowCertificateSystem
      sondowProjectComponentFormulas.product bounds.product
  logSystem :
    SondowCertificateSystem
      sondowProjectComponentFormulas.logRelation bounds.logRelation
  decompositionSystem :
    SondowCertificateSystem
      sondowProjectComponentFormulas.decomposition bounds.decomposition
  threePowSystem :
    SondowCertificateSystem
      sondowProjectComponentFormulas.threePow bounds.threePow
  payloadSystem :
    SondowCertificateSystem
      sondowProjectComponentFormulas.payload bounds.payload

def MainSondowFullCertificateSourceComponentCompilers.toSourceCertificateSystems
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    MainSondowSourceComponentCertificateSystems bounds where
  productSystem := compilers.productCertificateSystem
  logSystem := compilers.logCertificateSystem
  decompositionSystem := compilers.decompositionCertificateSystem
  threePowSystem := compilers.threePowCertificateSystem
  payloadSystem := compilers.payloadCertificateSystem

theorem MainSondowFullCertificateSourceComponentCompilers.source_certificates_valid
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    (compilers.toSourceCertificateSystems).productSystem.valid n
        hsource.productLogCertificate ∧
      (compilers.toSourceCertificateSystems).logSystem.valid n
        hsource.productLogCertificate ∧
      (compilers.toSourceCertificateSystems).decompositionSystem.valid n
        hsource.decompositionCertificate ∧
      (compilers.toSourceCertificateSystems).threePowSystem.valid n
        hsource.threePowCertificate ∧
      (compilers.toSourceCertificateSystems).payloadSystem.valid n
        hsource.payloadCertificate := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def MainSondowFullCertificateSourceComponentCompilers.productProofCodeCompiler
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    ComponentProofCodeCompiler
      sondowProjectComponentFormulas.product bounds.product
      sondowProductCode where
  SourceCert := MainSondowProductLogSourceCertificate
  valid := fun n cert => cert.index = n
  sourceCode := sondowProductCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert =>
    (compilers.productProof cert.index (0 : ℚ) cert.source).size + 2
  compile := by
    intro n cert hvalid
    cases hvalid
    exact compilers.productProof cert.index (0 : ℚ) cert.source
  compile_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.product_conclusion cert.index (0 : ℚ) cert.source
  compile_size_plus_two_le := by
    intro n cert hvalid
    cases hvalid
    exact compilers.product_size_plus_two_le cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.logProofCodeCompiler
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    ComponentProofCodeCompiler
      sondowProjectComponentFormulas.logRelation bounds.logRelation
      sondowLogRelationCode where
  SourceCert := MainSondowProductLogSourceCertificate
  valid := fun n cert => cert.index = n
  sourceCode := sondowLogRelationCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert =>
    (compilers.logProof cert.index (0 : ℚ) cert.source).size + 2
  compile := by
    intro n cert hvalid
    cases hvalid
    exact compilers.logProof cert.index (0 : ℚ) cert.source
  compile_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.log_conclusion cert.index (0 : ℚ) cert.source
  compile_size_plus_two_le := by
    intro n cert hvalid
    cases hvalid
    exact compilers.log_size_plus_two_le cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.decompositionProofCodeCompiler
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    ComponentProofCodeCompiler
      sondowProjectComponentFormulas.decomposition bounds.decomposition
      sondowDecompositionCode where
  SourceCert := MainSondowDecompositionSourceCertificate
  valid := fun n cert => cert.index = n
  sourceCode := sondowDecompositionCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert =>
    (compilers.decompositionProof cert.index (0 : ℚ) cert.source).size + 2
  compile := by
    intro n cert hvalid
    cases hvalid
    exact compilers.decompositionProof cert.index (0 : ℚ) cert.source
  compile_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.decomposition_conclusion cert.index (0 : ℚ) cert.source
  compile_size_plus_two_le := by
    intro n cert hvalid
    cases hvalid
    exact
      compilers.decomposition_size_plus_two_le
        cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.threePowProofCodeCompiler
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    ComponentProofCodeCompiler
      sondowProjectComponentFormulas.threePow bounds.threePow
      sondowThreePowCode where
  SourceCert := MainSondowThreePowSourceCertificate
  valid := fun n cert => cert.index = n
  sourceCode := sondowThreePowCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert =>
    (compilers.threePowProof cert.index (0 : ℚ) cert.source).size + 2
  compile := by
    intro n cert hvalid
    cases hvalid
    exact compilers.threePowProof cert.index (0 : ℚ) cert.source
  compile_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.threePow_conclusion cert.index (0 : ℚ) cert.source
  compile_size_plus_two_le := by
    intro n cert hvalid
    cases hvalid
    exact compilers.threePow_size_plus_two_le cert.index (0 : ℚ) cert.source

def MainSondowFullCertificateSourceComponentCompilers.payloadProofCodeCompiler
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    ComponentProofCodeCompiler
      sondowProjectComponentFormulas.payload bounds.payload
      sondowPayloadCode where
  SourceCert := MainSondowPayloadSourceCertificate
  valid := fun n cert => cert.index = n
  sourceCode := sondowPayloadCode
  sourceCode_eq_expected := by
    intro n
    rfl
  sourceSize := fun cert =>
    (compilers.payloadProof cert.index cert.q cert.source).size + 2
  compile := by
    intro n cert hvalid
    cases hvalid
    exact compilers.payloadProof cert.index cert.q cert.source
  compile_conclusion := by
    intro n cert hvalid
    cases hvalid
    exact compilers.payload_conclusion cert.index cert.q cert.source
  compile_size_plus_two_le := by
    intro n cert hvalid
    cases hvalid
    exact compilers.payload_size_plus_two_le cert.index cert.q cert.source

def MainSondowFullCertificateSourceComponentCompilers.toProjectProofCodeCompilers
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    SondowProjectComponentProofCodeCompilers bounds where
  product := compilers.productProofCodeCompiler
  logRelation := compilers.logProofCodeCompiler
  decomposition := compilers.decompositionProofCodeCompiler
  threePow := compilers.threePowProofCodeCompiler
  payload := compilers.payloadProofCodeCompiler

def MainSondowFullCertificateSourceComponentCompilers.projectProofCodeCertificateAt
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    SondowProjectProofCodeCertificateAt
      compilers.toProjectProofCodeCompilers n where
  productCert := hsource.productLogCertificate
  productValid := rfl
  logCert := hsource.productLogCertificate
  logValid := rfl
  decompositionCert := hsource.decompositionCertificate
  decompositionValid := rfl
  threePowCert := hsource.threePowCertificate
  threePowValid := rfl
  payloadCert := hsource.payloadCertificate
  payloadValid := rfl

def MainSondowFullCertificateSourceComponentCompilers.componentCertificateOfSource
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    SondowComponentCertificate :=
  (compilers.projectProofCodeCertificateAt hsource).toComponentCertificate

theorem MainSondowFullCertificateSourceComponentCompilers.componentCertificateOfSource_valid
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    SondowComponentCertificate.ProofObjectSystemValid
      sondowProjectComponentFormulas bounds n
      (compilers.componentCertificateOfSource hsource) :=
  (compilers.projectProofCodeCertificateAt hsource).toComponentCertificate_valid

def MainSondowFullCertificateSourceComponentCompilers.componentCertificateOfFullCertificate
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowComponentCertificate :=
  compilers.componentCertificateOfSource
    ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

theorem MainSondowFullCertificateSourceComponentCompilers.componentCertificateOfFullCertificate_valid
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowComponentCertificate.ProofObjectSystemValid
      sondowProjectComponentFormulas bounds n
      (compilers.componentCertificateOfFullCertificate hchecked) :=
  compilers.componentCertificateOfSource_valid
    ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

def MainSondowFullCertificateSourceComponentCompilers.toFullCertificateComponentProofCompiler
    {bounds : SondowComponentBounds}
    (compilers :
      MainSondowFullCertificateSourceComponentCompilers bounds) :
    MainSondowFullCertificateComponentProofCompiler bounds where
  productProof := by
    intro n q hchecked
    exact compilers.productProof n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).productLogSource
  logProof := by
    intro n q hchecked
    exact compilers.logProof n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).productLogSource
  decompositionProof := by
    intro n q hchecked
    exact compilers.decompositionProof n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).decompositionSource
  threePowProof := by
    intro n q hchecked
    exact compilers.threePowProof n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).threePowSource
  payloadProof := by
    intro n q hchecked
    let hsource :=
      (mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked
    exact compilers.payloadProof n q
      ⟨hsource.gamma_eq, hsource.denominatorSource⟩
  product_conclusion := by
    intro n q hchecked
    exact compilers.product_conclusion n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).productLogSource
  log_conclusion := by
    intro n q hchecked
    exact compilers.log_conclusion n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).productLogSource
  decomposition_conclusion := by
    intro n q hchecked
    exact compilers.decomposition_conclusion n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).decompositionSource
  threePow_conclusion := by
    intro n q hchecked
    exact compilers.threePow_conclusion n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).threePowSource
  payload_conclusion := by
    intro n q hchecked
    let hsource :=
      (mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked
    exact compilers.payload_conclusion n q
      ⟨hsource.gamma_eq, hsource.denominatorSource⟩
  product_size_plus_two_le := by
    intro n q hchecked
    exact compilers.product_size_plus_two_le n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).productLogSource
  log_size_plus_two_le := by
    intro n q hchecked
    exact compilers.log_size_plus_two_le n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).productLogSource
  decomposition_size_plus_two_le := by
    intro n q hchecked
    exact compilers.decomposition_size_plus_two_le n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).decompositionSource
  threePow_size_plus_two_le := by
    intro n q hchecked
    exact compilers.threePow_size_plus_two_le n q
      ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
        hchecked).threePowSource
  payload_size_plus_two_le := by
    intro n q hchecked
    let hsource :=
      (mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked
    exact compilers.payload_size_plus_two_le n q
      ⟨hsource.gamma_eq, hsource.denominatorSource⟩

def MainSondowFullCertificateComponentProofCompiler.toTraceCompiler
    {bounds : SondowComponentBounds}
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds) :
    ExternalCheckedCodeToProjectComponentProofCertificateTraces
      mainSondowFullCertificateCheckedCodeSemantics bounds where
  productTraceOfChecked := by
    intro n q hchecked
    exact proofObjectAcceptedTrace
      (compiler.productProof n q.down hchecked)
      (compiler.product_conclusion n q.down hchecked)
      (compiler.product_size_plus_two_le n q.down hchecked)
  logTraceOfChecked := by
    intro n q hchecked
    exact proofObjectAcceptedTrace
      (compiler.logProof n q.down hchecked)
      (compiler.log_conclusion n q.down hchecked)
      (compiler.log_size_plus_two_le n q.down hchecked)
  decompositionTraceOfChecked := by
    intro n q hchecked
    exact proofObjectAcceptedTrace
      (compiler.decompositionProof n q.down hchecked)
      (compiler.decomposition_conclusion n q.down hchecked)
      (compiler.decomposition_size_plus_two_le n q.down hchecked)
  threePowTraceOfChecked := by
    intro n q hchecked
    exact proofObjectAcceptedTrace
      (compiler.threePowProof n q.down hchecked)
      (compiler.threePow_conclusion n q.down hchecked)
      (compiler.threePow_size_plus_two_le n q.down hchecked)
  payloadTraceOfChecked := by
    intro n q hchecked
    exact proofObjectAcceptedTrace
      (compiler.payloadProof n q.down hchecked)
      (compiler.payload_conclusion n q.down hchecked)
      (compiler.payload_size_plus_two_le n q.down hchecked)

/-- Eventual version of the full-certificate compiler.  This is the form most
closely matched to the Sondow forward route: rationality gives eventual accepted
certificates, so only the tail must be compiled into project proof objects. -/
structure MainSondowEventualFullCertificateComponentProofCompiler
    (bounds : SondowComponentBounds) where
  threshold : ℕ
  productProof :
    ∀ n : ℕ, ∀ q : ℚ, threshold ≤ n →
      mainSondowFullCertificateChecks q n →
        BAProofObject BussS21Axiom
  logProof :
    ∀ n : ℕ, ∀ q : ℚ, threshold ≤ n →
      mainSondowFullCertificateChecks q n →
        BAProofObject BussS21Axiom
  decompositionProof :
    ∀ n : ℕ, ∀ q : ℚ, threshold ≤ n →
      mainSondowFullCertificateChecks q n →
        BAProofObject BussS21Axiom
  threePowProof :
    ∀ n : ℕ, ∀ q : ℚ, threshold ≤ n →
      mainSondowFullCertificateChecks q n →
        BAProofObject BussS21Axiom
  payloadProof :
    ∀ n : ℕ, ∀ q : ℚ, threshold ≤ n →
      mainSondowFullCertificateChecks q n →
        BAProofObject BussS21Axiom
  product_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      (productProof n q hn hchecked).conclusion =
        sondowProjectComponentFormulas.product n
  log_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      (logProof n q hn hchecked).conclusion =
        sondowProjectComponentFormulas.logRelation n
  decomposition_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      (decompositionProof n q hn hchecked).conclusion =
        sondowProjectComponentFormulas.decomposition n
  threePow_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      (threePowProof n q hn hchecked).conclusion =
        sondowProjectComponentFormulas.threePow n
  payload_conclusion :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      (payloadProof n q hn hchecked).conclusion =
        sondowProjectComponentFormulas.payload n
  product_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((productProof n q hn hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.product n
  log_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((logProof n q hn hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.logRelation n
  decomposition_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((decompositionProof n q hn hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.decomposition n
  threePow_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((threePowProof n q hn hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.threePow n
  payload_size_plus_two_le :
    ∀ n : ℕ, ∀ q : ℚ, ∀ hn : threshold ≤ n,
      ∀ hchecked : mainSondowFullCertificateChecks q n,
      ((((payloadProof n q hn hchecked).size + 2 : ℕ) : ℝ)) ≤
        bounds.payload n

def MainSondowFullCertificateComponentProofCompiler.toEventualCompiler
    {bounds : SondowComponentBounds}
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds) :
    MainSondowEventualFullCertificateComponentProofCompiler bounds where
  threshold := 0
  productProof := fun n q _hn hchecked =>
    compiler.productProof n q hchecked
  logProof := fun n q _hn hchecked =>
    compiler.logProof n q hchecked
  decompositionProof := fun n q _hn hchecked =>
    compiler.decompositionProof n q hchecked
  threePowProof := fun n q _hn hchecked =>
    compiler.threePowProof n q hchecked
  payloadProof := fun n q _hn hchecked =>
    compiler.payloadProof n q hchecked
  product_conclusion := fun n q _hn hchecked =>
    compiler.product_conclusion n q hchecked
  log_conclusion := fun n q _hn hchecked =>
    compiler.log_conclusion n q hchecked
  decomposition_conclusion := fun n q _hn hchecked =>
    compiler.decomposition_conclusion n q hchecked
  threePow_conclusion := fun n q _hn hchecked =>
    compiler.threePow_conclusion n q hchecked
  payload_conclusion := fun n q _hn hchecked =>
    compiler.payload_conclusion n q hchecked
  product_size_plus_two_le := fun n q _hn hchecked =>
    compiler.product_size_plus_two_le n q hchecked
  log_size_plus_two_le := fun n q _hn hchecked =>
    compiler.log_size_plus_two_le n q hchecked
  decomposition_size_plus_two_le := fun n q _hn hchecked =>
    compiler.decomposition_size_plus_two_le n q hchecked
  threePow_size_plus_two_le := fun n q _hn hchecked =>
    compiler.threePow_size_plus_two_le n q hchecked
  payload_size_plus_two_le := fun n q _hn hchecked =>
    compiler.payload_size_plus_two_le n q hchecked

noncomputable def
    MainSondowEventualFullCertificateComponentProofCompiler.toProjectProofObjectCertificates
    {bounds : SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds) :
    SondowRationalityToProjectProofObjectCertificates
      (mainGammaRationalityContext
        (_root_.is_rational _root_.euler_mascheroni))
      bounds where
  certificates_of_rationality := by
    intro hrat
    rcases
      _root_.accepted_sondow_certificate_eventual_of_rationality_reproof
        hrat with
      ⟨Naccepted, hNaccepted⟩
    refine ⟨max compiler.threshold Naccepted, ?_⟩
    intro n hn
    have htail : compiler.threshold ≤ n :=
      le_trans (Nat.le_max_left compiler.threshold Naccepted) hn
    have haccepted_tail : Naccepted ≤ n :=
      le_trans (Nat.le_max_right compiler.threshold Naccepted) hn
    have haccepted : mainSondowAcceptedAt n :=
      hNaccepted n haccepted_tail
    rcases haccepted with ⟨q, hchecked⟩
    let cert : SondowComponentCertificate :=
      { productProof :=
          compiler.productProof n q htail hchecked
        logProof :=
          compiler.logProof n q htail hchecked
        decompositionProof :=
          compiler.decompositionProof n q htail hchecked
        threePowProof :=
          compiler.threePowProof n q htail hchecked
        payloadProof :=
          compiler.payloadProof n q htail hchecked }
    refine ⟨cert, ?_⟩
    exact
      { product_conclusion :=
          compiler.product_conclusion n q htail hchecked
        log_conclusion :=
          compiler.log_conclusion n q htail hchecked
        decomposition_conclusion :=
          compiler.decomposition_conclusion n q htail hchecked
        threePow_conclusion :=
          compiler.threePow_conclusion n q htail hchecked
        payload_conclusion :=
          compiler.payload_conclusion n q htail hchecked
        product_size_plus_two_le :=
          compiler.product_size_plus_two_le n q htail hchecked
        log_size_plus_two_le :=
          compiler.log_size_plus_two_le n q htail hchecked
        decomposition_size_plus_two_le :=
          compiler.decomposition_size_plus_two_le n q htail hchecked
        threePow_size_plus_two_le :=
          compiler.threePow_size_plus_two_le n q htail hchecked
        payload_size_plus_two_le :=
          compiler.payload_size_plus_two_le n q htail hchecked }

/-- Five component-level definability bridges, one for each Sondow project atom. -/
structure SondowProjectAtomDefinabilityBridges
    (bounds : SondowComponentBounds) where
  product :
    ProjectAtomDefinabilityBridge
      sondowProjectComponentFormulas.product bounds.product
  logRelation :
    ProjectAtomDefinabilityBridge
      sondowProjectComponentFormulas.logRelation bounds.logRelation
  decomposition :
    ProjectAtomDefinabilityBridge
      sondowProjectComponentFormulas.decomposition bounds.decomposition
  threePow :
    ProjectAtomDefinabilityBridge
      sondowProjectComponentFormulas.threePow bounds.threePow
  payload :
    ProjectAtomDefinabilityBridge
      sondowProjectComponentFormulas.payload bounds.payload

def sondowComponentBoundsAddConst
    (bounds : SondowComponentBounds) (C : ℝ) :
    SondowComponentBounds where
  product := fun n => bounds.product n + C
  logRelation := fun n => bounds.logRelation n + C
  decomposition := fun n => bounds.decomposition n + C
  threePow := fun n => bounds.threePow n + C
  payload := fun n => bounds.payload n + C
  product_poly := bounds.product_poly.add_const C
  log_poly := bounds.log_poly.add_const C
  decomposition_poly := bounds.decomposition_poly.add_const C
  threePow_poly := bounds.threePow_poly.add_const C
  payload_poly := bounds.payload_poly.add_const C

def SondowProjectAtomDefinabilityBridges.toEventualFullCertificateComponentProofCompiler
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectAtomDefinabilityBridges bounds) :
    MainSondowEventualFullCertificateComponentProofCompiler bounds where
  threshold := 0
  productProof := fun n _q _hn _hchecked =>
    bridges.product.proofObject n
  logProof := fun n _q _hn _hchecked =>
    bridges.logRelation.proofObject n
  decompositionProof := fun n _q _hn _hchecked =>
    bridges.decomposition.proofObject n
  threePowProof := fun n _q _hn _hchecked =>
    bridges.threePow.proofObject n
  payloadProof := fun n _q _hn _hchecked =>
    bridges.payload.proofObject n
  product_conclusion := fun n _q _hn _hchecked =>
    bridges.product.proofObject_conclusion n
  log_conclusion := fun n _q _hn _hchecked =>
    bridges.logRelation.proofObject_conclusion n
  decomposition_conclusion := fun n _q _hn _hchecked =>
    bridges.decomposition.proofObject_conclusion n
  threePow_conclusion := fun n _q _hn _hchecked =>
    bridges.threePow.proofObject_conclusion n
  payload_conclusion := fun n _q _hn _hchecked =>
    bridges.payload.proofObject_conclusion n
  product_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.product.proofObject_size_plus_two_le n
  log_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.logRelation.proofObject_size_plus_two_le n
  decomposition_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.decomposition.proofObject_size_plus_two_le n
  threePow_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.threePow.proofObject_size_plus_two_le n
  payload_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.payload.proofObject_size_plus_two_le n

def SondowProjectAtomDefinabilityBridges.toFullCertificateComponentProofCompiler
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectAtomDefinabilityBridges bounds) :
    MainSondowFullCertificateComponentProofCompiler bounds where
  productProof := fun n _q _hchecked =>
    bridges.product.proofObject n
  logProof := fun n _q _hchecked =>
    bridges.logRelation.proofObject n
  decompositionProof := fun n _q _hchecked =>
    bridges.decomposition.proofObject n
  threePowProof := fun n _q _hchecked =>
    bridges.threePow.proofObject n
  payloadProof := fun n _q _hchecked =>
    bridges.payload.proofObject n
  product_conclusion := fun n _q _hchecked =>
    bridges.product.proofObject_conclusion n
  log_conclusion := fun n _q _hchecked =>
    bridges.logRelation.proofObject_conclusion n
  decomposition_conclusion := fun n _q _hchecked =>
    bridges.decomposition.proofObject_conclusion n
  threePow_conclusion := fun n _q _hchecked =>
    bridges.threePow.proofObject_conclusion n
  payload_conclusion := fun n _q _hchecked =>
    bridges.payload.proofObject_conclusion n
  product_size_plus_two_le := fun n _q _hchecked =>
    bridges.product.proofObject_size_plus_two_le n
  log_size_plus_two_le := fun n _q _hchecked =>
    bridges.logRelation.proofObject_size_plus_two_le n
  decomposition_size_plus_two_le := fun n _q _hchecked =>
    bridges.decomposition.proofObject_size_plus_two_le n
  threePow_size_plus_two_le := fun n _q _hchecked =>
    bridges.threePow.proofObject_size_plus_two_le n
  payload_size_plus_two_le := fun n _q _hchecked =>
    bridges.payload.proofObject_size_plus_two_le n

/-- Five direct project-atom proof bridges.  This is the constructor-level
bounded-arithmetic proof-object obligation without the definability transport
presentation. -/
structure SondowProjectDirectAtomProofBridges
    (bounds : SondowComponentBounds) where
  product :
    DirectProjectAtomProofBridge
      sondowProjectComponentFormulas.product bounds.product
  logRelation :
    DirectProjectAtomProofBridge
      sondowProjectComponentFormulas.logRelation bounds.logRelation
  decomposition :
    DirectProjectAtomProofBridge
      sondowProjectComponentFormulas.decomposition bounds.decomposition
  threePow :
    DirectProjectAtomProofBridge
      sondowProjectComponentFormulas.threePow bounds.threePow
  payload :
    DirectProjectAtomProofBridge
      sondowProjectComponentFormulas.payload bounds.payload

def SondowProjectAtomDefinabilityBridges.toDirectAtomProofBridges
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectAtomDefinabilityBridges bounds) :
    SondowProjectDirectAtomProofBridges bounds where
  product := bridges.product.toDirectProofBridge
  logRelation := bridges.logRelation.toDirectProofBridge
  decomposition := bridges.decomposition.toDirectProofBridge
  threePow := bridges.threePow.toDirectProofBridge
  payload := bridges.payload.toDirectProofBridge

theorem
    sondowProjectAtomDefinabilityBridges_nonempty_to_directAtomProofBridges_nonempty
    {bounds : SondowComponentBounds} :
    Nonempty (SondowProjectAtomDefinabilityBridges bounds) →
      Nonempty (SondowProjectDirectAtomProofBridges bounds) := by
  intro hbridges
  rcases hbridges with ⟨bridges⟩
  exact ⟨bridges.toDirectAtomProofBridges⟩

theorem
    sondowProjectAtomDefinabilityBridges_nonempty_to_fullCompiler_nonempty
    {bounds : SondowComponentBounds} :
    Nonempty (SondowProjectAtomDefinabilityBridges bounds) →
      Nonempty (MainSondowFullCertificateComponentProofCompiler bounds) := by
  intro hbridges
  rcases hbridges with ⟨bridges⟩
  exact ⟨bridges.toFullCertificateComponentProofCompiler⟩

def SondowProjectDirectAtomProofBridges.toFullCertificateComponentProofCompiler
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectDirectAtomProofBridges bounds) :
    MainSondowFullCertificateComponentProofCompiler bounds where
  productProof := fun n _q _hchecked =>
    bridges.product.proof n
  logProof := fun n _q _hchecked =>
    bridges.logRelation.proof n
  decompositionProof := fun n _q _hchecked =>
    bridges.decomposition.proof n
  threePowProof := fun n _q _hchecked =>
    bridges.threePow.proof n
  payloadProof := fun n _q _hchecked =>
    bridges.payload.proof n
  product_conclusion := fun n _q _hchecked =>
    bridges.product.proof_conclusion n
  log_conclusion := fun n _q _hchecked =>
    bridges.logRelation.proof_conclusion n
  decomposition_conclusion := fun n _q _hchecked =>
    bridges.decomposition.proof_conclusion n
  threePow_conclusion := fun n _q _hchecked =>
    bridges.threePow.proof_conclusion n
  payload_conclusion := fun n _q _hchecked =>
    bridges.payload.proof_conclusion n
  product_size_plus_two_le := fun n _q _hchecked =>
    bridges.product.proof_size_plus_two_le n
  log_size_plus_two_le := fun n _q _hchecked =>
    bridges.logRelation.proof_size_plus_two_le n
  decomposition_size_plus_two_le := fun n _q _hchecked =>
    bridges.decomposition.proof_size_plus_two_le n
  threePow_size_plus_two_le := fun n _q _hchecked =>
    bridges.threePow.proof_size_plus_two_le n
  payload_size_plus_two_le := fun n _q _hchecked =>
    bridges.payload.proof_size_plus_two_le n

theorem
    sondowProjectDirectAtomProofBridges_nonempty_to_fullCompiler_nonempty
    {bounds : SondowComponentBounds} :
    Nonempty (SondowProjectDirectAtomProofBridges bounds) →
      Nonempty (MainSondowFullCertificateComponentProofCompiler bounds) := by
  intro hbridges
  rcases hbridges with ⟨bridges⟩
  exact ⟨bridges.toFullCertificateComponentProofCompiler⟩

def SondowProjectDirectAtomProofBridges.toEventualFullCertificateComponentProofCompiler
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectDirectAtomProofBridges bounds) :
    MainSondowEventualFullCertificateComponentProofCompiler bounds where
  threshold := 0
  productProof := fun n _q _hn _hchecked =>
    bridges.product.proof n
  logProof := fun n _q _hn _hchecked =>
    bridges.logRelation.proof n
  decompositionProof := fun n _q _hn _hchecked =>
    bridges.decomposition.proof n
  threePowProof := fun n _q _hn _hchecked =>
    bridges.threePow.proof n
  payloadProof := fun n _q _hn _hchecked =>
    bridges.payload.proof n
  product_conclusion := fun n _q _hn _hchecked =>
    bridges.product.proof_conclusion n
  log_conclusion := fun n _q _hn _hchecked =>
    bridges.logRelation.proof_conclusion n
  decomposition_conclusion := fun n _q _hn _hchecked =>
    bridges.decomposition.proof_conclusion n
  threePow_conclusion := fun n _q _hn _hchecked =>
    bridges.threePow.proof_conclusion n
  payload_conclusion := fun n _q _hn _hchecked =>
    bridges.payload.proof_conclusion n
  product_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.product.proof_size_plus_two_le n
  log_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.logRelation.proof_size_plus_two_le n
  decomposition_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.decomposition.proof_size_plus_two_le n
  threePow_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.threePow.proof_size_plus_two_le n
  payload_size_plus_two_le := fun n _q _hn _hchecked =>
    bridges.payload.proof_size_plus_two_le n

def SondowProjectDirectAtomProofBridges.toDefinabilityBridgesWithOverhead
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectDirectAtomProofBridges bounds) :
    SondowProjectAtomDefinabilityBridges
      (sondowComponentBoundsAddConst bounds 3) where
  product :=
    bridges.product.toDefinabilityBridgeWithOverhead 0
      sondowProjectComponentFormulas.product (by intro n; rfl)
  logRelation :=
    bridges.logRelation.toDefinabilityBridgeWithOverhead 1
      sondowProjectComponentFormulas.logRelation (by intro n; rfl)
  decomposition :=
    bridges.decomposition.toDefinabilityBridgeWithOverhead 2
      sondowProjectComponentFormulas.decomposition (by intro n; rfl)
  threePow :=
    bridges.threePow.toDefinabilityBridgeWithOverhead 3
      sondowProjectComponentFormulas.threePow (by intro n; rfl)
  payload :=
    bridges.payload.toDefinabilityBridgeWithOverhead 4
      sondowProjectComponentFormulas.payload (by intro n; rfl)

theorem
    sondowProjectDirectAtomProofBridges_nonempty_to_definabilityBridges_nonempty_with_overhead
    {bounds : SondowComponentBounds} :
    Nonempty (SondowProjectDirectAtomProofBridges bounds) →
      Nonempty
        (SondowProjectAtomDefinabilityBridges
          (sondowComponentBoundsAddConst bounds 3)) := by
  intro hbridges
  rcases hbridges with ⟨bridges⟩
  exact ⟨bridges.toDefinabilityBridgesWithOverhead⟩

/-- Audit fact: main `AcceptedCertificateCodeSemantics` is a strong total
proof-code semantics on its relevant fragment.  For the Sondow certificate
family, supplying it for the whole family already implies every Sondow
certificate is accepted.  This is why the sidecar bridge uses the weaker
index-based `accepted n ↔ ∃ checked code at n` interface as the natural target. -/
theorem accepted_all_of_main_sondow_accepted_code_semantics
    (hsem :
      _root_.AcceptedCertificateCodeSemantics.{u}
        _root_.sondowCertificateValidCode) :
    ∀ n : ℕ, mainSondowAcceptedAt n := by
  intro n
  rcases hsem.proof_code_semantics.complete
      (_root_.sondowCertificateValidCode n)
      (hsem.relevant_family n) with ⟨c, hchecks⟩
  exact hsem.accepted_of_checked hchecks

/-- Main-library accepted-code semantics induces the sidecar's index-based
accepted/checked-code semantics. -/
def externalAcceptedCheckedCodeSemanticsOfMain
    (hsem :
      _root_.AcceptedCertificateCodeSemantics.{u}
        _root_.sondowCertificateValidCode) :
    ExternalAcceptedCheckedCodeSemantics.{u} mainSondowAcceptedAt where
  Code := hsem.proof_code_semantics.Code
  checksAt := fun c n =>
    hsem.proof_code_semantics.checks c
      (_root_.sondowCertificateValidCode n)
  size := hsem.proof_code_semantics.size
  accepted_iff_checked_at := by
    intro n
    constructor
    · intro haccepted
      exact hsem.has_code_of_accepted haccepted
    · intro hchecked
      rcases hchecked with ⟨c, hc⟩
      exact hsem.accepted_of_checked hc

/-- The audit-clean main-side package still required to feed the sidecar.  Its
semantic field says exactly
`accepted n ↔ ∃ checked code at n`, and the compiler turns such checked codes
into the five sidecar proof-certificate traces. -/
structure MainSondowConditionalCheckedCodeTraceBridge
    (bounds : SondowComponentBounds) where
  codeSemantics :
    ExternalAcceptedCheckedCodeSemantics.{u} mainSondowAcceptedAt
  traceCompiler :
    ExternalCheckedCodeToProjectComponentProofCertificateTraces
      codeSemantics bounds

def MainSondowConditionalCheckedCodeTraceBridge.toExternalPackage
    {bounds : SondowComponentBounds}
    (h : MainSondowConditionalCheckedCodeTraceBridge.{u} bounds) :
    ExternalAcceptedCheckedCodeToProjectComponentTracePackage
      mainSondowAcceptedAt bounds where
  codeSemantics := h.codeSemantics
  traceCompiler := h.traceCompiler

noncomputable def MainSondowConditionalCheckedCodeTraceBridge.toComponentTraces
    {bounds : SondowComponentBounds}
    (h : MainSondowConditionalCheckedCodeTraceBridge.{u} bounds) :
    AcceptedToProjectComponentProofCertificateTraces
      mainSondowAcceptedAt bounds :=
  h.toExternalPackage.toComponentTraces

def MainSondowFullCertificateComponentProofCompiler.toConditionalBridge
    {bounds : SondowComponentBounds}
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds) :
    MainSondowConditionalCheckedCodeTraceBridge.{u} bounds where
  codeSemantics := mainSondowFullCertificateCheckedCodeSemantics
  traceCompiler := compiler.toTraceCompiler

theorem MainSondowConditionalCheckedCodeTraceBridge.accepted_iff_checked_code
    {bounds : SondowComponentBounds}
    (h : MainSondowConditionalCheckedCodeTraceBridge.{u} bounds)
    (n : ℕ) :
    mainSondowAcceptedAt n ↔
      ∃ c : h.codeSemantics.Code, h.codeSemantics.checksAt c n :=
  h.codeSemantics.accepted_iff_checked_at n

theorem
    mainSondowConditionalCheckedCodeTraceBridge_nonempty_iff_externalPackage_nonempty
    {bounds : SondowComponentBounds} :
    Nonempty
      (MainSondowConditionalCheckedCodeTraceBridge.{u} bounds) ↔
      Nonempty
        (ExternalAcceptedCheckedCodeToProjectComponentTracePackage.{u}
          mainSondowAcceptedAt bounds) := by
  constructor
  · intro hbridge
    rcases hbridge with ⟨bridge⟩
    exact ⟨bridge.toExternalPackage⟩
  · intro hpkg
    rcases hpkg with ⟨pkg⟩
    exact ⟨{
      codeSemantics := pkg.codeSemantics
      traceCompiler := pkg.traceCompiler }⟩

theorem
    mainSondowConditionalCheckedCodeTraceBridge_nonempty_iff_componentTraces_nonempty
    {bounds : SondowComponentBounds} :
    Nonempty
      (MainSondowConditionalCheckedCodeTraceBridge.{u} bounds) ↔
      Nonempty
        (AcceptedToProjectComponentProofCertificateTraces
          mainSondowAcceptedAt bounds) :=
    (mainSondowConditionalCheckedCodeTraceBridge_nonempty_iff_externalPackage_nonempty
      (bounds := bounds)).trans
    (externalCheckedCodeTracePackage_nonempty_iff_componentTraces_nonempty.{u}
      (Accepted := mainSondowAcceptedAt) (bounds := bounds))

theorem not_rational_of_main_sondow_conditional_checked_code_trace_bridge
    {bounds : SondowComponentBounds}
    (bridge : MainSondowConditionalCheckedCodeTraceBridge.{u} bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_main_rationality_of_external_checked_code_trace_package
    (MainRationality := _root_.is_rational _root_.euler_mascheroni)
    (Accepted := mainSondowAcceptedAt)
    _root_.accepted_sondow_certificate_eventual_of_rationality_reproof
    bridge.toExternalPackage
    calibration

theorem not_rational_of_main_sondow_full_certificate_component_proof_compiler
    {bounds : SondowComponentBounds}
    (compiler :
      MainSondowFullCertificateComponentProofCompiler bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_rational_of_main_sondow_conditional_checked_code_trace_bridge.{0}
    (bridge :=
      (compiler.toConditionalBridge :
        MainSondowConditionalCheckedCodeTraceBridge.{0} bounds))
    calibration

/-- Minimal audit-facing upper-side input package.  This is the natural
certificate route: an accepted full Sondow certificate is compiled into the five
project component `BAProofObject`s, and the lower side is the exact Buss/Pudlak
formula-length calibration for the same reflection-graft target. -/
structure SondowProjectFullCertificateCollisionInputs where
  bounds : SondowComponentBounds
  compiler : MainSondowFullCertificateComponentProofCompiler bounds
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      sondowProjectComponentFormulas.target sondowProjectComponentCode

namespace SondowProjectFullCertificateCollisionInputs

def toConditionalCheckedCodeTraceBridge
    (h : SondowProjectFullCertificateCollisionInputs) :
    MainSondowConditionalCheckedCodeTraceBridge.{u} h.bounds :=
  h.compiler.toConditionalBridge

def lowerSource
    (h : SondowProjectFullCertificateCollisionInputs) :
    BussPudlakTheorem5PALowerBoundSource :=
  h.calibration.lower_source

theorem formula_code_calibrated
    (h : SondowProjectFullCertificateCollisionInputs) (n : ℕ) :
    rescaledExternalPudlakCode
        h.lowerSource.conditions.scale_data.scale n =
      sondowProjectComponentCode (sondowProjectComponentFormulas.target n) :=
  h.calibration.formula_code_eq n

theorem target_code_eq
    (_h : SondowProjectFullCertificateCollisionInputs) (n : ℕ) :
    sondowProjectComponentCode (sondowProjectComponentFormulas.target n) =
      BoundedArithmeticLab.sondowReflectionGraftCode n := by
  exact sondowProjectComponentCode_target n

theorem length_calibrated
    (h : SondowProjectFullCertificateCollisionInputs) (n : ℕ) :
    h.lowerSource.pa_length n =
      semanticBAProofLength PAAxiom sondowProjectComponentFormulas.target n :=
  h.calibration.length_eq n

theorem accepted_iff_checked_code
    (h : SondowProjectFullCertificateCollisionInputs) (n : ℕ) :
    mainSondowAcceptedAt n ↔
      ∃ c : h.toConditionalCheckedCodeTraceBridge.codeSemantics.Code,
        h.toConditionalCheckedCodeTraceBridge.codeSemantics.checksAt c n :=
  h.toConditionalCheckedCodeTraceBridge.accepted_iff_checked_code n

theorem not_rational
    (h : SondowProjectFullCertificateCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_rational_of_main_sondow_full_certificate_component_proof_compiler
    h.compiler h.calibration

end SondowProjectFullCertificateCollisionInputs

theorem not_rational_of_sondow_project_full_certificate_collision_inputs
    (h : SondowProjectFullCertificateCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational

/-- Audit-facing package at the exact source-component layer.  This states the
current hard upper-side obligation without strengthening it to unconditional
project-atom proof bridges: the compiler may use precisely the source
proposition extracted from a checked full Sondow certificate. -/
structure SondowProjectSourceComponentCollisionInputs where
  bounds : SondowComponentBounds
  sourceCompilers : MainSondowFullCertificateSourceComponentCompilers bounds
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      sondowProjectComponentFormulas.target sondowProjectComponentCode

namespace SondowProjectSourceComponentCollisionInputs

def toFullCertificateComponentProofCompiler
    (h : SondowProjectSourceComponentCollisionInputs) :
    MainSondowFullCertificateComponentProofCompiler h.bounds :=
  h.sourceCompilers.toFullCertificateComponentProofCompiler

def toFullCertificateCollisionInputs
    (h : SondowProjectSourceComponentCollisionInputs) :
    SondowProjectFullCertificateCollisionInputs where
  bounds := h.bounds
  compiler := h.toFullCertificateComponentProofCompiler
  calibration := h.calibration

def sourceCertificateSystems
    (h : SondowProjectSourceComponentCollisionInputs) :
    MainSondowSourceComponentCertificateSystems h.bounds :=
  h.sourceCompilers.toSourceCertificateSystems

def projectProofCodeCompilers
    (h : SondowProjectSourceComponentCollisionInputs) :
    SondowProjectComponentProofCodeCompilers h.bounds :=
  h.sourceCompilers.toProjectProofCodeCompilers

theorem full_certificate_iff_source_components
    (_h : SondowProjectSourceComponentCollisionInputs) (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  mainSondowFullCertificateChecks_iff_sourceComponents q n

theorem source_certificates_valid
    (h : SondowProjectSourceComponentCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    h.sourceCertificateSystems.productSystem.valid n
        hsource.productLogCertificate ∧
      h.sourceCertificateSystems.logSystem.valid n
        hsource.productLogCertificate ∧
      h.sourceCertificateSystems.decompositionSystem.valid n
        hsource.decompositionCertificate ∧
      h.sourceCertificateSystems.threePowSystem.valid n
        hsource.threePowCertificate ∧
      h.sourceCertificateSystems.payloadSystem.valid n
        hsource.payloadCertificate :=
  h.sourceCompilers.source_certificates_valid hsource

theorem source_certificates_valid_of_full_certificate
    (h : SondowProjectSourceComponentCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    h.sourceCertificateSystems.productSystem.valid n
        (((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
          hchecked).productLogCertificate) ∧
      h.sourceCertificateSystems.logSystem.valid n
        (((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
          hchecked).productLogCertificate) ∧
      h.sourceCertificateSystems.decompositionSystem.valid n
        (((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
          hchecked).decompositionCertificate) ∧
      h.sourceCertificateSystems.threePowSystem.valid n
        (((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
          hchecked).threePowCertificate) ∧
      h.sourceCertificateSystems.payloadSystem.valid n
        (((mainSondowFullCertificateChecks_iff_sourceComponents q n).1
          hchecked).payloadCertificate) :=
  h.source_certificates_valid
    ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

def projectProofCodeCertificateAtOfSource
    (h : SondowProjectSourceComponentCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hsource : MainSondowFullCertificateSourceComponents q n) :
    SondowProjectProofCodeCertificateAt
      h.projectProofCodeCompilers n :=
  h.sourceCompilers.projectProofCodeCertificateAt hsource

def projectProofCodeCertificateAtOfFullCertificate
    (h : SondowProjectSourceComponentCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowProjectProofCodeCertificateAt
      h.projectProofCodeCompilers n :=
  h.projectProofCodeCertificateAtOfSource
    ((mainSondowFullCertificateChecks_iff_sourceComponents q n).1 hchecked)

def componentCertificateOfFullCertificate
    (h : SondowProjectSourceComponentCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowComponentCertificate :=
  h.sourceCompilers.componentCertificateOfFullCertificate hchecked

theorem componentCertificateOfFullCertificate_valid
    (h : SondowProjectSourceComponentCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowComponentCertificate.ProofObjectSystemValid
      sondowProjectComponentFormulas h.bounds n
      (h.componentCertificateOfFullCertificate hchecked) :=
  h.sourceCompilers.componentCertificateOfFullCertificate_valid hchecked

def lowerSource
    (h : SondowProjectSourceComponentCollisionInputs) :
    BussPudlakTheorem5PALowerBoundSource :=
  h.calibration.lower_source

theorem formula_code_calibrated
    (h : SondowProjectSourceComponentCollisionInputs) (n : ℕ) :
    rescaledExternalPudlakCode
        h.lowerSource.conditions.scale_data.scale n =
      sondowProjectComponentCode (sondowProjectComponentFormulas.target n) :=
  h.calibration.formula_code_eq n

theorem target_code_eq
    (_h : SondowProjectSourceComponentCollisionInputs) (n : ℕ) :
    sondowProjectComponentCode (sondowProjectComponentFormulas.target n) =
      BoundedArithmeticLab.sondowReflectionGraftCode n := by
  exact sondowProjectComponentCode_target n

theorem length_calibrated
    (h : SondowProjectSourceComponentCollisionInputs) (n : ℕ) :
    h.lowerSource.pa_length n =
      semanticBAProofLength PAAxiom sondowProjectComponentFormulas.target n :=
  h.calibration.length_eq n

theorem accepted_iff_checked_code
    (h : SondowProjectSourceComponentCollisionInputs) (n : ℕ) :
    mainSondowAcceptedAt n ↔
      ∃ c : h.toFullCertificateCollisionInputs.toConditionalCheckedCodeTraceBridge.codeSemantics.Code,
        h.toFullCertificateCollisionInputs.toConditionalCheckedCodeTraceBridge.codeSemantics.checksAt c n :=
  h.toFullCertificateCollisionInputs.accepted_iff_checked_code n

theorem not_rational
    (h : SondowProjectSourceComponentCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toFullCertificateCollisionInputs.not_rational

end SondowProjectSourceComponentCollisionInputs

theorem not_rational_of_sondow_project_source_component_collision_inputs
    (h : SondowProjectSourceComponentCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational

/-- Audit-facing package at the derivation-source layer.  This is strictly
lower than `SondowProjectSourceComponentCollisionInputs`: the upper side must
provide actual S21 derivations for the five component formulas, not just proof
objects with the right conclusions. -/
structure SondowProjectS21DerivationCollisionInputs where
  bounds : SondowComponentBounds
  derivationSources :
    MainSondowFullCertificateS21DerivationSources bounds
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      sondowProjectComponentFormulas.target sondowProjectComponentCode

namespace SondowProjectS21DerivationCollisionInputs

def sourceCompilers
    (h : SondowProjectS21DerivationCollisionInputs) :
    MainSondowFullCertificateSourceComponentCompilers h.bounds :=
  h.derivationSources.toSourceComponentCompilers

def toSourceComponentCollisionInputs
    (h : SondowProjectS21DerivationCollisionInputs) :
    SondowProjectSourceComponentCollisionInputs where
  bounds := h.bounds
  sourceCompilers := h.sourceCompilers
  calibration := h.calibration

def projectProofCodeCompilers
    (h : SondowProjectS21DerivationCollisionInputs) :
    SondowProjectComponentProofCodeCompilers h.bounds :=
  h.toSourceComponentCollisionInputs.projectProofCodeCompilers

def componentCertificateOfFullCertificate
    (h : SondowProjectS21DerivationCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowComponentCertificate :=
  h.toSourceComponentCollisionInputs.componentCertificateOfFullCertificate
    hchecked

theorem componentCertificateOfFullCertificate_valid
    (h : SondowProjectS21DerivationCollisionInputs)
    {q : ℚ} {n : ℕ}
    (hchecked : mainSondowFullCertificateChecks q n) :
    SondowComponentCertificate.ProofObjectSystemValid
      sondowProjectComponentFormulas h.bounds n
      (h.componentCertificateOfFullCertificate hchecked) :=
  h.toSourceComponentCollisionInputs
    |>.componentCertificateOfFullCertificate_valid hchecked

theorem full_certificate_iff_source_components
    (_h : SondowProjectS21DerivationCollisionInputs) (q : ℚ) (n : ℕ) :
    mainSondowFullCertificateChecks q n ↔
      MainSondowFullCertificateSourceComponents q n :=
  mainSondowFullCertificateChecks_iff_sourceComponents q n

def lowerSource
    (h : SondowProjectS21DerivationCollisionInputs) :
    BussPudlakTheorem5PALowerBoundSource :=
  h.calibration.lower_source

theorem formula_code_calibrated
    (h : SondowProjectS21DerivationCollisionInputs) (n : ℕ) :
    rescaledExternalPudlakCode
        h.lowerSource.conditions.scale_data.scale n =
      sondowProjectComponentCode (sondowProjectComponentFormulas.target n) :=
  h.calibration.formula_code_eq n

theorem target_code_eq
    (_h : SondowProjectS21DerivationCollisionInputs) (n : ℕ) :
    sondowProjectComponentCode (sondowProjectComponentFormulas.target n) =
      BoundedArithmeticLab.sondowReflectionGraftCode n := by
  exact sondowProjectComponentCode_target n

theorem length_calibrated
    (h : SondowProjectS21DerivationCollisionInputs) (n : ℕ) :
    h.lowerSource.pa_length n =
      semanticBAProofLength PAAxiom sondowProjectComponentFormulas.target n :=
  h.calibration.length_eq n

theorem accepted_iff_checked_code
    (h : SondowProjectS21DerivationCollisionInputs) (n : ℕ) :
    mainSondowAcceptedAt n ↔
      ∃ c : h.toSourceComponentCollisionInputs
          |>.toFullCertificateCollisionInputs
          |>.toConditionalCheckedCodeTraceBridge
          |>.codeSemantics.Code,
        h.toSourceComponentCollisionInputs
          |>.toFullCertificateCollisionInputs
          |>.toConditionalCheckedCodeTraceBridge
          |>.codeSemantics.checksAt c n :=
  h.toSourceComponentCollisionInputs.accepted_iff_checked_code n

theorem not_rational
    (h : SondowProjectS21DerivationCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toSourceComponentCollisionInputs.not_rational

end SondowProjectS21DerivationCollisionInputs

theorem not_rational_of_sondow_project_s21_derivation_collision_inputs
    (h : SondowProjectS21DerivationCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational

theorem not_rational_of_main_sondow_eventual_full_certificate_component_proof_compiler
    {bounds : SondowComponentBounds}
    (compiler :
      MainSondowEventualFullCertificateComponentProofCompiler bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_gamma_rationality_witness_of_project_proof_object_certificates
    compiler.toProjectProofObjectCertificates
    calibration

theorem not_rational_of_sondow_project_atom_definability_bridges
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectAtomDefinabilityBridges bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_rational_of_main_sondow_full_certificate_component_proof_compiler
    bridges.toFullCertificateComponentProofCompiler
    calibration

theorem not_rational_of_sondow_project_direct_atom_proof_bridges
    {bounds : SondowComponentBounds}
    (bridges : SondowProjectDirectAtomProofBridges bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_rational_of_main_sondow_full_certificate_component_proof_compiler
    bridges.toFullCertificateComponentProofCompiler
    calibration

/-- Audit-facing final input package for the direct proof-object route.  It
contains exactly the two remaining obligations: five direct S21 proof bridges
for the project atoms, and the exact Buss/Pudlak formula-length calibration for
the same project target box. -/
structure SondowProjectDirectCollisionInputs where
  bounds : SondowComponentBounds
  bridges : SondowProjectDirectAtomProofBridges bounds
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      sondowProjectComponentFormulas.target sondowProjectComponentCode

namespace SondowProjectDirectCollisionInputs

def toFullCertificateComponentProofCompiler
    (h : SondowProjectDirectCollisionInputs) :
    MainSondowFullCertificateComponentProofCompiler h.bounds :=
  h.bridges.toFullCertificateComponentProofCompiler

def toFullCertificateCollisionInputs
    (h : SondowProjectDirectCollisionInputs) :
    SondowProjectFullCertificateCollisionInputs where
  bounds := h.bounds
  compiler := h.toFullCertificateComponentProofCompiler
  calibration := h.calibration

def toConditionalCheckedCodeTraceBridge
    (h : SondowProjectDirectCollisionInputs) :
    MainSondowConditionalCheckedCodeTraceBridge.{u} h.bounds :=
  h.toFullCertificateCollisionInputs.toConditionalCheckedCodeTraceBridge

def lowerSource
    (h : SondowProjectDirectCollisionInputs) :
    BussPudlakTheorem5PALowerBoundSource :=
  h.calibration.lower_source

theorem formula_code_calibrated
    (h : SondowProjectDirectCollisionInputs) (n : ℕ) :
    rescaledExternalPudlakCode
        h.lowerSource.conditions.scale_data.scale n =
      sondowProjectComponentCode (sondowProjectComponentFormulas.target n) :=
  h.calibration.formula_code_eq n

theorem target_code_eq
    (_h : SondowProjectDirectCollisionInputs) (n : ℕ) :
    sondowProjectComponentCode (sondowProjectComponentFormulas.target n) =
      BoundedArithmeticLab.sondowReflectionGraftCode n := by
  exact sondowProjectComponentCode_target n

theorem length_calibrated
    (h : SondowProjectDirectCollisionInputs) (n : ℕ) :
    h.lowerSource.pa_length n =
      semanticBAProofLength PAAxiom sondowProjectComponentFormulas.target n :=
  h.calibration.length_eq n

theorem accepted_iff_checked_code
    (h : SondowProjectDirectCollisionInputs) (n : ℕ) :
    mainSondowAcceptedAt n ↔
      ∃ c : h.toConditionalCheckedCodeTraceBridge.codeSemantics.Code,
        h.toConditionalCheckedCodeTraceBridge.codeSemantics.checksAt c n :=
  h.toConditionalCheckedCodeTraceBridge.accepted_iff_checked_code n

theorem not_rational
    (h : SondowProjectDirectCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toFullCertificateCollisionInputs.not_rational

end SondowProjectDirectCollisionInputs

theorem not_rational_of_sondow_project_direct_collision_inputs
    (h : SondowProjectDirectCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational

/-- Same audit package, but with the polytime-definability presentation of the
five project-atom proofs.  This is not a weaker target: it converts to the
direct package at the same component bounds. -/
structure SondowProjectDefinabilityCollisionInputs where
  bounds : SondowComponentBounds
  bridges : SondowProjectAtomDefinabilityBridges bounds
  calibration :
    ConcreteBussPudlakFormulaLengthCalibration
      sondowProjectComponentFormulas.target sondowProjectComponentCode

namespace SondowProjectDefinabilityCollisionInputs

def toDirectCollisionInputs
    (h : SondowProjectDefinabilityCollisionInputs) :
    SondowProjectDirectCollisionInputs where
  bounds := h.bounds
  bridges := h.bridges.toDirectAtomProofBridges
  calibration := h.calibration

def toFullCertificateComponentProofCompiler
    (h : SondowProjectDefinabilityCollisionInputs) :
    MainSondowFullCertificateComponentProofCompiler h.bounds :=
  h.bridges.toFullCertificateComponentProofCompiler

def toFullCertificateCollisionInputs
    (h : SondowProjectDefinabilityCollisionInputs) :
    SondowProjectFullCertificateCollisionInputs where
  bounds := h.bounds
  compiler := h.toFullCertificateComponentProofCompiler
  calibration := h.calibration

def lowerSource
    (h : SondowProjectDefinabilityCollisionInputs) :
    BussPudlakTheorem5PALowerBoundSource :=
  h.calibration.lower_source

theorem formula_code_calibrated
    (h : SondowProjectDefinabilityCollisionInputs) (n : ℕ) :
    rescaledExternalPudlakCode
        h.lowerSource.conditions.scale_data.scale n =
      sondowProjectComponentCode (sondowProjectComponentFormulas.target n) :=
  h.calibration.formula_code_eq n

theorem length_calibrated
    (h : SondowProjectDefinabilityCollisionInputs) (n : ℕ) :
    h.lowerSource.pa_length n =
      semanticBAProofLength PAAxiom sondowProjectComponentFormulas.target n :=
  h.calibration.length_eq n

def ofDirectCollisionInputsWithDefinabilityOverhead
    (h : SondowProjectDirectCollisionInputs) :
    SondowProjectDefinabilityCollisionInputs where
  bounds := sondowComponentBoundsAddConst h.bounds 3
  bridges := h.bridges.toDefinabilityBridgesWithOverhead
  calibration := h.calibration

theorem not_rational
    (h : SondowProjectDefinabilityCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.toDirectCollisionInputs.not_rational

end SondowProjectDefinabilityCollisionInputs

theorem not_rational_of_sondow_project_definability_collision_inputs
    (h : SondowProjectDefinabilityCollisionInputs) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  h.not_rational


/-- A stronger adapter retained for audit comparison.  This is useful when a
main `AcceptedCertificateCodeSemantics` object is genuinely available, but it
is not the preferred target statement because that main interface includes a
total completeness field on the whole relevant fragment. -/
structure MainSondowAcceptedCheckedCodeTraceBridge
    (bounds : SondowComponentBounds) where
  codeSemantics :
    _root_.AcceptedCertificateCodeSemantics.{u}
      _root_.sondowCertificateValidCode
  traceCompiler :
    ExternalCheckedCodeToProjectComponentProofCertificateTraces
      (externalAcceptedCheckedCodeSemanticsOfMain codeSemantics) bounds

def MainSondowAcceptedCheckedCodeTraceBridge.toExternalPackage
    {bounds : SondowComponentBounds}
    (h : MainSondowAcceptedCheckedCodeTraceBridge.{u} bounds) :
    ExternalAcceptedCheckedCodeToProjectComponentTracePackage
      mainSondowAcceptedAt bounds where
  codeSemantics := externalAcceptedCheckedCodeSemanticsOfMain h.codeSemantics
  traceCompiler := h.traceCompiler

noncomputable def MainSondowAcceptedCheckedCodeTraceBridge.toComponentTraces
    {bounds : SondowComponentBounds}
    (h : MainSondowAcceptedCheckedCodeTraceBridge.{u} bounds) :
    AcceptedToProjectComponentProofCertificateTraces
      mainSondowAcceptedAt bounds :=
  h.toExternalPackage.toComponentTraces

theorem not_rational_of_main_sondow_checked_code_trace_bridge
    {bounds : SondowComponentBounds}
    (bridge : MainSondowAcceptedCheckedCodeTraceBridge.{u} bounds)
    (calibration :
      ConcreteBussPudlakFormulaLengthCalibration
        sondowProjectComponentFormulas.target sondowProjectComponentCode) :
    ¬ _root_.is_rational _root_.euler_mascheroni :=
  not_main_rationality_of_external_checked_code_trace_package
    (MainRationality := _root_.is_rational _root_.euler_mascheroni)
    (Accepted := mainSondowAcceptedAt)
    _root_.accepted_sondow_certificate_eventual_of_rationality_reproof
    bridge.toExternalPackage
    calibration

end SondowMainCheckedCodeBridge
