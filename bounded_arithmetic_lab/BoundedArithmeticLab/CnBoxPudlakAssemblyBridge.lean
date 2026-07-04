/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakExternalGapCriterion

/-!
# Assembly bridge for Sondow project certificates

This module refines the remaining assembler obligation.  A compiled Sondow
project source certificate already carries the five component proof
certificates.  The missing step is a per-source assembly certificate that
builds a canonical finite-consistency proof certificate with the declared
bound.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate

namespace CompiledSondowProjectSourceCertificateAt

def sourceSize {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) : Nat :=
  source.product.sourceSize + source.logRelation.sourceSize +
    source.decomposition.sourceSize + source.threePow.sourceSize +
      source.payload.sourceSize

theorem product_conclusion_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    source.product.proof.conclusion =
      sondowProjectComponentFormulas.product n := by
  rw [source.product.proof_conclusion, source.product_index_eq]

theorem logRelation_conclusion_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    source.logRelation.proof.conclusion =
      sondowProjectComponentFormulas.logRelation n := by
  rw [source.logRelation.proof_conclusion, source.log_index_eq]

theorem decomposition_conclusion_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    source.decomposition.proof.conclusion =
      sondowProjectComponentFormulas.decomposition n := by
  rw [source.decomposition.proof_conclusion,
    source.decomposition_index_eq]

theorem threePow_conclusion_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    source.threePow.proof.conclusion =
      sondowProjectComponentFormulas.threePow n := by
  rw [source.threePow.proof_conclusion, source.threePow_index_eq]

theorem payload_conclusion_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    source.payload.proof.conclusion =
      sondowProjectComponentFormulas.payload n := by
  rw [source.payload.proof_conclusion, source.payload_index_eq]

theorem product_size_plus_two_le_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (((source.product.proof.size + 2 : Nat) : Real)) ≤
      bounds.product n := by
  simpa [source.product_index_eq] using
    source.product.proof_size_plus_two_le

theorem logRelation_size_plus_two_le_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (((source.logRelation.proof.size + 2 : Nat) : Real)) ≤
      bounds.logRelation n := by
  simpa [source.log_index_eq] using
    source.logRelation.proof_size_plus_two_le

theorem decomposition_size_plus_two_le_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (((source.decomposition.proof.size + 2 : Nat) : Real)) ≤
      bounds.decomposition n := by
  simpa [source.decomposition_index_eq] using
    source.decomposition.proof_size_plus_two_le

theorem threePow_size_plus_two_le_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (((source.threePow.proof.size + 2 : Nat) : Real)) ≤
      bounds.threePow n := by
  simpa [source.threePow_index_eq] using
    source.threePow.proof_size_plus_two_le

theorem payload_size_plus_two_le_at
    {bounds : SondowComponentBounds} {n : Nat}
    (source : CompiledSondowProjectSourceCertificateAt bounds n) :
    (((source.payload.proof.size + 2 : Nat) : Real)) ≤
      bounds.payload n := by
  simpa [source.payload_index_eq] using
    source.payload.proof_size_plus_two_le

end CompiledSondowProjectSourceCertificateAt

structure SondowProjectCanonicalAssemblyFor
    {bounds : SondowComponentBounds} (bound : Nat → Real)
    {n : Nat} (source : CompiledSondowProjectSourceCertificateAt bounds n)
    where
  assembledProof : BAProofObject BussS21Axiom
  proof_conclusion :
    assembledProof.conclusion = canonicalPudlakTargetFamilySpec.target n
  proof_size_plus_two_le :
    (((assembledProof.size + 2 : Nat) : Real)) ≤ bound n

def SondowProjectCanonicalAssemblyFor.toCanonicalProofCertificateAt
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    {n : Nat} {source : CompiledSondowProjectSourceCertificateAt bounds n}
    (assembly : SondowProjectCanonicalAssemblyFor bound source) :
    CanonicalProofCertificateAt bound n where
  sourceSize :=
    CompiledSondowProjectSourceCertificateAt.sourceSize source
  proof := assembly.assembledProof
  proof_conclusion := assembly.proof_conclusion
  proof_size_plus_two_le := assembly.proof_size_plus_two_le

structure SondowProjectCanonicalAssemblyProvider
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  assembly :
    ∀ n : Nat, ∀ source : CompiledSondowProjectSourceCertificateAt bounds n,
      SondowProjectCanonicalAssemblyFor bound source

def SondowProjectCanonicalAssemblyProvider.toAssembler
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (provider : SondowProjectCanonicalAssemblyProvider bounds bound) :
    SondowProjectToCanonicalProofCertificateAssembler bounds bound where
  assemble := by
    intro n source
    exact (provider.assembly n source).toCanonicalProofCertificateAt

def SondowProjectCanonicalAssemblyProvider.ofAssembler
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (assembler : SondowProjectToCanonicalProofCertificateAssembler bounds bound) :
    SondowProjectCanonicalAssemblyProvider bounds bound where
  assembly := by
    intro n source
    let cert := assembler.assemble n source
    exact {
      assembledProof := cert.proof
      proof_conclusion := cert.proof_conclusion
      proof_size_plus_two_le := cert.proof_size_plus_two_le }

theorem sondowProjectCanonicalAssemblyProvider_nonempty_iff_assembler_nonempty
    {bounds : SondowComponentBounds} {bound : Nat → Real} :
    Nonempty (SondowProjectCanonicalAssemblyProvider bounds bound) ↔
      Nonempty (SondowProjectToCanonicalProofCertificateAssembler bounds bound) := by
  constructor
  · intro h
    rcases h with ⟨provider⟩
    exact ⟨provider.toAssembler⟩
  · intro h
    rcases h with ⟨assembler⟩
    exact ⟨SondowProjectCanonicalAssemblyProvider.ofAssembler assembler⟩

structure ProjectLevelCnBoxSondowAssemblyChecklist
    (MainRationality : Prop) (SondowAccepted : Nat → Prop)
    (bounds : SondowComponentBounds) (bound : Nat → Real) where
  bound_poly : IsPolynomialBound bound
  sondow_eventual_accepted :
    MainAcceptedEventuallyUnderRationality
      MainRationality SondowAccepted
  accepted_to_compiled_source :
    AcceptedToCompiledProjectSourceCertificateCompiler
      SondowAccepted bounds
  canonical_assembly :
    SondowProjectCanonicalAssemblyProvider bounds bound
  lower_source : BussPudlakTheorem5PALowerBoundSource
  relabeling :
    SemanticFormulaRelabeling lower_source.box.formula
      (concretePAFormalization
        canonicalPudlakTargetFamilySpec.target
        canonicalPudlakTargetFamilySpec.code).box.formula
  length_eq :
    ∀ n : Nat,
      lower_source.pa_length n =
        semanticBAProofLength PAAxiom finiteConsistencyFormula n

namespace ProjectLevelCnBoxSondowAssemblyChecklist

noncomputable def toCompiledChecklist
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxSondowCompiledChecklist
      MainRationality SondowAccepted bounds bound where
  bound_poly := checklist.bound_poly
  sondow_eventual_accepted := checklist.sondow_eventual_accepted
  accepted_to_compiled_source := checklist.accepted_to_compiled_source
  canonical_assembler := checklist.canonical_assembly.toAssembler
  lower_source := checklist.lower_source
  relabeling := checklist.relabeling
  length_eq := checklist.length_eq

noncomputable def toCertificateBackedGapCriterion
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ProjectLevelCnBoxCertificateBackedGapCriterion
      MainRationality SondowAccepted bound :=
  checklist.toCompiledChecklist.toCertificateBackedGapCriterion

theorem not_main_rationality
    {MainRationality : Prop} {SondowAccepted : Nat → Prop}
    {bounds : SondowComponentBounds} {bound : Nat → Real}
    (checklist :
      ProjectLevelCnBoxSondowAssemblyChecklist
        MainRationality SondowAccepted bounds bound) :
    ¬ MainRationality :=
  checklist.toCertificateBackedGapCriterion.not_main_rationality

end ProjectLevelCnBoxSondowAssemblyChecklist

end BoundedProofPredicate
end BoundedArithmeticLab
