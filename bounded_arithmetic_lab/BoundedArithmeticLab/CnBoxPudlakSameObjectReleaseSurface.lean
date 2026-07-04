/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakSameObjectBridge

/-!
# Same-object release surface

This module exposes stable paper-facing names for the canonical CnBox/Pudlak
same-object bridge.  The statements are theorem aliases over the bridge
certificate, so the public surface cannot silently change the target object.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace CnBoxPudlakSameObjectReleaseSurface

theorem sameObject_checklist :
    CnBoxPudlakSameObjectBridge.Checklist :=
  CnBoxPudlakSameObjectBridge.checklist

theorem sameObject_certificate (n : Nat) :
    CnBoxPudlakSameObjectBridge.Certificate n :=
  CnBoxPudlakSameObjectBridge.certificate n

theorem sameObject_finiteConsistency_generator_certificate (n : Nat) :
    FiniteConsistencySameObjectCertificate n :=
  canonicalFiniteConsistency_sameObjectCertificate n

def sameObject_generation_certificate (n : Nat) :
    FiniteConsistencyGenerationCertificate n :=
  mkFiniteConsistencyGenerationCertificate n

theorem sameObject_target_family_identification :
    PudlakTargetFamilyIdentificationCertificate
      canonicalPudlakTargetFamilySpec :=
  canonicalPudlakTargetFamily_identificationCertificate

theorem sameObject_box_eq_mkFiniteConsistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.box n = mkFiniteConsistencyCnBox n :=
  (sameObject_certificate n).box_eq_mkFiniteConsistency

theorem sameObject_target_eq_finiteConsistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  (sameObject_certificate n).target_eq_finiteConsistency

theorem sameObject_target_eq_box_formula (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula :=
  (sameObject_certificate n).target_eq_box_formula

theorem sameObject_code_eq_partialConsistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  (sameObject_certificate n).code_eq_partialConsistency

theorem sameObject_code_eq_box_formulaCode (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode :=
  (sameObject_certificate n).code_eq_box_formulaCode

theorem sameObject_target_roundtrip (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.target n).encode =
      some (canonicalPudlakTargetFamilySpec.target n) :=
  (sameObject_certificate n).target_roundtrip

theorem sameObject_box_code_roundtrip_to_target (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n) :=
  (sameObject_certificate n).box_code_roundtrip_to_target

theorem sameObject_box_certifies (n : Nat) :
    (canonicalPudlakTargetFamilySpec.box n).Certifies :=
  (sameObject_certificate n).box_certifies

theorem sameObject_predicate_alignment (n : Nat) :
    BoundedPAPredicateCnBoxAlignment
      (canonicalPudlakTargetFamilySpec.box n) :=
  (sameObject_certificate n).predicate_alignment

theorem sameObject_statement_iff_pa_finite_consistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.statement n ↔
      PAFiniteConsistencyStatement n :=
  (sameObject_certificate n).statement_iff_pa_finite_consistency

theorem sameObject_carries_iff_statement (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        canonicalPudlakTargetFamilySpec.statement n :=
  (sameObject_certificate n).carries_iff_statement

theorem sameObject_carries_iff_pa_finite_consistency (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n :=
  (sameObject_certificate n).carries_iff_pa_finite_consistency

theorem sameObject_length_eq_semantic_target (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom canonicalPudlakTargetFamilySpec.target n :=
  (sameObject_certificate n).length_eq_semantic_target

theorem sameObject_length_eq_semantic_box_formula (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n :=
  (sameObject_certificate n).length_eq_semantic_box_formula

end CnBoxPudlakSameObjectReleaseSurface
end BoundedProofPredicate
end BoundedArithmeticLab
