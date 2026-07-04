/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.CnBoxPudlakCanonicalCalibration

/-!
# Same-object bridge for canonical CnBox/Pudlak targets

This module records the exact object identity used by the canonical finite
consistency route: the Pudlak target formula, the generated `CnBox`, the
formula code, and the bounded PA proof predicate all refer to the same
`finiteConsistencyFormula n`.
-/

namespace BoundedArithmeticLab
namespace BoundedProofPredicate
namespace CnBoxPudlakSameObjectBridge

structure Certificate (n : Nat) : Prop where
  box_eq_mkFiniteConsistency :
    canonicalPudlakTargetFamilySpec.box n = mkFiniteConsistencyCnBox n
  target_eq_finiteConsistency :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n
  target_eq_box_formula :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula
  code_eq_partialConsistency :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n
  code_eq_box_formulaCode :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode
  target_roundtrip :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.target n).encode =
      some (canonicalPudlakTargetFamilySpec.target n)
  box_code_roundtrip_to_target :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n)
  box_certifies :
    (canonicalPudlakTargetFamilySpec.box n).Certifies
  predicate_alignment :
    BoundedPAPredicateCnBoxAlignment
      (canonicalPudlakTargetFamilySpec.box n)
  statement_iff_pa_finite_consistency :
    canonicalPudlakTargetFamilySpec.statement n ↔
      PAFiniteConsistencyStatement n
  carries_iff_statement :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        canonicalPudlakTargetFamilySpec.statement n
  carries_iff_pa_finite_consistency :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n
  length_eq_semantic_target :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom canonicalPudlakTargetFamilySpec.target n
  length_eq_semantic_box_formula :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n

abbrev Checklist : Prop :=
  ∀ n : Nat, Certificate n

theorem box_eq_mkFiniteConsistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.box n = mkFiniteConsistencyCnBox n :=
  rfl

theorem target_eq_finiteConsistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n = finiteConsistencyFormula n :=
  canonicalPudlakTarget_target_eq_finiteConsistency n

theorem target_eq_box_formula (n : Nat) :
    canonicalPudlakTargetFamilySpec.target n =
      (canonicalPudlakTargetFamilySpec.box n).formula :=
  rfl

theorem code_eq_partialConsistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        partialConsistencyCode n :=
  canonicalPudlakTarget_code_eq_partialConsistency n

theorem code_eq_box_formulaCode (n : Nat) :
    canonicalPudlakTargetFamilySpec.code
      (canonicalPudlakTargetFamilySpec.target n) =
        (canonicalPudlakTargetFamilySpec.box n).formulaCode :=
  rfl

theorem target_roundtrip (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.target n).encode =
      some (canonicalPudlakTargetFamilySpec.target n) :=
  BAFormula.decode_encode (canonicalPudlakTargetFamilySpec.target n)

theorem box_code_roundtrip_to_target (n : Nat) :
    BAFormula.decode (canonicalPudlakTargetFamilySpec.box n).code =
      some (canonicalPudlakTargetFamilySpec.target n) := by
  simpa [canonicalPudlakTargetFamilySpec, canonicalFiniteConsistencyGenerator,
    mkFiniteConsistencyCnBox] using finiteConsistencyFormula_decode_encode n

theorem box_certifies (n : Nat) :
    (canonicalPudlakTargetFamilySpec.box n).Certifies := by
  simpa [canonicalPudlakTargetFamilySpec, canonicalFiniteConsistencyGenerator] using
    mkFiniteConsistencyCnBox_certifies n

theorem predicate_alignment (n : Nat) :
    BoundedPAPredicateCnBoxAlignment
      (canonicalPudlakTargetFamilySpec.box n) := by
  simpa [canonicalPudlakTargetFamilySpec, canonicalFiniteConsistencyGenerator] using
    mkFiniteConsistencyCnBox_predicateAlignment n

theorem statement_iff_pa_finite_consistency (n : Nat) :
    canonicalPudlakTargetFamilySpec.statement n ↔
      PAFiniteConsistencyStatement n :=
  Iff.rfl

theorem carries_iff_statement (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        canonicalPudlakTargetFamilySpec.statement n :=
  canonicalPudlakTargetFamily_carriesPAFiniteConsistency n

theorem carries_iff_pa_finite_consistency (n : Nat) :
    CnBoxCarriesPAFiniteConsistency
      (canonicalPudlakTargetFamilySpec.box n) ↔
        PAFiniteConsistencyStatement n := by
  simpa [canonicalPudlakTargetFamilySpec, canonicalFiniteConsistencyGenerator] using
    mkFiniteConsistencyCnBox_carriesPAFiniteConsistency_iff n

theorem length_eq_semantic_target (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom canonicalPudlakTargetFamilySpec.target n :=
  canonicalPudlakTarget_length_eq_semantic n

theorem length_eq_semantic_box_formula (n : Nat) :
    canonicalPudlakTargetFamilySpec.length n =
      semanticBAProofLength PAAxiom
        (fun k => (canonicalPudlakTargetFamilySpec.box k).formula) n :=
  rfl

theorem certificate (n : Nat) : Certificate n where
  box_eq_mkFiniteConsistency := box_eq_mkFiniteConsistency n
  target_eq_finiteConsistency := target_eq_finiteConsistency n
  target_eq_box_formula := target_eq_box_formula n
  code_eq_partialConsistency := code_eq_partialConsistency n
  code_eq_box_formulaCode := code_eq_box_formulaCode n
  target_roundtrip := target_roundtrip n
  box_code_roundtrip_to_target := box_code_roundtrip_to_target n
  box_certifies := box_certifies n
  predicate_alignment := predicate_alignment n
  statement_iff_pa_finite_consistency :=
    statement_iff_pa_finite_consistency n
  carries_iff_statement := carries_iff_statement n
  carries_iff_pa_finite_consistency :=
    carries_iff_pa_finite_consistency n
  length_eq_semantic_target := length_eq_semantic_target n
  length_eq_semantic_box_formula := length_eq_semantic_box_formula n

theorem checklist : Checklist :=
  certificate

end CnBoxPudlakSameObjectBridge
end BoundedProofPredicate
end BoundedArithmeticLab
