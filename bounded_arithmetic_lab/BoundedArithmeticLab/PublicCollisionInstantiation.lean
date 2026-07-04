/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionAPI

/-!
# Public collision instantiations

This module packages the common paper pattern: if a hypothesis can produce a
public collision checklist, then the hypothesis is false.  It is generic and
does not mention any project-specific CnBox/Sondow/Pudlak objects.
-/

namespace BoundedArithmeticLab

structure PublicCollisionInstantiation (Hypothesis : Prop) where
  checklist : Hypothesis → PublicCollisionAPI.Checklist

structure PublicSeparatedCollisionInstantiation (Hypothesis : Prop) where
  checklist : Hypothesis → PublicCollisionAPI.SeparatedChecklist

structure PublicGapCollisionInstantiation (Hypothesis : Prop) where
  checklist : Hypothesis → PublicCollisionAPI.GapChecklist

namespace PublicCollisionInstantiation

theorem collision {Hypothesis : Prop}
    (inst : PublicCollisionInstantiation Hypothesis)
    (hypothesis : Hypothesis) : False :=
  PublicCollisionAPI.collision_from_checklist (inst.checklist hypothesis)

theorem not_hypothesis {Hypothesis : Prop}
    (inst : PublicCollisionInstantiation Hypothesis) :
    ¬ Hypothesis := by
  intro hypothesis
  exact inst.collision hypothesis

def toSeparatedCollisionInstantiation {Hypothesis : Prop}
    (inst : PublicCollisionInstantiation Hypothesis) :
    PublicSeparatedCollisionInstantiation Hypothesis where
  checklist := fun hypothesis =>
    (inst.checklist hypothesis).toSeparatedCollisionChecklist

def toGapCollisionInstantiation {Hypothesis : Prop}
    (inst : PublicCollisionInstantiation Hypothesis) :
    PublicGapCollisionInstantiation Hypothesis where
  checklist := fun hypothesis =>
    (inst.checklist hypothesis).toPublicGapCollisionChecklist

end PublicCollisionInstantiation

namespace PublicSeparatedCollisionInstantiation

def toCollisionInstantiation {Hypothesis : Prop}
    (inst : PublicSeparatedCollisionInstantiation Hypothesis) :
    PublicCollisionInstantiation Hypothesis where
  checklist := fun hypothesis =>
    (inst.checklist hypothesis).toPublicCollisionChecklist

theorem collision {Hypothesis : Prop}
    (inst : PublicSeparatedCollisionInstantiation Hypothesis)
    (hypothesis : Hypothesis) : False :=
  PublicCollisionAPI.collision_from_separated_checklist
    (inst.checklist hypothesis)

theorem not_hypothesis {Hypothesis : Prop}
    (inst : PublicSeparatedCollisionInstantiation Hypothesis) :
    ¬ Hypothesis := by
  intro hypothesis
  exact inst.collision hypothesis

end PublicSeparatedCollisionInstantiation

namespace PublicGapCollisionInstantiation

noncomputable def toCollisionInstantiation {Hypothesis : Prop}
    (inst : PublicGapCollisionInstantiation Hypothesis) :
    PublicCollisionInstantiation Hypothesis where
  checklist := fun hypothesis =>
    (inst.checklist hypothesis).toPublicCollisionChecklist

theorem collision {Hypothesis : Prop}
    (inst : PublicGapCollisionInstantiation Hypothesis)
    (hypothesis : Hypothesis) : False :=
  PublicCollisionAPI.collision_from_gap_checklist
    (inst.checklist hypothesis)

theorem not_hypothesis {Hypothesis : Prop}
    (inst : PublicGapCollisionInstantiation Hypothesis) :
    ¬ Hypothesis := by
  intro hypothesis
  exact inst.collision hypothesis

end PublicGapCollisionInstantiation

theorem
    publicSeparatedCollisionInstantiation_nonempty_iff_collisionInstantiation_nonempty
    {Hypothesis : Prop} :
    Nonempty (PublicSeparatedCollisionInstantiation Hypothesis) ↔
      Nonempty (PublicCollisionInstantiation Hypothesis) := by
  constructor
  · intro h
    rcases h with ⟨inst⟩
    exact ⟨inst.toCollisionInstantiation⟩
  · intro h
    rcases h with ⟨inst⟩
    exact ⟨inst.toSeparatedCollisionInstantiation⟩

theorem publicGapCollisionInstantiation_nonempty_iff_collisionInstantiation_nonempty
    {Hypothesis : Prop} :
    Nonempty (PublicGapCollisionInstantiation Hypothesis) ↔
      Nonempty (PublicCollisionInstantiation Hypothesis) := by
  constructor
  · intro h
    rcases h with ⟨inst⟩
    exact ⟨inst.toCollisionInstantiation⟩
  · intro h
    rcases h with ⟨inst⟩
    exact ⟨inst.toGapCollisionInstantiation⟩

end BoundedArithmeticLab
