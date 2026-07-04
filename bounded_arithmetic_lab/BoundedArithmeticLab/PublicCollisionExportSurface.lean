/-
Copyright (c) 2026 James. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James
-/
import BoundedArithmeticLab.PublicCollisionInstantiation

/-!
# Public collision export surface

This module is the generic open-source candidate export surface.  It contains
only project-independent theorem aliases over the public collision API and
public collision instantiation layer.
-/

namespace BoundedArithmeticLab

namespace PublicCollisionExportSurface

abbrev CollisionInstantiation := PublicCollisionInstantiation
abbrev GapCollisionInstantiation := PublicGapCollisionInstantiation
abbrev SeparatedCollisionInstantiation := PublicSeparatedCollisionInstantiation

theorem collision {Hypothesis : Prop}
    (inst : CollisionInstantiation Hypothesis)
    (hypothesis : Hypothesis) : False :=
  inst.collision hypothesis

theorem not_hypothesis {Hypothesis : Prop}
    (inst : CollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  inst.not_hypothesis

theorem gap_collision {Hypothesis : Prop}
    (inst : GapCollisionInstantiation Hypothesis)
    (hypothesis : Hypothesis) : False :=
  inst.collision hypothesis

theorem gap_not_hypothesis {Hypothesis : Prop}
    (inst : GapCollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  inst.not_hypothesis

theorem separated_collision {Hypothesis : Prop}
    (inst : SeparatedCollisionInstantiation Hypothesis)
    (hypothesis : Hypothesis) : False :=
  inst.collision hypothesis

theorem separated_not_hypothesis {Hypothesis : Prop}
    (inst : SeparatedCollisionInstantiation Hypothesis) :
    ¬ Hypothesis :=
  inst.not_hypothesis

theorem gap_nonempty_iff_collision_nonempty {Hypothesis : Prop} :
    Nonempty (GapCollisionInstantiation Hypothesis) ↔
      Nonempty (CollisionInstantiation Hypothesis) :=
  publicGapCollisionInstantiation_nonempty_iff_collisionInstantiation_nonempty

theorem separated_nonempty_iff_collision_nonempty {Hypothesis : Prop} :
    Nonempty (SeparatedCollisionInstantiation Hypothesis) ↔
      Nonempty (CollisionInstantiation Hypothesis) :=
  publicSeparatedCollisionInstantiation_nonempty_iff_collisionInstantiation_nonempty

theorem checklist_collision (checklist : PublicCollisionAPI.Checklist) :
    False :=
  PublicCollisionAPI.collision_from_checklist checklist

theorem gap_checklist_collision
    (checklist : PublicCollisionAPI.GapChecklist) : False :=
  PublicCollisionAPI.collision_from_gap_checklist checklist

theorem separated_checklist_collision
    (checklist : PublicCollisionAPI.SeparatedChecklist) : False :=
  PublicCollisionAPI.collision_from_separated_checklist checklist

end PublicCollisionExportSurface

end BoundedArithmeticLab
