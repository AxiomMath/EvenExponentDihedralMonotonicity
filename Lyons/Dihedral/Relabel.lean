/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Lyons.Meta.Tag

/-!
# Exchanging two reflections by an automorphism

The dihedral group has an automorphism fixing every rotation and sending the distinguished
reflection to any prescribed one:

`r j ↦ r j`,  `sr j ↦ sr (j + c)`.

## Main definitions

* `Lyons.relabelAut`: the automorphism.

## Main results

* `Lyons.exists_relabelAut`: it exists for every target reflection.
-/

open DihedralGroup

namespace Lyons

variable {n : ℕ}

/-- The automorphism of the dihedral group fixing every rotation and translating the reflection
index by `c`.

Multiplicativity is not symmetric in the four cases: `sr j` is `r ^ (-j) * b` rather than
`r ^ j * b`, so the index arithmetic runs the opposite way in the two mixed products. -/
def relabelAut (c : ZMod n) : DihedralGroup n ≃* DihedralGroup n where
  toFun g := match g with
    | .r j => .r j
    | .sr j => .sr (j + c)
  invFun g := match g with
    | .r j => .r j
    | .sr j => .sr (j - c)
  left_inv g := by cases g <;> simp
  right_inv g := by cases g <;> simp
  map_mul' x y := by
    cases x with
    | r i =>
      cases y with
      | r j => simp [r_mul_r]
      | sr j => simp [r_mul_sr]; ring
    | sr i =>
      cases y with
      | r j => simp [sr_mul_r]; ring
      | sr j => simp [sr_mul_sr]

@[simp] theorem relabelAut_r (c j : ZMod n) :
    relabelAut c (DihedralGroup.r j) = DihedralGroup.r j := rfl

@[simp] theorem relabelAut_sr (c j : ZMod n) :
    relabelAut c (DihedralGroup.sr j) = DihedralGroup.sr (j + c) := rfl

/-- **Every reflection is the image of the distinguished one under an automorphism fixing the
rotations.** Reflections are exactly the elements `sr c`, so parametrising the target by `c`
covers all of them. -/
@[lyons_tag "lem_reflection_relabel"]
theorem exists_relabelAut (c : ZMod n) :
    ∃ φ : DihedralGroup n ≃* DihedralGroup n,
      (∀ j : ZMod n, φ (DihedralGroup.r j) = DihedralGroup.r j) ∧
        φ (DihedralGroup.sr 0) = DihedralGroup.sr c :=
  ⟨relabelAut c, fun _ => rfl, by simp⟩

end Lyons
