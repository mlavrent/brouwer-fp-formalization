import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.endomorphism
import category_theory.groupoid
import algebra.category.Group.basic
import category_theory.category.basic
import data.complex.exponential
import analysis.special_functions.trigonometric.basic

import .disk
import .fundamental_group


/--
A retraction is a continuous map r from a space to a subset of itself where
r restricted to that subset is the identity.
-/
structure retraction {α : Type} [topological_space α] {X Y : set α} (r : C(X, Y)) : Prop :=
(hy_sub_x : Y ⊆ X)
(inclusion_right_inv : function.right_inverse (set.inclusion hy_sub_x) r)

lemma surjective_of_retraction {α : Type} [topological_space α] {X Y : set α} (r : C(X, Y)) :
  retraction r → function.surjective r :=
begin
  intro hret,
  apply function.has_right_inverse.surjective,
  apply exists.intro (set.inclusion hret.hy_sub_x),
  exact hret.inclusion_right_inv,
end

noncomputable def nth_winding_loop (n : ℤ) : path pt pt :=
path.mk
  (continuous_map.mk
    (λt, (real.cos (2 * real.pi * n * t), real.sin (2 * real.pi * n * t)))
    (by continuity))
  (by simp [pt])
  begin
    simp [pt],
    rw mul_comm _ ↑n,
    apply and.intro,
    apply real.cos_int_mul_two_pi,
    rw ← zero_add (↑n * (2 * real.pi)),
    rw real.sin_add_int_mul_two_pi 0 n,
    simp,
  end

def nth_winding_loop_class (n : ℤ) : circle.pointed_space.basepoint ⟶ circle.pointed_space.basepoint :=
sorry
-- @quotient.mk
--   (path pt pt)
--   (path.homotopic.setoid pt pt)
--   (nth_winding_loop n)

noncomputable lemma fg_circle_iso_int : fundamental_group circle.pointed_space ≅ ℤ := {
  hom := (λγ, sorry),
  inv := (λn, sorry),
  hom_inv_id' := sorry,
  inv_hom_id' := sorry,
}

noncomputable lemma fg_disk_iso_0 : fundamental_group disk.pointed_space ≅ unit :=
category_theory.iso.mk
  (λγ, 0)
  (λn, 1)
  (begin
    ext γ,
    simp, -- 1, γ are elements in fundamental group i.e. 1.hom and γ.hom are arrows in fundamental groupoid
    -- apply quotient.sound,
    sorry,
  end)
  (by {funext, simp})

-- instance mul_one_class.π₁_D₂ : mul_one_class (fundamental_group disk.pointed_space) := sorry
-- instance mul_one_class.π₁_S₁ : mul_one_class (fundamental_group circle.pointed_space) := sorry

instance unit.has_zero : has_zero unit := {
  zero := unit.star,
}

instance unit.add_group : add_group unit := {
  add := λ_ _, 0,
  zero := 0,
  neg := λ_, 0,
  add_assoc := by cc,
  add_zero := by cc,
  zero_add := by cc,
  add_left_neg := by cc,
}

lemma no_surj_hom_π₁D₂_to_π₁S₁ (φ : (fundamental_group disk.pointed_space) →* (fundamental_group circle.pointed_space)) :
  ¬ function.surjective φ :=
begin
  by_contradiction,
  let ψ := fg_disk_iso_0.inv ≫ φ ≫ fg_circle_iso_int.hom,

  have hψ_epi : category_theory.epi ψ := begin
    -- apply @category_theory.epi_of_epi_fac _ _ _ _ _ fg_disk_iso_0.inv (φ ≫ fg_circle_iso_int.hom) ψ _,
    sorry,
  end,

  have hψ_not_epi : ¬ category_theory.epi ψ := begin
    rw category_theory.epi_iff_surjective,
    apply not_surjective_fintype_infinite,
  end,
  contradiction,
end

lemma no_surj_hom_π₁D₂_to_frontier (φ : (fundamental_group disk.pointed_space) →* (fundamental_group frontier_disk.pointed_space)) :
  ¬ function.surjective φ :=
begin
  by_contradiction,
  let φ' : (fundamental_group disk.pointed_space) →* (fundamental_group circle.pointed_space) := sorry,
    -- (pointed_map_of_continuous_map frontier_disk_homeo_circle.to_fun) ∘ φ,
    -- compose these somehow

  have h_φ'_surj : function.surjective φ' :=
    begin
      apply function.surjective.comp,
      { sorry },
      { sorry },
    end,
  have h_φ'_not_surj : ¬ function.surjective φ' := no_surj_hom_π₁D₂_to_π₁S₁ φ',
  contradiction,
end

/--
The 2-dimensional no retraction theorem asserts that there is no retraction
from the disk D² to its boundary circle S¹.
-/
theorem no_retraction_theorem (f : C(disk, frontier disk)) :
  ¬ retraction f :=
begin
  by_contradiction,

  let codomain_ptd_space : pointed_space (frontier disk) := ⟨f disk.pointed_space.basepoint⟩,

  have h_iso : fundamental_group codomain_ptd_space ≃* fundamental_group frontier_disk.pointed_space :=
    mulequiv_fg_of_path_conn codomain_ptd_space frontier_disk.pointed_space,

  let f_ptd : Cp(disk.pointed_space, codomain_ptd_space) := {
    to_fun := f,
    pointed_map := by refl,
  },
  have h_fptd_eq_f : f_ptd.to_continuous_map = f := begin
    ext,
    repeat {simp [f_ptd]},
  end,

  let φ_pre : (fundamental_group disk.pointed_space) →* (fundamental_group codomain_ptd_space) :=
    induced_hom f_ptd,
  have h_φpre_surj : function.surjective φ_pre :=
    surj_hom_of_surj f_ptd begin
      apply surjective_of_retraction,
      rw h_fptd_eq_f,
      exact h,
    end,

  let φ : (fundamental_group disk.pointed_space) →* (fundamental_group frontier_disk.pointed_space) :=
    monoid_hom.comp (mul_equiv.to_monoid_hom h_iso) φ_pre,

  have h_φ_surj : function.surjective φ :=
    begin
      apply function.surjective.comp,
      { exact mul_equiv.surjective h_iso, },
      { exact h_φpre_surj, },
    end,
  have hnot_surj : ¬ function.surjective φ := no_surj_hom_π₁D₂_to_frontier φ,

  contradiction,
end