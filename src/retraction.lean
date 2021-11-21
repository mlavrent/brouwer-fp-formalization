import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.endomorphism
import category_theory.groupoid
import algebra.category.Group.basic
import category_theory.category.basic

import .disk
import .fundamental_group


/--
A retract is a continuous map r from a space to a subset of itself where
r restricted to that subset is the identity.
-/
structure retract {α : Type} [topological_space α] {X Y : set α} (r : C(X, Y)) : Prop :=
(hy_sub_x : Y ⊆ X)
(inclusion_right_inv : function.right_inverse (set.inclusion hy_sub_x) r)

lemma surjective_of_retract {α : Type} [topological_space α] {X Y : set α} (r : X → Y) :
  retract r → function.surjective r :=
begin
  intro hret,
  apply function.has_right_inverse.surjective,
  apply exists.intro (set.inclusion hret.hy_sub_x),
  exact hret.inclusion_right_inv,
end

lemma fg_circle_iso_int : fundamental_group circle ≅ ℤ :=
category_theory.iso.mk
  (λγ, sorry)
  (λn, sorry)
  sorry
  sorry
lemma fg_disk_iso_0 : fundamental_group disk ≅ unit :=
category_theory.iso.mk
  (λγ, 0)
  (λn, sorry)
  sorry
  sorry

instance mul_one_class.π₁_D₂ : mul_one_class (fundamental_group disk) := sorry
instance mul_one_class.π₁_S₁ : mul_one_class (fundamental_group circle) := sorry

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

lemma no_surj_hom_π₁D₂_to_π₁S₁ (φ : (fundamental_group disk) →* (fundamental_group circle)) :
  ¬ function.surjective φ :=
begin
  by_contradiction,
  let ψ := π₁_D₂_iso_0.inv ≫ φ ≫ π₁_S₁_iso_ℤ.hom,

  have hψ_epi : category_theory.epi ψ := begin
    -- apply @category_theory.epi_of_epi_fac _ _ _ _ _ π₁_D₂_iso_0.inv (φ ≫ π₁_S₁_iso_ℤ.hom) ψ _,
    sorry,
  end,

  have hψ_not_epi : ¬ category_theory.epi ψ := begin
    rw category_theory.epi_iff_surjective,
    apply not_surjective_fintype_infinite,
  end,
  contradiction,
end

/--
The 2-dimensional no retraction theorem asserts that there is no retract
from the disk D² to its boundary circle S¹.
-/
theorem no_retraction_theorem (f : C(disk, frontier disk)) :
  ¬ retract f :=
begin
  by_contradiction,

  let φ : (fundamental_group disk) →* (fundamental_group (frontier disk)) :=
    induced_hom f,
  -- rw disk_frontier_eq_circle at φ,

  have h_surj : function.surjective φ :=
    @surj_hom_of_surj f (surjective_of_retract f h),

  have hnot_surj : ¬ function.surjective φ := sorry,
  contradiction,
end