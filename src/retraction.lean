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

structure retract {α : Type} [topological_space α] {X Y : set α} (r : X → Y) : Prop :=
(retract_continuous : continuous r)
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

def π₁_S₁ : Type := fundamental_group circle ptS₁
def π₁_D₂ : Type := fundamental_group disk ptD₂

lemma π₁_S₁_iso_ℤ : fundamental_group circle ptS₁ ≅ ℤ :=
category_theory.iso.mk
  (λγ, sorry)
  (λn, sorry)
  sorry
  sorry
lemma π₁_D₂_iso_0 : fundamental_group disk ptD₂ ≅ unit := sorry

instance mul_one_class.π₁_D₂ : mul_one_class π₁_D₂ := sorry
instance mul_one_class.π₁_S₁ : mul_one_class π₁_S₁ := sorry

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

lemma no_surj_hom_π₁D₂_to_π₁S₁ (φ : π₁_D₂ →* π₁_S₁) :
  ¬ function.surjective φ :=
begin
  by_contradiction,
  let φ' := π₁_D₂_iso_0.inv ≫ φ ≫ π₁_S₁_iso_ℤ.hom,
  have hφ'_epi : category_theory.epi φ' := sorry,
  sorry,
  -- not_surjective_fintype_infinite φ
end

theorem no_retraction_theorem (f : C(disk, frontier disk)) :
  ¬ retract f :=
begin
  by_contradiction,
  have hpointed : f ptD₂ = ptfD₂ := sorry,

  let φ : (fundamental_group disk ptD₂) →* (fundamental_group (frontier disk) ptfD₂) :=
    induced_hom f hpointed,
  have h_surj : function.surjective φ := surj_hom_of_surj f hpointed (surjective_of_retract f h),

  have hnot_surj : ¬ function.surjective φ := sorry,
  contradiction,
end