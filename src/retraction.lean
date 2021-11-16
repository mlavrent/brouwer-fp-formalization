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

structure retract {α : Type} [topological_space α] {X Y : set α } (r : X → Y) : Prop :=
(retract_continuous : continuous r)
(hy_sub_x : Y ⊆ X)
(retract_of_inclusion_id : r ∘ (set.inclusion hy_sub_x) = id)

#check category_theory.Aut ℝ

def π₁_S₁ : Type := fundamental_group circle ptS₁
def π₁_D₂ : Type := fundamental_group disk ptD₂

lemma π₁_S₁_iso_ℤ : fundamental_group circle ptS₁ ≅ ℤ := sorry
lemma π₁_D₂_iso_0 : fundamental_group disk ptD₂ ≅ unit := sorry

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


lemma no_surj_hom_0toℤ (φ : unit →+ ℤ) :
  ¬ function.surjective ⇑φ :=
begin
  simp [function.surjective],
  apply exists.intro (1 : ℤ),
  intros u heq,
  cases u,
  sorry,
end

lemma no_surj_hom_π₁D₂_to_π₁S₁ (φ : π₁_D₂ →* π₁_S₁) :
  ¬ function.surjective ⇑φ :=
begin
  sorry,
end

theorem no_retraction_theorem (f : disk → frontier disk):
  ¬ retract f :=
begin
  by_contradiction,

  let φ : (fundamental_group disk ptD₂) →* (fundamental_group (frontier disk) ptfD₂) := sorry,
  sorry,
end