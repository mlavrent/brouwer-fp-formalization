import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

import .disk

structure retraction {α : Type} [topological_space α] {X Y : set α } (r : X → Y) : Prop :=
(retract_continuous : continuous r)
(hy_sub_x : Y ⊆ X)
(retract_of_inclusion_id : r ∘ (set.inclusion hy_sub_x) = id)


-- lemma π₁_of_S₁_iso_ℤ : fundamental_groupoid disk 0 := sorry
-- lemma π₁_of_D₂_iso_0 : fundamental_groupoid unit_circle ≅ ℤ := sorry

theorem no_retraction_theorem (f : disk → frontier disk):
  ¬ retraction f :=
begin
  by_contradiction,
  sorry,
end