import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

import .disk
import .retraction



-- lemma π₁_of_S₁_iso_ℤ : fundamental_groupoid disk 0 := sorry
-- lemma π₁_of_D₂_iso_0 : fundamental_groupoid unit_circle ≅ ℤ := sorry

lemma chord_intersect_circle (p a : disk) (hp_neq_a p ≠ a) :=
  ∃(t : ℝ), |p + t * (p - a)| = 1 := sorry

def brouwer_func (p a : disk) (hp_neq_a : p ≠ a) : frontier disk :=
sorry

lemma brouwer_func_id_on_frontier (p : disk) (a : frontier disk) (hp_neq_a : p ≠ a) :
  true := sorry


theorem brouwer_fixed_point (f : disk → disk) :
  ∃x, f x = x :=
begin
  by_contradiction,
  have hno_fix : ∀x, f x ≠ x := begin
    rw ← not_exists,
    assumption,
   end,

  let r : disk → frontier disk :=
    sorry,

  have hf_retract : retraction r := {
    retract_continuous := sorry,
    hy_sub_x := frontier_subset_closed_set _ _,
    retract_of_inclusion_id := sorry,
  },

  have hf_not_retract : ¬ retraction r := no_retraction_theorem r,
  contradiction,
end
