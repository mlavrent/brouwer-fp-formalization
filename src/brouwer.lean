import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic
-- import topology.homotopy.fundamental_groupoid


def unit_disk : set _ := metric.closed_ball (0 : ℝ × ℝ) 1

def unit_circle : set _ := metric.sphere (0 : ℝ × ℝ) 1

lemma closed_set_boundary_contained {α : Type} [topological_space α] (X : set α) :
  is_closed X → frontier X ⊆ X :=
begin
  intro hclosed,
  -- is_closed.frontier_eq
  sorry,
end

lemma disk_boundary_eq_circle : frontier unit_disk = unit_circle :=
sorry


-- lemma π₁_of_S₁_iso_ℤ : fundamental_groupoid unit_disk 0 := sorry
-- lemma π₁_of_D₂_iso_0 : fundamental_groupoid unit_circle ≅ ℤ := sorry

lemma disk_line_intersects_boundary {α : Type} [topological_space α] [has_add α] (a b : unit_disk) (hxy_neq : a ≠ b) :
  ∃(c : unit_circle)(t : ℝ), true := --c = a + t * (b - a) :=
sorry


structure retraction {α : Type} [topological_space α] {X Y : set α } (r : X → Y) : Prop :=
(retract_continuous : continuous r)
(hy_sub_x : Y ⊆ X)
(retract_of_inclusion_id : r ∘ (set.inclusion hy_sub_x) = id)


theorem no_retraction_theorem (f : unit_disk → frontier unit_disk):
  ¬ retraction f :=
sorry


theorem brouwer_fixed_point (f : unit_disk → unit_disk) :
  ∃x, f x = x :=
begin
  by_contradiction,
  have hno_fix : ∀x, f x ≠ x := begin
    rw ← not_exists,
    assumption,
   end,

  let r : unit_disk → frontier unit_disk :=
    sorry,

  have hf_retract : retraction r := {
    retract_continuous := sorry,
    hy_sub_x := sorry,
    retract_of_inclusion_id := sorry,
  },

  have hf_not_retract : ¬ retraction r := no_retraction_theorem r,
  contradiction,
end
