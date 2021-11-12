import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

def disk : set (ℝ × ℝ) := metric.closed_ball (0 : ℝ × ℝ) 1


-- class has_scalar_mul (α : Type) [has_mul α] :=
-- (scalar_mul : α → α × α → α × α)


lemma frontier_subset_closed_set {α : Type} [topological_space α] (X : set α) :
  is_closed X → frontier X ⊆ X :=
begin
  intro hclosed,
  have hfx_sub_fxd : frontier X ⊆ X \ interior X :=
    by rw is_closed.frontier_eq hclosed,
  have hfxd_sub_x : X \ interior X ⊆ X :=
    set.diff_subset X (interior X),
  apply has_subset.subset.trans hfx_sub_fxd hfxd_sub_x,
end

lemma frontier_disk_subset_disk :
  frontier disk ⊆ disk :=
frontier_subset_closed_set disk metric.is_closed_ball

instance boundary_to_disk : has_lift (frontier disk) (disk) := {
  lift := begin
    intro fd,
    cases fd,
    have fd_val_in_disk : fd_val ∈ disk :=
      frontier_disk_subset_disk fd_property,
    exact subtype.mk fd_val fd_val_in_disk,
  end
}


