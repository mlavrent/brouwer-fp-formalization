import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import analysis.normed_space.basic
import analysis.special_functions.trigonometric.basic

import .pointed_space

def disk : set (ℝ × ℝ) := metric.closed_ball (0 : ℝ × ℝ) 1
def circle : set (ℝ × ℝ) := metric.sphere (0 : ℝ × ℝ) 1
def pt : ℝ × ℝ := (1, 0)

noncomputable def disk.pointed_space : pointed_space disk :=
pointed_space.mk
  (subtype.mk pt (by simp [pt, disk, norm]))

noncomputable def circle.pointed_space : pointed_space circle :=
pointed_space.mk
  (subtype.mk pt (by simp [pt, circle, norm]))

instance inhabited.disk : inhabited disk :=
⟨subtype.mk pt (by simp [pt, disk, norm])⟩

lemma frontier_disk_eq_circle : frontier disk = circle :=
begin
  simp [disk, circle],
  rw frontier_closed_ball,
  linarith,
end

/--
Defines the identity homeomorphism between the boundary of the disk and the circle.
-/
noncomputable def frontier_disk_homeo_circle : frontier disk ≃ₜ circle := {
  to_fun := λx, subtype.mk (↑x) (begin rw ← frontier_disk_eq_circle, simp, end),
  inv_fun := λx, subtype.mk (↑x) (begin rw frontier_disk_eq_circle, simp, end),
  left_inv :=
    begin
      intro x,
      simp,
    end,
  right_inv :=
    begin
      intro x,
      simp,
    end,
}

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

instance has_lift.frontier_disk : has_lift (frontier disk) (disk) := {
  lift := begin
    intro fd,
    cases fd,
    have fd_val_in_disk : fd_val ∈ disk :=
      frontier_disk_subset_disk fd_property,
    exact subtype.mk fd_val fd_val_in_disk,
  end
}

noncomputable def frontier_disk.pointed_space : pointed_space (frontier disk) :=
pointed_space.mk
  (subtype.mk pt (by simp [pt, frontier_disk_eq_circle, circle, norm]))

instance disk.path_connected : path_connected_space disk := {
  nonempty := nonempty_of_pointed_space disk.pointed_space,
  joined :=
    begin
      intros x y,
      apply @nonempty_of_exists _ (λ_, true),
      apply exists.intro,
      tautology,

      sorry,
      -- exact {
      --   to_fun := sorry, --λt, (↑x) + t * (↑(x - y)),
      --   source' := sorry,
      --   target' := sorry,
      -- }
    end,
}

instance circle.path_connected : path_connected_space circle := {
  nonempty := nonempty_of_pointed_space circle.pointed_space,
  joined :=
    begin
      intros x y,
      apply @nonempty_of_exists _ (λ_, true),
      apply exists.intro,
      tautology,

      let x_ang : ℝ := sorry,
      let y_ang : ℝ := sorry,
      exact {
        to_fun := λt,
          subtype.mk
            (real.cos t, real.sin t)
            sorry,
        source' := sorry,
        target' := sorry,
      },
    end,
}

instance frontier_disk.path_connected : path_connected_space (frontier disk) :=
begin
  rw frontier_disk_eq_circle,
  exact circle.path_connected,
end
