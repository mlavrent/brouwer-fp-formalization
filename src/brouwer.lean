import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

import .disk
import .retraction

-- TODO: see if we can do this via classical.some i.e. ray & circle have ∩
def ray_fn (f : disk → disk) (h_no_fix : ∀x, f x ≠ x) : C(disk, frontier disk) :=
sorry

lemma ray_fn_continuous (f : C(disk, disk)) (h_no_fix : ∀x, f x ≠ x) :
  continuous (ray_fn f h_no_fix) :=
sorry

lemma ray_fn_fdisk_eq_id (f : C(disk, disk)) (h_no_fix : ∀x, f x ≠ x) :
  (ray_fn f h_no_fix) ∘ (set.inclusion frontier_disk_subset_disk) = id :=
begin
  apply funext,
  intro x,
  simp [ray_fn],
  sorry,
end

lemma ray_fn_fdisk_eq_id₂ (f : C(disk, disk)) (h_no_fix : ∀x, f x ≠ x) :
  ∀x, (ray_fn f h_no_fix) (set.inclusion frontier_disk_subset_disk x) = x :=
begin
  intro x,
  rw ← function.comp_app (ray_fn f h_no_fix) _ _,
  rw ray_fn_fdisk_eq_id,
  exact id.def x,
end




theorem brouwer_fixed_point (f : C(disk, disk)) :
  ∃x, f x = x :=
begin
  by_contradiction,
  rw not_exists at h,

  let r : disk → frontier disk :=
    ray_fn f h,

  have hf_retract : retraction r := {
    retract_continuous := ray_fn_continuous f h,
    hy_sub_x := frontier_disk_subset_disk,
    inclusion_right_inv := begin
      simp [r],
      intro x,
      apply ray_fn_fdisk_eq_id₂,
    end,
  },

  have hf_not_retract : ¬ retract r := no_retraction_theorem r,
  contradiction,
end
