import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

import .disk
import .retraction


def brouwer_func (f : disk → disk) (h_no_fix : ∀x, f x ≠ x) : C(disk, frontier disk) :=
sorry

lemma brouwer_func_continuous (f : C(disk, disk)) (h_no_fix : ∀x, f x ≠ x) :
  continuous (brouwer_func f h_no_fix) :=
sorry

lemma brouwer_func_circle_eq_id (f : C(disk, disk)) (h_no_fix : ∀x, f x ≠ x) :
  ∀(x : frontier disk), brouwer_func f h_no_fix ↑x = x :=
begin
  intro x,
  simp [brouwer_func],
  sorry,
end


theorem brouwer_fixed_point (f : C(disk, disk)) :
  ∃x, f x = x :=
begin
  by_contradiction,
  have h_no_fix : ∀x, f x ≠ x := begin
    rw ← not_exists,
    assumption,
   end,

  let r : disk → frontier disk :=
    brouwer_func f h_no_fix,

  have hf_retract : retract r := {
    retract_continuous := brouwer_func_continuous f h_no_fix,
    hy_sub_x := frontier_disk_subset_disk,
    inclusion_right_inv := begin
      intro x,
      simp [r],
      apply brouwer_func_circle_eq_id f h_no_fix,
    end,
  },

  have hf_not_retract : ¬ retract r := no_retraction_theorem r,
  contradiction,
end
