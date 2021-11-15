import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

import .disk
import .retraction


def brouwer_func (f : disk → disk) (h_no_fix : ∀x, f x ≠ x) (a : disk) : frontier disk :=
sorry

lemma brouwer_func_continuous (f : disk → disk) (hf_cont : continuous f) (h_no_fix : ∀x, f x ≠ x) :
  continuous (brouwer_func f h_no_fix) :=
sorry

lemma brouwer_func_circle_eq_id (f : disk → disk) (hf_cont : continuous f) (h_no_fix : ∀x, f x ≠ x) :
  ∀(x : frontier disk), brouwer_func f h_no_fix ↑x = x :=
begin
  intro x,
  simp [brouwer_func],
  sorry,
end


theorem brouwer_fixed_point (f : disk → disk) (hf_cont : continuous f) :
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
    retract_continuous := brouwer_func_continuous f hf_cont h_no_fix,
    hy_sub_x := frontier_disk_subset_disk,
    retract_of_inclusion_id := begin
      apply funext,
      intro x,
      simp [r],
      apply brouwer_func_circle_eq_id f hf_cont h_no_fix,
    end,
  },

  have hf_not_retract : ¬ retract r := no_retraction_theorem r,
  contradiction,
end
