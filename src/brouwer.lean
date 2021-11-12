import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic

import .disk
import .retraction



-- lemma π₁_of_S₁_iso_ℤ : fundamental_groupoid disk 0 := sorry
-- lemma π₁_of_D₂_iso_0 : fundamental_groupoid unit_circle ≅ ℤ := sorry

def brouwer_func (f : disk → disk) (h_no_fix : ∀x, f x ≠ x) (a : disk) : frontier disk :=
sorry

lemma brouwer_func_continuous (f : disk → disk) (h_no_fix : ∀x, f x ≠ x) :
  continuous (brouwer_func f h_no_fix) :=
sorry

lemma brouwer_func_res_eq_id (f : disk → disk) (h_no_fix : ∀x, f x ≠ x) :
  ∀(x : frontier disk), brouwer_func f h_no_fix ↑x = x :=
sorry


theorem brouwer_fixed_point (f : disk → disk) :
  ∃x, f x = x :=
begin
  by_contradiction,
  have h_no_fix : ∀x, f x ≠ x := begin
    rw ← not_exists,
    assumption,
   end,

  let r : disk → frontier disk :=
    brouwer_func f h_no_fix,

  have hf_retract : retraction r := {
    retract_continuous := brouwer_func_continuous f h_no_fix,
    hy_sub_x := frontier_disk_subset_disk,
    retract_of_inclusion_id := begin
      ext; rw [id],
      { sorry, },
      { sorry, },
    end,
  },

  have hf_not_retract : ¬ retraction r := no_retraction_theorem r,
  contradiction,
end
