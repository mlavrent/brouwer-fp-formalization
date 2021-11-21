import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.endomorphism
import category_theory.groupoid
import algebra.category.Group.basic
import category_theory.category.basic

import .pointed_space

def fundamental_group (X : Type) [pointed_space X] : Type :=
@category_theory.Aut
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  pointed_space.basepoint

noncomputable instance fundamental_group.group {X : Type} [pointed_space X] : group (fundamental_group X) :=
@category_theory.Aut.group
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  pointed_space.basepoint

noncomputable instance fundamental_group.mul_one_class {X : Type} [pointed_space X] : mul_one_class (fundamental_group X) := {
  one := fundamental_group.group.one,
  mul := fundamental_group.group.mul,
  one_mul := fundamental_group.group.one_mul,
  mul_one := fundamental_group.group.mul_one,
}

-- example : ∀(x : fundamental_group ℤ 1), x := sorry

-- TODO: figure out composition below
noncomputable def induced_hom {X Y : Type} [pointed_space X] [pointed_space Y] (f : C(X, Y)) :
  (fundamental_group X) →* (fundamental_group Y) := {
  to_fun := λγ, {
    hom := sorry, --f ∘ γ.hom,
    inv := sorry, --γ.inv ∘ f,
    hom_inv_id' := sorry,
    inv_hom_id' := sorry,
  },
  map_one' := sorry,
  map_mul' := sorry,
}

lemma surj_hom_of_surj {X Y : Type} [topological_space X] [topological_space Y] {x : X} {y : Y} (f : C(X, Y)) (hpointed : f x = y) :
  function.surjective f → function.surjective (induced_hom f hpointed) :=
sorry

