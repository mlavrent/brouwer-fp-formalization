import topology.basic
import topology.metric_space.basic
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.endomorphism
import category_theory.groupoid
import algebra.category.Group.basic
import category_theory.category.basic

def fundamental_group (X : Type) [topological_space X] (p : X) : Type :=
@category_theory.Aut
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  p

noncomputable instance fundamental_group.group {X : Type} [topological_space X] {p : X} : group (fundamental_group X p) :=
@category_theory.Aut.group
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  p

noncomputable def induced_hom {X Y : Type} [topological_space X] [topological_space Y] {x : X} {y : Y} (f : continuous_map X Y) (hpointed : f x = y) :
  (fundamental_group X x) →* (fundamental_group Y y) := {
  to_fun := λ(a : fundamental_group X x), sorry,
  map_one' := sorry,
  map_mul' := sorry,
}