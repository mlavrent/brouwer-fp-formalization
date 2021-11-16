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

noncomputable instance fundamental_group.mul_one_class {X : Type} [topological_space X] (p : X) : mul_one_class (fundamental_group X p) := {
  one := fundamental_group.group.one,
  mul := fundamental_group.group.mul,
  one_mul := fundamental_group.group.one_mul,
  mul_one := fundamental_group.group.mul_one,
}

-- example : ∀(x : fundamental_group ℤ 1), x := sorry

-- TODO: figure out composition below
noncomputable def induced_hom {X Y : Type} [topological_space X] [topological_space Y] {x : X} {y : Y} (f : continuous_map X Y) (hpointed : f x = y) :
  (fundamental_group X x) →* (fundamental_group Y y) := {
  to_fun := λi, {
    hom := f ∘ i.hom,
    inv := i.inv ∘ f,
    hom_inv_id' := sorry,
    inv_hom_id' := sorry,
  },
  map_one' := sorry,
  map_mul' := sorry,
}