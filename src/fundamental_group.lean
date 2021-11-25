import topology.basic
import topology.metric_space.basic
import topology.path_connected
import topology.continuous_function.basic
import topology.homotopy.fundamental_groupoid
import category_theory.endomorphism
import category_theory.groupoid
import algebra.category.Group.basic
import category_theory.category.basic
import category_theory.types
import .pointed_space

-- notation `↾` f : 200 := category_theory.as_hom f

def fundamental_group {X : Type} [topological_space X] (Xp : pointed_space X) : Type :=
@category_theory.Aut
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  Xp.basepoint

noncomputable instance fundamental_group.group {X : Type} [topological_space X] {Xp : pointed_space X} :
   group (fundamental_group Xp) :=
@category_theory.Aut.group
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  Xp.basepoint

noncomputable instance fundamental_group.mul_one_class {X : Type} [topological_space X] {Xp : pointed_space X} :
  mul_one_class (fundamental_group Xp) := {
  one := fundamental_group.group.one,
  mul := fundamental_group.group.mul,
  one_mul := fundamental_group.group.one_mul,
  mul_one := fundamental_group.group.mul_one,
}

def loop {X : Type} [topological_space X] (Xp : pointed_space X) : Type :=
path Xp.basepoint Xp.basepoint

noncomputable def conn_path {X : Type} [topological_space X] [path_connected_space X] (p q : X) :
  @quiver.hom (fundamental_groupoid X) _ p q :=
@quotient.mk (path p q) (path.homotopic.setoid p q) (joined.some_path (path_connected_space.joined p q))

noncomputable theorem iso_fg_of_path_conn {X : Type} [topological_space X] [path_connected_space X]
  (Xp : pointed_space X) (Xq : pointed_space X) :
  (fundamental_group Xp) ≅ (fundamental_group Xq) := {
  hom := λγ, category_theory.iso.mk
    ((conn_path Xq.basepoint Xp.basepoint) ≫ γ ≫ (conn_path Xp.basepoint Xq.basepoint))
    ((conn_path Xq.basepoint Xp.basepoint) ≫ γ⁻¹ ≫ (conn_path Xp.basepoint Xq.basepoint))
    sorry
    sorry,
  inv := λγ, category_theory.iso.mk
    ((conn_path Xp.basepoint Xq.basepoint) ≫ γ ≫ (conn_path Xq.basepoint Xp.basepoint))
    ((conn_path Xp.basepoint Xq.basepoint) ≫ γ ≫ (conn_path Xq.basepoint Xp.basepoint))
    sorry
    sorry,
}

-- TODO: figure out composition below
noncomputable def induced_hom {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  (fundamental_group Xp) →* (fundamental_group Yq) := {
  to_fun := λγ, {
    hom := sorry,
    inv := sorry,
    hom_inv_id' := sorry,
    inv_hom_id' := sorry,
  },
  map_one' := sorry,
  map_mul' := sorry,
}

lemma surj_hom_of_surj {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  function.surjective f → function.surjective (induced_hom f) :=
sorry

