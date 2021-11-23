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

notation `↾` f : 200 := category_theory.as_hom f

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

def loop (X : Type) [pointed_space X] : Type :=
path (@pointed_space.basepoint X) (@pointed_space.basepoint X)

noncomputable def conn_path {X : Type} [topological_space X] [path_connected_space X] (p q : X) :
  @quiver.hom (fundamental_groupoid X) _ p q :=
@quotient.mk (path p q) (path.homotopic.setoid p q) (joined.some_path (path_connected_space.joined p q))

theorem iso_fg_of_path_conn {X : Type} [topological_space X] [path_connected_space X] (ps₁ : pointed_space X) (ps₂ : pointed_space X):
  (@fundamental_group X ps₁) ≅ (@fundamental_group X ps₂) := {
  hom := λγ, category_theory.iso.mk
    ((conn_path (@pointed_space.basepoint ps₁) (@pointed_space.basepoint ps₂)) ≫ γ.hom ≫ (conn_path (@pointed_space.basepoint ps₂) (@pointed_space.basepoint ps₁)))
    ((conn_path (@pointed_space.basepoint ps₁) (@pointed_space.basepoint ps₂)) ≫ γ.inv ≫ (conn_path (@pointed_space.basepoint ps₁) (@pointed_space.basepoint ps₂)))
    sorry
    sorry, -- do (ps₁ -> ps₂) * γ * (ps₂ -> ps₁)
  inv := λγ, sorry, -- do opposite of above
}

-- TODO: figure out composition below
noncomputable def induced_hom {X Y : Type} [pointed_space X] [pointed_space Y] (f : Cp(X, Y)) :
  (fundamental_group X) →* (fundamental_group Y) := {
  to_fun := λγ, {
    hom := @category_theory.category_struct.comp _ _ _ _ _ γ.hom f,
    inv := ↾f ≫ γ.inv,
    hom_inv_id' := sorry,
    inv_hom_id' := sorry,
  },
  map_one' := sorry,
  map_mul' := sorry,
}

lemma surj_hom_of_surj {X Y : Type} [pointed_space X] [pointed_space Y] (f : Cp(X, Y)) :
  function.surjective f → function.surjective (induced_hom f) :=
sorry

