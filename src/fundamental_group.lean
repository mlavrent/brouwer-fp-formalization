import topology.basic
import topology.metric_space.basic
import topology.path_connected
import topology.continuous_function.basic
import topology.homotopy.basic
import topology.homotopy.fundamental_groupoid
import category_theory.endomorphism
import category_theory.groupoid
import algebra.category.Group.basic
import category_theory.category.basic
import category_theory.types
import .pointed_space

notation `↾` f : 200 := category_theory.as_hom f

/--
Define the fundamental group as the the automorphism group of the fundamental groupoid i.e.
the set of all arrows from the basepoint to itself (p ⟶ p).
-/
def fundamental_group {X : Type} [topological_space X] (Xp : pointed_space X) : Type :=
@category_theory.Aut
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  Xp.basepoint

/--
Use the automorphism group instance to give a group structure to the fundamental group.
-/
noncomputable instance fundamental_group.group {X : Type} [topological_space X] {Xp : pointed_space X} :
   group (fundamental_group Xp) :=
@category_theory.Aut.group
  X
  (@category_theory.groupoid.to_category (fundamental_groupoid X) _)
  Xp.basepoint

noncomputable instance category_struct.topological_space {X : Type} [topological_space X] : category_theory.category_struct X :=
fundamental_groupoid.category_theory.groupoid.to_category_struct

-- noncomputable instance fundamental_group.mul_one_class {X : Type} [topological_space X] {Xp : pointed_space X} :
--   mul_one_class (fundamental_group Xp) := {
--   one := fundamental_group.group.one,
--   mul := fundamental_group.group.mul,
--   one_mul := fundamental_group.group.one_mul,
--   mul_one := fundamental_group.group.mul_one,
-- }

/--
Type alias for working with loops in a space X with basepoint p.
-/
def loop {X : Type} [topological_space X] (Xp : pointed_space X) : Type :=
path Xp.basepoint Xp.basepoint

/--
Defines the homotopy between an out-and-back path and a point i.e. for path γ
starting at point p, γ * γ⁻¹ ∼ p.
-/
noncomputable def linear_symm_homotopy {X : Type} [topological_space X] {p q : X} (γ : path p q) :
  path.homotopy (path.refl p) (γ.trans γ.symm) := {
  to_homotopy := {
    to_fun := λst, γ (subtype.mk (st.fst.val * (|1 - 2 * st.snd.val|)) sorry),
    to_fun_zero := by simp,
    to_fun_one := begin
      simp,
      intros t ht,
      rw path.trans_apply,
      sorry,
    end,
  },
  prop' := begin -- TODO: is this what we want to prove?
    intros s t ht,
    simp,
    apply and.intro,
    { sorry, },
    { sorry, },
  end,
}

/--
Given a path connected space X and two points p, q, we return a path between them
along with the reverse path, bundled together.
-/
noncomputable def conn_path {X : Type} [topological_space X] [path_connected_space X] (p q : X) :
  @category_theory.iso (fundamental_groupoid X) _ p q :=
let pq_path := joined.some_path (path_connected_space.joined p q) in {
  hom := @quotient.mk (path p q) (path.homotopic.setoid p q) pq_path,
  inv := @quotient.mk (path q p) (path.homotopic.setoid q p) pq_path.symm,
  hom_inv_id' := begin
    apply quotient.sound,
    apply nonempty_of_exists,
    apply @exists.intro _ (λ_, true)
      (path.homotopy.symm (linear_symm_homotopy pq_path))
      (by tautology),
  end,
  inv_hom_id' := begin
    apply quotient.sound,
    apply nonempty_of_exists,
    let homotopy := linear_symm_homotopy pq_path.symm,
    rw path.symm_symm at homotopy,
    apply @exists.intro _ (λ_, true)
      (path.homotopy.symm homotopy)
      (by tautology),
  end,
}

/--
Given a path connected space X, the fundamental group is independent of which basepoint was used.
-/
noncomputable theorem iso_fg_of_path_conn {X : Type} [topological_space X] [path_connected_space X]
  (Xp : pointed_space X) (Xq : pointed_space X) :
  (fundamental_group Xp) ≅ (fundamental_group Xq) :=
let α := conn_path Xp.basepoint Xq.basepoint in {
  hom := λγ, category_theory.iso.mk
    (α.inv ≫ γ.hom ≫ α.hom)
    (α.inv ≫ γ.inv ≫ α.hom)
    (by simp)
    (by simp),
  inv := λγ, category_theory.iso.mk
    (α.hom ≫ γ.hom ≫ α.inv)
    (α.hom ≫ γ.inv ≫ α.inv)
    (by simp)
    (by simp),
}

-- TODO: figure out composition below
/--
Given a function f : X → Y, returns the induced map between the fundamental groups i.e.
returns f⋆ : π₁(X) → π₁(Y).
-/
noncomputable def induced_hom {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  (fundamental_group Xp) →* (fundamental_group Yq) := {
  to_fun := λγ, {
    hom := γ.hom ≫ f, -- TODO: define f on fundamental groupoids;
    inv := sorry,
    hom_inv_id' := sorry,
    inv_hom_id' := sorry,
  },
  map_one' := sorry,
  map_mul' := sorry,
}

/--
Given a surjective map f : X → Y, the induced map f⋆ on fundamental groups is also surjective.
-/
lemma surj_hom_of_surj {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  function.surjective f → function.surjective (induced_hom f) :=
sorry
