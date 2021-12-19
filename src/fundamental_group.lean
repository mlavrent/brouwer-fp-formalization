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

example {X Y : Type} [setoid X] (f : X → Y) (x : X) (h : ∀ (a b : X), a ≈ b → f a = f b) :
  (quotient.lift f h) ⟦x⟧ = f x := begin
    exact quotient.lift_mk f h x
  end

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

noncomputable instance category.topological_space (X : Type) [topological_space X] : category_theory.category X :=
fundamental_groupoid.category_theory.groupoid.to_category

@[simp]
def space_of_fg {X : Type} [topological_space X] (p : fundamental_groupoid X) : X := p
notation `↘` p : 70 := space_of_fg p

def fg_of_space {X : Type} [topological_space X] (p : X) : fundamental_groupoid X := p
notation `↗` p : 70 := fg_of_space p

def path_quotient_of_groupoid_arrow {X : Type} [topological_space X] {a b : fundamental_groupoid X} :
  (a ⟶ b) = quotient (path.homotopic.setoid (↘a) (↘b)) := rfl


lemma fg_mul {X : Type} [topological_space X] {Xp : pointed_space X} (a b : fundamental_group Xp) :
  a * b = category_theory.iso.trans b a :=
by refl

lemma fg_one {X : Type} [topological_space X] {Xp : pointed_space X}:
  (1 : fundamental_group Xp) = @category_theory.iso.refl X (category.topological_space X) (Xp.basepoint) :=
by refl

/--
Type alias for working with loops in a space X with basepoint p.
-/
def loop {X : Type} [topological_space X] (Xp : pointed_space X) : Type :=
path Xp.basepoint Xp.basepoint

example (X Y : Type) (f : X → Y) (a b : X) : a = b → f a = f b :=
begin
  exact congr_arg (λ (a : X), f a),
end


/-
The following is a set of helper lemmas for rewriting computations on ℝ.
-/

@[simp]
lemma sub_12 : (1 : ℝ) - (2 : ℝ) = -1 :=
by linarith

@[simp]
lemma arith (s : ℝ) : s * (1 - |1 - 2|) = 0 :=
calc s * (1 - |1 - 2|) = s * (1 - |(-1)|) : by rw sub_12
... = s * (1 - 1) : by simp
... = s * 0 : by rw sub_self
... = 0 : mul_zero s

@[simp]
lemma arith2 (a : ℝ) : 2 * a ≤ 1 + 1 ↔ a ≤ 1 := begin
  split;
  { intros, linarith, },
end

@[simp]
lemma unit_interval_bound_fst (st : unit_interval × unit_interval) : st.fst ≥ 0 ∧ st.fst ≤ 1 :=
begin
  apply and.intro,
  exact unit_interval.nonneg',
  exact unit_interval.le_one',
end

@[simp]
lemma unit_interval_bound_snd (st : unit_interval × unit_interval) : st.snd ≥ 0 ∧ st.snd ≤ 1 :=
begin
  apply and.intro,
  exact unit_interval.nonneg',
  exact unit_interval.le_one',
end

/--
Defines the homotopy between an out-and-back path and a point i.e. for path γ
starting at point p, γ * γ⁻¹ ∼ p.
-/
noncomputable def linear_symm_homotopy {X : Type} [topological_space X] {p q : X} (γ : path p q) :
  path.homotopy (path.refl p) (γ.trans γ.symm) := {
  to_homotopy := {
    to_fun := λst, γ (subtype.mk (st.fst.val * (1 - |1 - 2 * st.snd.val|)) begin
      simp,
      have hs : st.fst ≥ 0 ∧ st.fst ≤ 1 := unit_interval_bound_fst st,
      have ht : st.snd ≥ 0 ∧ st.snd ≤ 1 := unit_interval_bound_snd st,
      apply and.intro;
      apply or.elim (abs_cases ((1 : ℝ) - 2 * ↑(st.snd)));
      intro h;
      rw (and.elim_left h),
      { apply mul_nonneg,
        repeat {simp, tautology}, },
      { apply mul_nonneg,
        repeat {simp, tautology}, },
      { apply mul_le_one,
        tautology, simp, tautology, simp, linarith, },
      { apply mul_le_one,
        tautology, simp, tautology, simp, linarith, },
    end),
    to_fun_zero := by simp,
    to_fun_one := begin
      simp,
      intros t ht,
      rw path.trans_apply,
      split_ifs;
      simp [unit_interval.symm];
      apply congr_arg;
      apply subtype.eq;
      simp;
      rw subtype.coe_mk at h,
      { have h_abs_pos : 0 ≤ 1 - 2 * t := by linarith, -- TODO: finish this!
        rw abs_of_nonneg h_abs_pos,
        linarith, },
      { have h_abs_neg : 1 - 2 * t ≤ 0 := by linarith,
        rw abs_of_nonpos h_abs_neg,
        linarith, },
    end,
  },
  prop' := begin
    intros s t ht_endpoint,
    simp at *,
    apply or.elim ht_endpoint;
    intro ht;
    apply and.intro;
    simp [ht],
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

/--
Similar to `iso_fg_of_path_conn`, except it defines a group isomorphism between the two fundamental groups
as opposed to a category isomorphism.
-/
noncomputable theorem mulequiv_fg_of_path_conn {X : Type} [topological_space X] [path_connected_space X]
  (Xp : pointed_space X) (Xq : pointed_space X) :
  (fundamental_group Xp) ≃* (fundamental_group Xq) :=
let α := conn_path Xp.basepoint Xq.basepoint in {
  to_fun := λγ, category_theory.iso.mk
    (α.inv ≫ γ.hom ≫ α.hom)
    (α.inv ≫ γ.inv ≫ α.hom)
    (by simp)
    (by simp),
  inv_fun := λγ, category_theory.iso.mk
    (α.hom ≫ γ.hom ≫ α.inv)
    (α.hom ≫ γ.inv ≫ α.inv)
    (by simp)
    (by simp),

  left_inv :=
    begin
      intro γ,
      simp,
      apply category_theory.iso.ext,
      refl,
    end,
  right_inv :=
    begin
      intro γ,
      simp,
      apply category_theory.iso.ext,
      refl,
    end,
  map_mul' :=
    begin
      intros γ₁ γ₂,
      rw @fg_mul _ _ Xq,
      apply category_theory.iso.ext,
      rw fg_mul,
      simp,
    end,
}

/--
Given a continuous function between pointed spaces, we can create a functor between the
associated fundamental groupoids of the spaces.
-/
noncomputable def induced_groupoid_functor {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  fundamental_groupoid X ⥤ fundamental_groupoid Y := {
  obj := f,
  map := begin
    intros p₁ p₂ α,
    let x_setoid := path.homotopic.setoid (↘p₁) (↘p₂),
    let y_setoid := path.homotopic.setoid (f ↘p₁) (f ↘p₂),
    have h_cont : continuous ⇑f := f.to_continuous_map.continuous,

    let f_path : path (↘p₁) (↘p₂) → path (f ↘p₁) (f ↘p₂) :=
      λγ, {
        to_continuous_map := {
          to_fun := f ∘ γ,
          continuous_to_fun := begin
            apply continuous.comp,
            { exact continuous_map.continuous_to_fun f.to_continuous_map, },
            { exact continuous_map.continuous_to_fun γ.to_continuous_map, },
          end,
        },
        source' := by simp,
        target' := by simp,
      },
    let f_path_class : path (↘p₁) (↘p₂) → ((f p₁) ⟶ (f p₂)) :=
      λγ, @quotient.mk _ y_setoid (f_path γ),
    let f_lift : (p₁ ⟶ p₂) → ((f p₁) ⟶ (f p₂)) :=
      begin
        apply @quotient.lift _ _ x_setoid f_path_class,
        intros γ₁ γ₂ h_homotopic,
        apply quotient.sound,
        apply nonempty.intro,
        exact {
          to_homotopy := {
            to_fun := f ∘ ⇑(classical.choice h_homotopic),
            to_fun_zero := by simp,
            to_fun_one := by simp,
          },
          prop' := begin
            intros s t ht_endpoint,
            simp at *,
            apply or.elim ht_endpoint;
            intro ht;
            apply and.intro;
            simp [ht],
          end,
        },
      end,
    exact f_lift α,
  end,
  map_comp' := begin
    intros a b c δ ε,
    rw path_quotient_of_groupoid_arrow at δ,
    rw path_quotient_of_groupoid_arrow at ε,
    simp,
    -- rw quotient.lift_mk,
    sorry,
  end,
}

notation `↟` f : 70 := induced_groupoid_functor f

-- ℤ
/--
Helpful rewrite lemma for dealing with the
-/
@[simp]
lemma f_of_induced_groupoid_functor {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) (x : X) :
  (↟f).obj x = f x := by refl

@[simp]
lemma induced_functor_of_id {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  (↟f).map (𝟙 Xp.basepoint) = 𝟙 ((↟f).obj Xp.basepoint) := by simp

/--
Given a function f : X → Y, returns the induced map between the fundamental groups i.e.
returns f⋆ : π₁(X) → π₁(Y).
-/
noncomputable def induced_hom {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  (fundamental_group Xp) →* (fundamental_group Yq) :=
let h_pointed : f Xp.basepoint = Yq.basepoint := pointed_continuous_map.pointed_map f in
let q1 : (↟f).obj Xp.basepoint ⟶ Yq.basepoint := begin simp [h_pointed], exact 𝟙 Yq.basepoint, end in
let q2 : Yq.basepoint ⟶ (↟f).obj Xp.basepoint := begin simp [h_pointed], exact 𝟙 Yq.basepoint, end in
let h_qinv₁ : q1 ≫ q2 = 𝟙 ((↟f).obj Xp.basepoint) := sorry in
let h_qinv₂ : q2 ≫ q1 = 𝟙 Yq.basepoint := sorry in
{
  to_fun := λγ, {
    hom := q2 ≫ (↟f).map γ.hom ≫ q1,
    inv := q2 ≫ (↟f).map γ.inv ≫ q1,
    hom_inv_id' :=
      calc (q2 ≫ (↟f).map γ.hom ≫ q1) ≫ q2 ≫ (↟f).map γ.inv ≫ q1 = q2 ≫ ((↟f).map γ.hom ≫ (q1 ≫ q2) ≫ (↟f).map γ.inv) ≫ q1 : by simp
        ... = q2 ≫ ((↟f).map γ.hom ≫ (↟f).map γ.inv) ≫ q1 : by simp [h_qinv₁]
        ... = q2 ≫ 𝟙 ((↟f).obj Xp.basepoint) ≫ q1 : begin rw ← category_theory.functor.map_comp (↟f) γ.hom γ.inv, simp, end
        ... = 𝟙 Yq.basepoint : by simp [h_qinv₂],
    inv_hom_id' :=
      calc (q2 ≫ (↟f).map γ.inv ≫ q1) ≫ q2 ≫ (↟f).map γ.hom ≫ q1 = q2 ≫ ((↟f).map γ.inv ≫ (q1 ≫ q2) ≫ (↟f).map γ.hom) ≫ q1 : by simp
        ... = q2 ≫ ((↟f).map γ.inv ≫ (↟f).map γ.hom) ≫ q1 : by simp [h_qinv₁]
        ... = q2 ≫ 𝟙 ((↟f).obj Xp.basepoint) ≫ q1 : begin rw ← category_theory.functor.map_comp (↟f) γ.inv γ.hom, simp, end
        ... = 𝟙 Yq.basepoint : by simp [h_qinv₂],
  },
  map_one' :=
    begin
      rw @fg_one _ _ Yq,
      ext,
      simp,
      rw ← h_qinv₂,
      sorry,
    end,
  map_mul' :=
    begin
      intros δ ε,
      ext,
      rw @fg_mul _ _ Yq _ _,
      simp [h_qinv₁],
      sorry,
    end,
}

/--
Given a surjective map f : X → Y, the induced map f⋆ on fundamental groups is also surjective.
-/
lemma surj_hom_of_surj {X Y : Type} [topological_space X] [topological_space Y]
  {Xp : pointed_space X} {Yq : pointed_space Y} (f : Cp(Xp, Yq)) :
  function.surjective f → function.surjective (induced_hom f) :=
begin
  intros h_f_surj y_loop,
  let y_loop_rep : path Yq.basepoint Yq.basepoint :=
    classical.some (@quotient.exists_rep _ (path.homotopic.setoid Yq.basepoint Yq.basepoint) y_loop.hom),
  let x_loop_rep : path Xp.basepoint Xp.basepoint := {
    to_fun := λt, classical.some (h_f_surj (y_loop_rep t)),
    continuous_to_fun := sorry,
    source' :=
      begin
        simp,
        -- classical.some_spec
        sorry,
      end,
    target' :=
      begin
        simp,
        -- classical.some_spec
        sorry,
      end,
  },
  let x_loop : fundamental_group Xp :=
    sorry, --@quotient.mk _ (path.homotopic.setoid Xp.basepoint Xp.basepoint) x_loop_rep,
  apply exists.intro x_loop,
  sorry,
end
