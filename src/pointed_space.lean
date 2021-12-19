import topology.basic
import topology.continuous_function.basic

structure pointed_space (X : Type) [topological_space X] : Type :=
-- (to_topological_space : topological_space X)
(basepoint : X)

structure pointed_continuous_map {X Y : Type} [topological_space X] [topological_space Y]
  (Xp : pointed_space X) (Yp : pointed_space Y)
  extends continuous_map X Y : Type :=
(pointed_map : to_fun Xp.basepoint = Yp.basepoint)

notation `Cp(` Xp `, ` Yp `)` := pointed_continuous_map Xp Yp

instance has_coe_to_fun.pointed_continuous_map {X Y : Type} [topological_space X] [topological_space Y]
  (Xp : pointed_space X) (Yp : pointed_space Y) :
  has_coe_to_fun Cp(Xp, Yp) (λ _, X → Y) :=
⟨λf, pointed_continuous_map.to_continuous_map f⟩

def pointed_map_of_continuous_map {X Y : Type} [topological_space X] [topological_space Y] [inhabited X] (f : C(X, Y)) :
  Cp((pointed_space.mk (inhabited.default X)), (pointed_space.mk (f (inhabited.default X)))) := {
  to_fun := f,
  pointed_map := by simp,
}

lemma nonempty_of_pointed_space {X : Type} [topological_space X] (Xp : pointed_space X) :
  nonempty X :=
begin
  apply @nonempty_of_exists _ (λ_, true),
  apply exists.intro Xp.basepoint,
  tautology,
end

lemma ptd_continuous_map_is_original {X Y : Type} [topological_space X] [topological_space Y] [inhabited X] (f : C(X, Y)) :
  (pointed_map_of_continuous_map f).to_continuous_map = f :=
begin
  ext,
  simp [pointed_map_of_continuous_map],
end
