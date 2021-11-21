import topology.basic
import topology.continuous_function.basic

@[class]
structure pointed_space (X : Type) extends topological_space X : Type :=
(basepoint : X)

structure pointed_continuous_map (X Y : Type)
  [pointed_space X] [pointed_space Y]
  extends continuous_map X Y : Type :=
(pointed_map : to_fun (@pointed_space.basepoint X _) = @pointed_space.basepoint Y _)

notation `Cp(` X `, ` Y `)` := pointed_continuous_map X Y


instance pointed_space.subspace {α : Type} [pointed_space α] (X : set α) (h_basepoint_in_X : (pointed_space.basepoint ∈ X)) :
  pointed_space X := {
  basepoint := subtype.mk pointed_space.basepoint (by simp [h_basepoint_in_X])
}

instance pointed_space.superspace {α : Type} [topological_space α] (X : set α) [pointed_space X] :
  pointed_space α := {
  basepoint := (@pointed_space.basepoint X _)
}
