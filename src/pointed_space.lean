import topology.basic
import topology.continuous_function.basic

@[class]
structure pointed_space (α : Type) extends topological_space α : Type :=
(basepoint : α)

structure pointed_continuous_map (α β : Type)
  [pointed_space α] [pointed_space β]
  extends continuous_map α β : Type :=
(pointed_map : to_fun (@pointed_space.basepoint α _) = @pointed_space.basepoint β _)

notation `Cp(` X `, ` Y `)` := pointed_continuous_map X Y
