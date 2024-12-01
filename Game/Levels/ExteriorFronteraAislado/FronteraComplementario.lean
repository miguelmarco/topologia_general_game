import Game.Levels.ExteriorFronteraAislado.FronteraCerrado
World "ExteriorFronteraAislado"
Level 8
Title "Frontera."

Introduction "La frontera de un conjunto coincide con la de su complementario.

En esta demostración, nos ayudará usar un lema auxiliar: `inter_comm` dice
que la intersección de dos conjuntos en conmutativa.

Análogamente, `union_comm` dice que la unión de dos conjuntos es conmutativa.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)

/--
Si `A` y `B` son dos conjuntos, `inter_comm A B` dice que `A ∩ B = B ∩ A.`
-/
TheoremDoc Set.inter_comm as "inter_comm" in "Utilidades"

/--
Si `A` y `B` son dos conjuntos, `union_comm A B` dice que `A ∪ B = B ∪ A.`
-/
TheoremDoc Set.union_comm as "union_comm" in "Utilidades"

NewTheorem Set.inter_comm Set.union_comm

/--
Dado un conjunto `A`  en un espacio topológico,
`frontera_complementario A` dice que `frontera Aᶜ =  frontera A`.
-/
TheoremDoc topo.frontera_complementario as "frontera_complementario" in "Exterior/Frontera/Aislado"


Statement frontera_complementario : frontera Aᶜ = frontera A := by
  Hint (hidden := true ) "Prueba a reescribir la frontera como el
  complementario del interior y el exterior."
  rw [frontera_compl_int_ext]
  Hint (hidden := true) "Puedes seguir reescribiendo."
  rw [frontera_compl_int_ext]
  Hint (hidden := true) "Puede ser útil reescribir el exterior
  como el complementario del interior."
  rw [def_exterior]
  Hint (hidden := true) "Puedes volver a reescribir el exterior."
  rw [def_exterior]
  Hint (hidden := true) "Ahora puedes eliminar el doble complementario
  reescribiendo con `compl_compl`."
  rw [compl_compl]
  Hint (hidden := true) "Solo falta reescribir aplicando la conmutatividad
  de la unión."
  rw [union_comm]

end topo
