import Game.Levels.EspaciosTopologicos.InterseccionCerrados
import Mathlib.Data.Set.Lattice




World "EspaciosTopologicos"
Level 5
Title "La unión de dos cerrados es cerrado."

Introduction "Despues de un reto un poco más dificil, vamos a ver uno más
fácil: la unión de dos cerrados es cerrado.
"

/--
Si `A` y `B` son dos conjuntos, `compl_union A B` dice que
(A ∪ B)ᶜ = Aᶜ ∩ Bᶜ
-/
TheoremDoc Set.compl_union as "compl_union" in "Utilidades"

/--
Si `A` y `B` son dos conjuntos, `compl_inter A B` dice que
(A ∩ B)ᶜ = Aᶜ ∪ Bᶜ
-/
TheoremDoc Set.compl_inter as "compl_inter" in "Utilidades"

NewTheorem Set.compl_union Set.compl_inter


namespace topo

open topo espacio_topologico Set

variable {X : Type} [espacio_topologico X]

/--
Dados dos cerrados `U` y, `V`, su unión `U ∪ V` es cerrado
-/
TheoremDoc topo.union_cerrados as "union_cerrados" in "Espacios Topológicos"

/--
Dados dos cerrados `U` y, `V`, su unión `U ∪ V` es cerrado
-/
Statement union_cerrados (U V : Set X) (hU : U ∈ cerrados) (hV : V ∈ cerrados) :
    U ∪ V ∈ cerrados := by
  Hint (hidden := true) "Hay varios sitios donde puedes reescribir la definición de cerrado."
  rw [def_cerrado] at *
  Hint (hidden := true) "El complementario de una unión puede simplificarse a una intersección."
  simp only [compl_union]
  Hint (hidden := true) "¿Qué puedes aplicar para demostrar que la intersección de dos abiertos es abierto?"
  apply interseccion_abiertos
  · exact hU
  · exact hV

end topo
