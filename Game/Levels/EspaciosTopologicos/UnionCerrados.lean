import Game.Levels.EspaciosTopologicos.InterseccionCerrados
import Mathlib.Data.Set.Lattice

open espacio_topologico Set


World "EspaciosTopologicos"
Level 5
Title "La unión de dos cerrados es cerrado."

Introduction "Despues de un reto un poco más dificil, vamos a ver uno más
fácil: la unión de dos cerrados es cerrado.
"

variable {X : Type} [espacio_topologico X]

/--
Dados dos cerrados `U` y, `V`, su unión `U ∪ V` es cerrado
-/
TheoremDoc union_cerrados as "union_cerrados" in "Espacios Topológicos"

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
