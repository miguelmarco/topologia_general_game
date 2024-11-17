import Game.Levels.Interior.CaracterizacionInterior
open espacio_topologico Set Function

World "Interior"
Level 2
Title "Caracterización del interior con entornos."

Introduction "Un punto `x` está en el interior de `A` si y sólo si
`A` es entorno de `x`.
"

variable {X : Type} [espacio_topologico X]

/--
Dados un conjunto `A` y un punto `x`, `caracterizacion_interior_entorno x A` dice que
`x ∈ interior' A ↔ entorno x A`.
-/
TheoremDoc caracterizacion_interior_entorno as "caracterizacion_interior_entorno" in "Interior"

Statement caracterizacion_interior_entorno (x : X) (A : Set X) : x ∈ interior' A ↔ entorno x A := by
  Hint (hidden := true) "Puede ser útil reescribir la caracterización anterior."
  rw [caracterizacion_interior]
  Hint (hidden := true) "Observa que lo que tenemos a la izquierda, recuerda mucho
  a la definicón de entorno. ¿Y si probamos a reescribir la definición de entorno?"
  rw [def_entorno]
