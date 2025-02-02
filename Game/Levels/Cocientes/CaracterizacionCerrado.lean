import Game.Levels.Cocientes.CocienteContinua
World "Cocientes"
Level 2
Title "Caracterización de cerrados en un cociente."

Introduction "
Un conjunto `C` en un cociente `X /' R` es cerrado si y sólo si
`π ⁻¹' C` es cerrado en `X`.
"



namespace topo
open topo espacio_topologico Set

variable {X : Type} [espacio_topologico X] [R : Equiv X]


/--
Un conjunto `C` en un cociente `X /' R` es cerrado si y solo si
`π ⁻¹' C`  es cerrado.
-/
TheoremDoc topo.caracterizacion_cerrado_cociente as "caracterizacion_cerrado_cociente" in "Cocientes"

Statement caracterizacion_cerrado_cociente (C : Set (X /' R)) : C ∈ cerrados  ↔ π ⁻¹' C ∈ cerrados := by
  Hint (hidden := true) "Puedes reescribir la definición de cerrado."
  rw [def_cerrado]
  Hint (hidden := true) "Puedes reescribir la definición de cerrado."
  rw [def_cerrado]
  Hint (hidden := true) "Puedes reescribir la definición de abierto en el cociente."
  rw [def_abierto_cociente]
  Hint (hidden := true) "Si te fijas en la definición de `π`,
  los dos conjuntos que queremos ver que son abiertos, son el mismo,
  así que el enunciado es cierto trivialmente."
  trivial

end topo
