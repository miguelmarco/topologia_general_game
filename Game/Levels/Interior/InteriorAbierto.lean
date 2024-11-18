import Game.Levels.Interior.CaracterizacionInteriorEntorno
open espacio_topologico Set Function

World "Interior"
Level 3
Title "El interior es abierto."

Introduction "El interior de un conjunto es abierto.
"

variable {X : Type} [espacio_topologico X]

/--
Dados un conjunto `A` `interior' A` es un abierto..
-/
TheoremDoc interior_abierto as "interior_abierto" in "Interior"

Statement interior_abierto (A : Set X) : interior' A ∈ abiertos := by
  Hint (hidden := true) "Prueba a reescribir la definición de interior."
  rw [def_interior]
  Hint (hidden := true) "Quieres ver que la unión de una familia
  es un abierto, así que puedes aplicar `union_abiertos`."
  apply union_abiertos
  Hint (hidden := true) "Ahora puedes tomar un elemento arbitrario con `intro`."
  intro U hU
  Hint (hidden := true) "`{hU}` te asegura que `{U}` cumple dos propiedades,
  puedes separarls con `choose` o `cases'`."
  choose hUab hUA using hU
  exact hUab
