import Game.Levels.Interior.InteriorAbierto
open espacio_topologico Set Function

World "Interior"
Level 4
Title "El interior contiene a los abiertos contenidos."

Introduction "El interior de un conjunto contiene a cualquier abierto
contenido en el conjunto.
"

variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A` y un abierto `U` tal que `U ⊆ A`,
`interior_contiene_abierto` dice que `U ⊆ interior' A` .
-/
TheoremDoc interior_contiene_abierto as "interior_contiene_abierto" in "Interior"


Statement interior_contiene_abierto (A U  : Set X) (hUab : U ∈ abiertos) (hUA : U ⊆ A) :
    U ⊆ interior' A := by
  Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
  toma un elemento arbitrario con `intro`."
  intro x hx
  Hint (hidden := true) "Puede ser útil reescribir con la caracterización
  de los puntos del interior."
  rw [caracterizacion_interior]
  Hint (hidden := true) "¿Qué abierto puedes usar?"
  use U
