import Game.Levels.Interior.InteriorContenido


World "Interior"
Level 6
Title "El interior respeta subconjuntos."

Introduction "Veamos que, si un conjunto está contenido en otro, sus
interiores tambien cumplen esa relación.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dados subconjuntos `A` y `B`  tales que `A ⊆ B`,
`interior_monotono` dice que `interior A ⊆ interior B` .
-/
TheoremDoc topo.interior_monotono as "interior_monotono" in "Interior"


Statement interior_monotono (A B : Set X) (h : A ⊆ B): interior A ⊆ interior B := by
  Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
  toma un elemento arbitrario con `intro`."
  intro x hx
  Hint (hidden := true) "Puede ser útil reescribir con la caracterización
  de los puntos del interior."
  rw [caracterizacion_interior] at hx ⊢
  Hint (hidden := true) "`{hx}`  te asegura que existen abiertos intermedios entre `{x}`
  y `{A}`. Puedes elegir uno con `choose`."
  choose U hUab hxU hUA using hx
  Hint (hidden := true) "¿Qué abierto puedes usar?"
  use U
  Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
  fconstructor
  · exact hUab
  Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
  fconstructor
  · exact hxU
  · Hint (hidden := true) "Para demostrar que un subconjunto está contenido en otro,
    lo habitual es tomar un elemento arbitrario del primero (con `intro`) y ver que
    debe estar en el segundo."
    intro y hy
    Hint (hidden := true) "Puedes aplicar `{h}`."
    apply h
    Hint (hidden := true) "Puedes aplicar `{hUA}`."
    apply hUA
    exact hy

end topo
