import Game.Levels.Interior.InteriorContieneAbierto


World "Interior"
Level 5
Title "El interior está contenido en el subconjunto."

Introduction "Veamos que el interior de un subconjunto está contenido en el propio subconjunto.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A` en un espacio topológico,
`interior_contenido` dice que `interior A ⊆ A` .
-/
TheoremDoc topo.interior_contenido as "interior_contenido" in "Interior"


Statement interior_contenido (A : Set X)  : interior A ⊆ A := by
  Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
  toma un elemento arbitrario con `intro`."
  intro x hx
  Hint (hidden := true) "Puede ser útil reescribir `{hx}` con la caracterización
  de los puntos del interior."
  rw [caracterizacion_interior] at hx
  Hint (hidden := true) "Como `{hx}` te asegura que existen abiertos intermedios, puedes
  elegir uno con `choose`."
  choose U hUab hxU hUA using hx
  Hint (hidden := true) "Puedes aplicar `{hUA}`."
  apply hUA
  exact hxU

end topo
