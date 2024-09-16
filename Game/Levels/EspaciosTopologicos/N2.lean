import Game.Levels.EspaciosTopologicos.N1
open Set espacio_topologico

World "EspaciosTopologicos"
Level 9
Title "Propiedades de entornos 2"


/--
Las familias de los entornos de cada punto en un espacio topológico cumplen `N2`.
-/
TheoremDoc entornos_N2 as "entornos_N2" in "Espacios Topológicos"

Statement entornos_N2 (X : Type) [espacio_topologico X] : ∀ (x : X), ∀ N , entorno x N →  x ∈ N := by
  Hint (hidden := true) "Como de costumbre, puedes empezar
  tomando un `x` genérico con `intro`."
  intro x N h
  Hint (hidden := true) "Puedes reescribir lo que significa ser
  entorno en `{h}` con `rw [def_entorno] at `{h}`."
  rw [def_entorno] at h
  Hint (hidden := true) "Como `{h}` te asegura que existen conjuntos
  con ciertas propiedades, puedes elegir uno con `choose U hUab hxU hUN using `{h}`."
  choose U hUab hxU hUN using h
  Hint (hidden := true) "Para aplicar `{hUN}`, usa `apply {hUN}`."
  apply hUN
  Hint (hidden := true) "El objetivo es exactamente `{hxU}`."
  exact hxU
