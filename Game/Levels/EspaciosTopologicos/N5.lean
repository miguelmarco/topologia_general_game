import Game.Levels.EspaciosTopologicos.N4
open Set espacio_topologico

World "EspaciosTopologicos"
Level 12
Title "Propiedades de entornos 5"


/--
Las familias de los entornos de cada punto en un espacio topológico cumplen `N3`.
-/
TheoremDoc entornos_N5 as "entornos_N5" in "Espacios Topológicos"

Statement entornos_N5 (X : Type) [espacio_topologico X] :∀ (x : X), ∀ (N : Set X), entorno x N → ∃ (N' : Set X), ∀ y ∈ N', entorno y N := by
  Hint (hidden := true) "Como de costumbre, puedes usar `intro` para introducir los
  elementos arbitrarios y sus hipótesis."
  intro x N hN
  Hint (hidden := true) "Puedes tomar un abierto intermedio entre `{x}` y `{N}` gracias
  a `{hN}` usando `choose`."
  choose U hUab hxU hUN using hN
  Hint (hidden := true) "Qué conjunto puedes usar para demostrar que existe
  un tal `N'`?"
  use U
  Hint (hidden := true) "Ahora deberías tomar un `y` arbitrario."
  intro y hy
  Hint (hidden := true) "¿Qué abierto intermedio puedes usar?"
  use U
