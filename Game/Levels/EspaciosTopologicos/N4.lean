import Game.Levels.EspaciosTopologicos.N3
open Set espacio_topologico

World "EspaciosTopologicos"
Level 11
Title "Propiedades de entornos 4"


/--
Las familias de los entornos de cada punto en un espacio topológico cumplen `N3`.
-/
TheoremDoc entornos_N4 as "entornos_N4" in "Espacios Topológicos"

Statement entornos_N4 (X : Type) [espacio_topologico X] : ∀ (x : X), ∀ (N N2 : Set X), entorno x N → N ⊆ N2 → entorno x N2:= by
  Hint (hidden := true) "Como de costumbre, hay que introducir elementos
  arbitrarios e hipótesis con `intro`."
  intro x N1 N2 hN hN2
  Hint (hidden := true) "Como ya hemos visto antes, `{hN}`
  nos asegura la existencia de conjuntos con ciertas propiedades. Elige
  uno con `choose`."
  choose U hUab hxU hUN using hN
  Hint (hidden := true) "Para ver que `{N2}` es entorno de `x`, hay que
  dar un abierto intermedio. ¿Cual puede ser?"
  use U
  Hint (hidden := true) "Se puede separar el objetivo en varios usando
  `fconstructor`."
  fconstructor
  · exact hUab
  fconstructor
  · exact hxU
  Hint (hidden := true) "La forma habitual de demostrar un contenido de
  conjuntos, es tomar un elemento arbitrario con `intro`."
  intro y hy
  Hint (hidden := true) "Ahora puedes aplicar las hipótesis que te aseguran
  ciertos contenidos."
  apply hN2
  apply hUN
  exact hy
