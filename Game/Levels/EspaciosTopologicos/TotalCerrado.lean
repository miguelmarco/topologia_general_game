import Game.Levels.EspaciosTopologicos.VacioCerrado

open Set


World "EspaciosTopologicos"
Level 3
Title "El total es cerrado."

Introduction "Vamos a ver un resultado análogo al anterior: el conjunto
total también es un cerrado
"

open espacio_topologico Set

variable {X : Type} [espacio_topologico X]


/--
En un espacio topológico, el total es un cerrado.
-/
TheoremDoc cerrado_total as "cerrado_total" in "Espacios Topológicos"

/--
En un espacio topológico, el vacío es un cerrado.
-/
Statement cerrado_total : (univ : Set X) ∈ cerrados := by
  Hint (hidden := true) "Puedes usar `def_cerrado` para reescribir lo
  que significa que el vacío sea un cerrado."
  rw [def_cerrado]
  Hint (hidden := true) "El complementario del total se puede simplificar."
  simp only [compl_univ]
  Hint (hidden := true) "Hay un axioma que te dice exactamente eso."
  exact abierto_vacio
