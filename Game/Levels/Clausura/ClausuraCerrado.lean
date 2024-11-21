import Game.Levels.Clausura.CaracterizacionClausuraEntornos

World "Clausura"
Level 3
Title "La clausura de un conjunto es un cerrado."

Introduction "Veamos un resultado fácil: la clausura de un conjunto siempre
es un cerrado.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Un punto `x` está en la clausura de `A` si y sólo si todo
entorno de `x`, interseca a `A`.
-/
TheoremDoc topo.clausura_cerrado as "clausura_cerrado" in "Clausura"

Statement clausura_cerrado : clausura A ∈ cerrados := by
  Hint (hidden := true) "Puede ser útil reescribir la definición de clausura."
  rw [def_clausura]
  Hint (hidden := true) "Como quieres ver que una intersección de cerrados
  es un cerrado, puedes aplicar un teorema que dice exactamente eso."
  apply cerrado_interseccion
  Hint (hidden := true) "Tienes que ver que esa familia de conjuntos
  está formada por cerrados, para eso, toma uno arbitrario con `intro`."
  intro C hC
  Hint (hidden := true) "Puedes separar `{hC}` en dos afirmaciones con `choose`
  o `cases'`."
  choose hC1 hC2 using hC
  exact hC1

end topo
