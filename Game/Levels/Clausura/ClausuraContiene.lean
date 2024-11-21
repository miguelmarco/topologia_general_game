import Game.Levels.Clausura.ClausuraContenidaEnCerrado


World "Clausura"
Level 5
Title "La clausura de un conjunto contiene al conjunto."

Introduction "Otro resultado fácil: la clausura de un conjunto
contiene al conjunto.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
La clausura de  un conjunto `A` contiene a `A`.
-/
TheoremDoc topo.clausura_contiene as "clausura_contiene" in "Clausura"

Statement clausura_contiene : A ⊆ clausura A := by
  Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
  toma un elemento arbitrario con `intro`."
  intro x hx
  Hint (hidden := true) "Puede ser útil reescribir la definición de clausura."
  rw [def_clausura]
  Hint (hidden := true) "Como tienes que ver que `{x}` está
  en una intersección (es decir, que está en todos los miembros de una
  familia), puedes tomar un elemento arbitrario de la familia con `intro`."
  intro C hC
  Hint (hidden := true) "Puedes separar `{hC}` en dos afirmaciones
  con `choose` o `cases'`."
  choose hC1 hC2 using hC
  apply hC2
  exact hx


end topo
