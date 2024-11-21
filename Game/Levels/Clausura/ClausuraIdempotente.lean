import Game.Levels.Clausura.CaracterizacionCerradoClausura

World "Clausura"
Level 8
Title "Clausura de la clausura."

Introduction "
La clausura de la clausura de un conjunto es la clausura
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`, `clausura (clausura A) = clausura A`
-/
TheoremDoc topo.clausura_clausura as "clausura_clausura" in "Clausura"

Statement clausura_clausura : clausura (clausura A) = clausura A := by
  Hint (hidden := true) "Observa que, según el resultado anterior,
  el objetivo es equivalente a que `clausura {A}` sea cerrado.

  Reescríbelo en esos términos."
  rw [← caracterizacion_cerrado_clausura]
  Hint (hidden := true) "Puedes aplicar un resultado que afirma exactamente eso."
  apply clausura_cerrado

end topo
