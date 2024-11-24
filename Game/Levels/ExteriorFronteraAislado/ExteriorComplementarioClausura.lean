import Game.Levels.ExteriorFronteraAislado.Exterior
World "ExteriorFronteraAislado"
Level 2
Title "El exterior es el complementario de la clausura."

Introduction "Veamos que el exterior de un conjunto es justo
el complementario de la clausura.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`  en un espacio topológico,
`exterior_complementario_clausura A` dice que `exterior A = (clausura A)ᶜ`.
-/
TheoremDoc topo.exterior_complementario_clausura as "exterior_complementario_clausura" in "Exterior/Frontera/Aislado"


Statement exterior_complementario_clausura : exterior A = (clausura A)ᶜ:= by
  Hint (hidden := true) "Reescribe la definición de exterior con `def_exterior`."
  rw [def_exterior]
  Hint (hidden := true) "Ya tenemos un teorema que nos dice cual es el complementario
  de una clausura."
  rw [complementario_clausura]


end topo
