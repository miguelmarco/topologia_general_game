import Game.Levels.ExteriorFronteraAislado.FronteraComplementario
World "ExteriorFronteraAislado"
Level 9
Title "Frontera."

Introduction "La frontera de un conjunto es la intersección de su clausura
y la de su complementario."

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`  en un espacio topológico,
`frontera_inter_clausura_compl A` dice que `frontera A =  clausura Aᶜ ∩ clausura A`.
-/
TheoremDoc topo.frontera_inter_clausura_compl as "frontera_inter_clausura_compl" in "Exterior/Frontera/Aislado"


Statement frontera_inter_clausura_compl : frontera A =  clausura Aᶜ ∩ clausura A := by
  Hint (hidden := true ) "Prueba a reescribir la frontera como el
  complementario del interior y el exterior."
  rw [frontera_compl_int_ext]
  Hint (hidden := true) "Prueba a simplificar la expresión."
  simp only [compl_union]
  Hint (hidden := true) "Puede ser útil reescribir el exterior."
  rw [def_exterior]
  Hint (hidden := true) "Recuerda que teniamos una fórmula para el complementario
  del interior. Puedes usarla para reescribir el objetivo."
  rw [complementario_interior]
  Hint (hidden := true) "Y había otra fórmula que nos dice que algo es
  el interior del complementario. Usala para reescribir."
  rw [← complementario_clausura]
  Hint (hidden := true) "Ya solo falta simplificar eliminando el doble
  complementario."
  rw [compl_compl]



end topo
