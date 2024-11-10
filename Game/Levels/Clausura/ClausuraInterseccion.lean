import Game.Levels.Clausura.ClausuraNoEntorno
open espacio_topologico Set Function

World "Clausura"
Level 11
Title "Clausura de una intersección."

Introduction "
La clausura de una intersección está contenida en la intersección de
las clausuras.

En este nivel, podremos ver lo útil que puede llegar a ser el simplificador
de expresiones `simp`.
"

variable {X : Type} [espacio_topologico X] (A B: Set X)

/--
Si `A` y `B` son conjuntos, entonces `clausura (A ∩ B) ⊆ clausura A ∩ clausura B`.
-/
TheoremDoc clausura_interseccion as "clausura_interseccion" in "Clausura"

Statement clausura_interseccion : clausura (A ∩ B) ⊆ clausura A ∩ clausura B := by
  Hint (hidden := true) "Prueba a simplificar el objetivo con `simp`."
  simp only [subset_inter_iff]
  Hint (hidden := true) "Ahora separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes aplicar un resultado que afirma que,
    en esta situación, la clausura del subconjunto pequeño está contenida
    en la del grande."
    apply clausura_subconjunto
    Hint (hidden := true) "Esto lo puede demostrar el simplificador."
    simp only [inter_subset_left]
  · Hint (hidden := true) "Puedes aplicar un resultado que afirma que,
    en esta situación, la clausura del subconjunto pequeño está contenida
    en la del grande."
    apply clausura_subconjunto
    Hint (hidden := true) "Esto lo puede demostrar el simplificador."
    simp only [inter_subset_right]
