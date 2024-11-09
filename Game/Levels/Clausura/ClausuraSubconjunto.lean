import Game.Levels.Clausura.ClausuraContiene
open espacio_topologico Set Function

World "Clausura"
Level 6
Title "La clausura es monótona."

Introduction "Otro resultado fácil: si $A ⊆ B$, $\\bar{A} ⊆ \\bar{B}$.

Para demostrar esto, símplemente tendrás que aplicar los resultados anteriores.
"

variable {X : Type} [espacio_topologico X] (A B : Set X)


/--
Si `A ⊆ B`, `clausura A ⊆ clausura B`
-/
TheoremDoc clausura_subconjunto as "clausura_subconjunto" in "Clausura"

Statement clausura_subconjunto (h : A ⊆ B): clausura A ⊆ clausura B := by
  Hint (hidden := true) "Recuerda que un resultado anterior te permite
  asegurar que la clausura de `A` está contenida en ciertos conjuntos."
  apply clausura_contenida_cerrado
  Hint (hidden := true) "Hay un resultado previo que te asegura
  que las clausuras son cerrados."
  apply clausura_cerrado
  Hint (hidden := true) "Ahora tendrás que tomar un elemento arbitrario."
  intro y hy
  Hint (hidden := true) "Puedes aplicar que la clausura de `B` contiene a `B`."
  apply clausura_contiene
  apply h
  exact hy
