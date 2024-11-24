import Game.Levels.Interior.ComplementarioInterior

World "Interior"
Level 11
Title "Interior del complementario."

Introduction "Veamos ahora otra relación simétrica a la anterior.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A` en un espacio topológico,
`complementario_clausura A ` dice que `(clausura A)ᶜ = interior Aᶜ`.
-/
TheoremDoc topo.complementario_clausura as "complementario_clausura" in "Clausura"


Statement complementario_clausura (A : Set X) : (clausura A)ᶜ = interior Aᶜ:= by
  Hint (hidden := true) "Para demostrar esto, puede ser útil usar el
  resultado anterior (aplicado a `{A}ᶜ`). Obtenlo con `have`."
  Hint (hidden := true) "`have h2 := complementario_interior {A}ᶜ`."
  have h2 := complementario_interior Aᶜ
  Hint (hidden := true) "Puedes simplificar la expresión de `{h2}`."
  simp only [compl_involutive, Function.Involutive.comp_self, cancela_inver] at h2
  Hint (hidden := true) "Ahora puedes reescribir el objetivo gracias a `{h2}`
  (de derecha a izquierda)."
  rw [← h2]
  Hint (hidden := true) "Solo hace falta simplificar la expresión del objetivo."
  simp only [compl_involutive, Function.Involutive.comp_self, cancela_inver]




end topo
