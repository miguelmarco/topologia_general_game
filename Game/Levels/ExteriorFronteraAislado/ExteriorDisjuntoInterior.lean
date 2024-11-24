import Game.Levels.ExteriorFronteraAislado.ExteriorComplementarioClausura
World "ExteriorFronteraAislado"
Level 3
Title "El exterior es disjunto con el interior."

Introduction "Veamos que el exterior de un conjunto es disjunto con
el interior.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`  en un espacio topológico,
`exterior_disjunto_interior A` dice que `interior A ∩  exterior A = ∅`.
-/
TheoremDoc topo.exterior_disjunto_interior as "exterior_disjunto_interior" in "Exterior/Frontera/Aislado"


Statement exterior_disjunto_interior :interior A ∩ exterior A = ∅:= by
  Hint (hidden := true) "Reescribe la definición de exterior con `def_exterior`."
  rw [def_exterior]
  Hint (hidden := true) "Para ver la igualdad entre conjuntos, aplica
  el principio de extensionalidad: toma un elemento arbitrario (con `ext`)
  y pasa a probar que extá en un conjunto si y solo si está en el segundo."
  ext x
  Hint (hidden := true) "Puedes simplificar la expresión."
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  Hint (hidden := true) "Introduce los antecedentes con `intro`."
  intro h h2
  Hint (hidden := true) "Recuerda que un teorema te aseguraba que
  el interior de un conjunto está contenido en el conjunto. Puedes
  obtener nuevas hipótesis (con `have`) gracias a él."
  Hint (hidden := true) "`have haux1 : {x} ∈ {A}`"
  have h3 :x ∈ A
  · Hint (hidden := true) "Puedes aplicar el teorema que te dice
    que el interior de un conjunto está contenido en él-"
    apply interior_contenido
    exact h
  Hint (hidden := true) "`have haux2 : {x} ∈ {A}ᶜ`"
  have h4 : x ∈ Aᶜ
  · apply interior_contenido
    exact h2
  Hint (hidden := true) "Ahora la contradicción viene de `{h4}`, así
  que puedes aplicarlo."
  apply h4
  exact h3



end topo
