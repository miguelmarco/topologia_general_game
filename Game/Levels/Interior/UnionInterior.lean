import Game.Levels.Interior.ComplementarioClausura

World "Interior"
Level 12
Title "Union de interiores."

Introduction "La unión de interiores está contenido en el interior
de la unión.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dados conjuntos `A` y `B` en un espacio topológico,
`union_interior A B ` dice que `interior A ∪ interior B ⊆ interior (A ∪ B)`.
-/
TheoremDoc topo.union_interior as "union_interior" in "Interior"


Statement union_interior (A B: Set X) : interior A ∪ interior B ⊆ interior (A ∪ B):= by
  Hint (hidden := true) "Toma un elemento arbitrario del primer conjunto
  con `intro`."
  intro x hx
  Hint (hidden := true) "`{hx}` nos dice que `{x}` está
  en `interior {A}` o en `interior {B}`. Separa la demostración
  en esos dos casos con `cases'`."
  cases' hx with hx hx
  · Hint (hidden := true) "Puede ser útil reescribir la caracterización
    de interior en el objetivo y en `{hx}`."
    rw [caracterizacion_interior] at hx ⊢
    Hint (hidden := true) "Gracias a `{hx}` sabemos que hay abiertos
    intermedios, puedes elegir uno con `choose`."
    choose U hUab hxU hUA using hx
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hUab
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hxU
    · Hint (hidden := true) "Para demostrar un contenido, toma un
      elemento arbitrario con `intro`."
      intro y hy
      Hint (hidden := true) "Ahora tienes que elegir cual de las dos
      opciones vas a demostrar: ¿la de la izquierda o la de la derecha?
      (`left` o `right`)"
      left
      apply hUA
      exact hy
  · Hint (hidden := true) "Puede ser útil reescribir la caracterización
    de interior en el objetivo y en `{hx}`."
    rw [caracterizacion_interior] at hx ⊢
    Hint (hidden := true) "Gracias a `{hx}` sabemos que hay abiertos
    intermedios, puedes elegir uno con `choose`."
    choose U hUab hxU hUA using hx
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hUab
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hxU
    · Hint (hidden := true) "Para demostrar un contenido, toma un
      elemento arbitrario con `intro`."
      intro y hy
      Hint (hidden := true) "Ahora tienes que elegir cual de las dos
      opciones vas a demostrar: ¿la de la izquierda o la de la derecha?
      (`left` o `right`)"
      right
      apply hUA
      exact hy



end topo
