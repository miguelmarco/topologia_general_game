import Game.Levels.Interior.InteriorMonotono


World "Interior"
Level 7
Title "Un conjunto es abierto si y solo si es igual a su interior."

Introduction "Veamos una caracterizacion de los abiertos en términos de interiores:
un conjunto es abierto si y solo si es igual a su interior.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A` en un espacio topológico,
`abierto_sii_interior A` dice que `A ∈ abiertos ↔ A = interior A`.
-/
TheoremDoc topo.abierto_sii_interior as "abierto_sii_interior" in "Interior"


Statement abierto_sii_interior (A : Set X) : A ∈ abiertos ↔ interior A = A:= by
  Hint (hidden := true) "Puedes separar el objetivo en dos usando `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
    intro h
    Hint (hidden := true) "La forma habitual de demostrar que dos conjuntos son iguales
    es por extensionalidad: tomar un elemento arbitrario (con `ext`) y ver que está en un conjunto
    si y solo si está en el otro."
    ext x
    Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
      intro hx
      Hint ( hidden := true ) "Puedes aplicar el teorema que vimos que afirma que
      el interior de un conjunto está contenido en el conjunto."
      apply interior_contenido
      exact hx
    · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
      intro hx
      Hint (hidden := true) "Puede ser útil reescribir el objetivo con la caracterización
      de que un punto esté en el interior."
      rw [caracterizacion_interior]
      Hint (hidden := true) "¿Qué conjunto abierto puedes usar?"
      use A
  · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Gracias a `{h}`, puedes reescribir el objetivo (aplicando `{h}`
    de derecha a izquierda)."
    rw [← h]
    Hint (hidden := true) "Puedes aplicar el teorema que dice que el interior de
    cualquier conjunto."
    apply interior_abierto


end topo
