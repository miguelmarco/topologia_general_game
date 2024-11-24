import Game.Levels.Interior.InteriorInterseccion

World "Interior"
Level 10
Title "Complementario del Interior."

Introduction "Veamos qué relación hay entre el complementario de un interior,
y la clausura.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dado un conjunto `A` en un espacio topológico,
`complementario_interior A ` dice que `(interior A)ᶜ = clausura Aᶜ`.
-/
TheoremDoc topo.complementario_interior as "complementario_interior" in "Interior"


Statement complementario_interior (A : Set X) : (interior A)ᶜ = clausura Aᶜ:= by
  Hint (hidden := true) "La forma habitual de demostrar la igualdad entre dos conjuntos es
  por extensionalidad: tomar un elemento arbitrario (con `ext`) y demostrar que pertenece
  a un conjunto si y solo si pertenece al segundo."
  ext x
  Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
    intro hx
    Hint (hidden := true) "Puedes reescribir el objetivo con la caracterización
    de la clausura."
    rw [caracterizacion_clausura]
    Hint (hidden := true) "Prueba a tomar un abierto arbitrario con `intro`."
    intro U hUab hxU
    Hint (hidden := true) "Este caso se puede demostrar por contradicción. (con `by_contra`)."
    by_contra hn
    Hint (hidden := true) "La contradicción viene del hecho de suponer
    que `{x}` no está en el interior de `{A}`, así que puedes aplicar `{hx}`."
    apply hx
    Hint (hidden := true) "Puede ser útil reescribir la caracterizaucíón
    de interior."
    rw [caracterizacion_interior]
    Hint (hidden := true) "Tienes qye ver que exisre un abierto con ciertas
    propiedades. ¿Cual puedes usar?"
    use U
    Hint (hidden := true) "Puedes separar el objetivo con `fconstructor`."
    fconstructor
    · exact hUab
    Hint (hidden := true) "Puedes separar el objetivo con `fconstructor`."
    fconstructor
    · exact hxU
    · Hint (hidden := true) "Prueba a simplificar `{hn}`  (con `simp`)."
      simp only [mem_inter_iff, mem_compl_iff, not_exists, not_and, not_not] at hn
      Hint (hidden := true) "Observa que `{hn}` dice exactamente lo mismo que el objetivo."
      exact hn
  · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Esta demostración también se puede hacer por contradicción."
    by_contra hn
    Hint (hidden := true) "Prueba a simplificar `{hn}`."
    simp only [mem_compl_iff, not_not] at hn
    Hint (hidden := true) "Prueba a reescribir la caracterización de interior
    en `{hn}`."
    rw [caracterizacion_interior] at hn
    Hint (hidden := true) "Como `{hn}` te asegura que existen ciertos abiertos,
    puedes elegir uno con `choose`."
    choose U hUab hxU hUA using hn
    Hint (hidden := true) "Puedes probar a reescribir la caracterización
    de clausura en `{h}`."
    rw [caracterizacion_clausura] at h
    Hint (hidden := true) "Observa que puedes obtener una nueva hipótesis
    gracias a `{h}`, `{hUab}` y `{hxU}` (con `have`)."
    have h2 := h U hUab hxU
    Hint (hidden := true) "`{h2}` te asegura que existen elementos
    en `{U}` y `{A}ᶜ`. Puedes elegir uno con `choose`."
    choose y hyU hyUA using h2
    Hint (hidden := true) "La contradicción vendrá de que `{y}`
    está en `{A}ᶜ`. Así que puedes aplicar `{hyUA}`."
    apply hyUA
    apply hUA
    exact hyU



end topo
