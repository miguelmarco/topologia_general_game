import Game.Levels.ExteriorFronteraAislado.ClausuraUnionInteriorFrontera
World "ExteriorFronteraAislado"
Level 11
Title "Puntos aislados y derivado."

Introduction "Los puntos aislados de un conjunto `A` son
aquellos `x` para los que hay un abierto `U` tal que `U ∩ A = {x}`.


El derivado de un conjunto `A` son los puntos `x` tales que para todo
abierto `U` conteniendo a `x` , `( U \\ {x}) ∩ A ≠ ∅`."

@[simp]
theorem no_vacio (X : Type) (A : Set X) : A ≠ ∅ ↔ ∃ y, y ∈ A := by
  rw [ne_eq]
  push_neg
  rfl

@[simp]
theorem unipuntual_sii (X : Type) (A : Set X) (x : X) : A = {x} ↔ x ∈ A ∧ ∀ y ∈ A, y = x := by
  exact Set.eq_singleton_iff_unique_mem

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)

def aislados := {x : X | ∃ U ∈ abiertos, U ∩ A = {x}}

/--
Los puntos aislados de un conjunto `A` son
aquellos `x` para los que hay un abierto `U` tal que `U ∩ A = {x}`.
-/
DefinitionDoc aislados as "aislados"

theorem def_aislados : aislados A = {x : X | ∃ U ∈ abiertos, U ∩ A = {x}} := rfl


/--
`def_aislados A` dice que `aislados A = {x : X | ∃ U ∈ abiertos, U ∩ A = {x}}`
-/
TheoremDoc topo.def_aislados as "def_aislados" in "Exterior/Frontera/Aislado"



NewTheorem topo.def_aislados

/--
Dado un conjunto `A` y un punto `x`
`no_aislado A x` dice que `x` no es un punto aislado de `A` si y solo si
`x ∉ A ∨  ∀ U ∈ abiertos, x ∈ U → ∃ y ≠ x, y ∈ U ∩ A` .
-/
TheoremDoc topo.no_aislado_sii as "no_aislado_sii" in "Exterior/Frontera/Aislado"

Statement no_aislado_sii (x : X)  : x ∉ aislados A ↔ x ∉ A ∨  ∀ U ∈ abiertos, x ∈ U → ∃ y ≠ x, y ∈ U ∩ A := by
  Hint (hidden := true) "Puedes separar el objetivo en dos usando `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes reescribir la definición de punto aislado en `{h}`."
    rw [def_aislados] at h
    Hint (hidden := true) "Puede ser útil simplificar la expresión en `{h}`."
    simp at h
    Hint (hidden := true) "Ahora tendremos que considerar dos casos: si `{x} ∈ {A}` o no.
    Distinguelos con `by_cases`."
    by_cases hcas : x ∈ A
    · Hint (hidden := true) "En este caso, claramente vamos a demostrar la opción de la derecha."
      right
      Hint (hidden := true) "Toma un abierto arbitrario, y sus propiedades, con `intro`."
      intro U hUab hxU
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) aplicando `{h}` a
      `{U}`, `{hUab}`, `{hxU} y `{hcas}`."
      have h2 := h U hUab hxU hcas
      Hint (hidden := true) "Como `{h2}` te asegura que existen ciertos elementos de `{A}`
      que cumplen más condiciones, puedes elegir uno con `choose`."
      choose y hyA hyU hyx using h2
      Hint (hidden := true) "¿Qué elemento puedes usar?"
      use y
      Hint (hidden := true) "Tendrás que separar el objetivo en varios con `fconstructor`."
      fconstructor
      · exact hyx
      fconstructor
      · exact hyU
      · exact hyA
    · Hint (hidden := true) "En este caso, lo que tenemos fácil es demostrar el caso de la izquierda."
      left
      exact hcas
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Como `{h}` nos dice que ocurre una de dos posibilidades,
    tenemos que separar los casos con `cases'`."
    cases' h with h h
    · Hint (hidden := true) "Puede ser útil reescribir la definición de aislados."
      rw [def_aislados]
      Hint (hidden := true) "Una forma de demostrar que `{x}` no puede estar en ese
      conjunto, es suponer que sí lo está (con `intro`) y luego llegar a una contradicción."
      intro hn
      Hint (hidden := true) "Observa que `{hn}` nos dice que existen ciertos abiertos,
      elige uno con `choose`."
      choose U hUab hU using hn
      Hint (hidden := true) "Prueba a simplificar `{hU}`."
      simp at hU
      Hint (hidden := true) "Puedes separar `{hU}` en dos afirmaciones con `choose` o `cases'`."
      choose hxU hU using hU
      Hint (hidden := true) "Ahora puedes separar `{hxU}` en dos afirmaciones."
      choose hxU hxA using hxU
      Hint (hidden := true) "La contradicción te la da `{h}`, así que puedes aplicarla."
      apply h
      exact hxA
    · Hint (hidden := true) "Puede ser útil reescribir la definición de aislado."
      rw [def_aislados]
      Hint (hidden := true) "Prueba a simplificar el objetivo"
      simp
      Hint (hidden := true) "Puedes tomar un abierto con esas condiciones con `intro`."
      intro U hUab hxU hxA
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) aplicando
      `{h}` a `{U}`, `{hUab}` y `{hxU}`."
      have h2 := h U hUab hxU
      Hint (hidden := true) "Ahora, gracias a `{h2}`, puedes elegir un elemento de
      `{U} ∩ {A}` distinto de `{x} (con `choose`)."
      choose y hyx  hyU hyA using h2
      Hint (hidden := true) "¿Qué elemento de `{A}` puedes usar?"
      use y


end topo
