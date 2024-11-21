import Game.Levels.Clausura.Denso

World "Interior"
Level 1
Title "Interior"

Introduction "El interior de un conjunto es la unión de los abiertos contenidos en él.

Veamos qué cumplen los puntos del interior.
"


namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]


def interior (A : Set X) := ⋃₀ { U ∈ abiertos | U ⊆ A}

/--
Si $A$ es un subconjunto de un espacio topológico, el **interior**
de $A$ ,es la unión de los abiertos contenidos en $A$.

Se denota en Lean como `interior' A`.
-/
DefinitionDoc interior as "interior"

TheoremTab "Interior"


/--
Si `A` es un conjunto en un espacio topológico, `def_interior A` dice
que `interior A = ⋃₀ { U ∈ abiertos | U ⊆ A}`.
-/
TheoremDoc topo.def_interior as "def_interior" in "lemas-definición"

theorem def_interior (A : Set X) : interior A = ⋃₀ { U ∈ abiertos | U ⊆ A} := by
  rfl

NewDefinition interior


NewTheorem topo.def_interior


/--
Un punto `x` está en el interior de `A` si y sólo si existe un abierto
`U` tal que `x ∈ U` y  `U ⊆ A`.
-/
TheoremDoc topo.caracterizacion_interior as "caracterizacion_interior" in "Interior"

Statement caracterizacion_interior (A : Set X) (x : X) : x ∈ interior A ↔ ∃ U ∈ abiertos, x ∈ U ∧ U ⊆ A := by
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reescribir la definición de interior
    en `{h}`."
    rw [def_interior] at h
    Hint (hidden := true) "`{h}`te asegura que `{x}` está en algún
    elemento de la familia, puedes elegirlo con `choose`."
    choose U hU hxU using h
    Hint (hidden := true) "`{hU}` te asegura dos afirmaciones, puedes obtenerlas
    con `choose` o `cases'`."
    choose hUab hUA  using hU
    Hint (hidden := true) "¿Cual es el abierto que puedes usar?"
    use U
  · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
    intro h
    Hint (hidden := true) "`{h}` te asegura que existen ciertos abiertos,
    puedes elegir uno con `choose`."
    choose U hUab hxU hUA using h
    Hint (hidden := true) "Puede ser útil reescribir la definición
    de interior."
    Hint (hidden := true) "¿Cual es el abierto que puedes usar?."
    use U
    Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
      fconstructor
      · exact hUab
      · exact hUA
    · exact hxU

end topo
