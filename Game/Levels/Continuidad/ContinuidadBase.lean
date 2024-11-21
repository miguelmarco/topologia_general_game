import Game.Levels.Continuidad.ContinuaEn

World "Continuidad"
Level 4
Title "Continuidad en términos de bases."

Introduction "Veamos ahora que, si tenemos una base de abiertos
en el espacio de llegada, basta ver que se cumple la definición de
continuidad para los abiertos básicos.
"
namespace topo
open topo espacio_topologico Set
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

/--
Si `f : X → Y` es una aplicación entre espacios topológicos, y `B` es una
base de abiertos de `Y`, `caracterizacion_continua_base` dice que
`continua f ↔ ∀ U ∈ B, f ⁻¹' U ∈ abiertos`.
-/
TheoremDoc topo.caracterizacion_continua_base as "caracterizacion_continua_base" in "Continuidad"

Statement caracterizacion_continua_base (B : Set (Set Y)) (hB : base B) :
    continua f ↔ ∀ U  ∈ B, f ⁻¹' U ∈ abiertos := by
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes tomar un elemento arbitrario de `B`
    con `intro`."
    intro U hU
    Hint (hidden := true) "Puede ser un buen momento para reescribir la
    definición de continuidad."
    rw [def_continua] at h
    Hint (hidden := true) "Observa que `{h}` implica el objetivo,
    así que puedes aplicarla."
    apply h
    Hint (hidden := true) "Ahora necesitas usar que `{B}` es una base,
    tendrás que reescribir la definición de base."
    rw [def_base] at hB
    Hint (hidden := true) "Puedes obtener dos hipótesis a partir
    de `{hB}`usando `choose` o `cases'`."
    choose hB1 hB2 using hB
    Hint (hidden := true) "Observa que puedes aplicar `{hB1}`."
    apply hB1
    Hint (hidden := true) "Y ahora el objetivo es exactamente una de las hipótesis."
    exact hU
  · Hint (hidden := true) "Introduce el antecedente como hipótesis, con `intro`."
    intro h
    Hint (hidden := true) "Puede ser un buen momento para reescribir la definición
    de continuidad."
    rw [def_continua]
    Hint (hidden := true) "Puedes tomar un abierto arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Aquí puede ser más fácil usar la caracterización
    de las bases. Prueba a reescribirla."
    rw [caracterizacion_base] at hB
    Hint (hidden := true) "Puedes obtener dos hipótesis de `{hB}` con `choose`
    o `cases'`."
    choose hB1 hB2 using hB
    Hint (hidden := true) "Ahora, como tenemos las propiedades de la base
    expresadas en términos de puntos, puede ser útil reescribir
    el objetivo en términos de puntos también."
    Hint (hidden := true) "Recuerda que un conjunto es abierto si y sólo
    si es entorno de todos sus puntos."
    rw  [abierto_sii_entorno]
    Hint (hidden := true) "Ahora puedes tomar un punto arbitrario con `intro`."
    intro x hx
    Hint (hidden := true) "Puedes obtener una nueva hipótesis si particularizas
    `{hB2}` para `{U}`, `{hU}`, `({f} {x})` y `{hx}`. Usa `have` para ello."
    have h2 := hB2 U hU (f x) hx
    Hint (hidden := true) "Como `{h2}` te asegura que existen ciertos
    elementos de `{B}`, puedes elegir uno (y sus propiedades) con `choose`."
    choose V hVB hfxV hVU using h2
    Hint (hidden := true) "Igual puede ser buen momento para reescribir
    la definición de entorno."
    rw [def_entorno]
    Hint (hidden := true) "¿Qué abierto puedes usar para demostrar que
    existe uno como pide el objetivo?

    Fíjate que buscas un abierto en `{X}`, pero `{U}` y `{V}` están
    en `{Y}`. ¿Qué hipótesis te asegura algo sobre abiertos en `{X}`."
    Hint (hidden := true) "`use (f ⁻¹' V)`"
    use (f ⁻¹' V)
    Hint (hidden := true) "Separa el objetvo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Se puede aplicar una hipótesis que garantiza
      justo lo que buscas."
      apply h
      Hint (hidden := true) "Este objetivo es exactamente igual a una hipótesis."
      exact hVB
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Este objetivo es exactamente igual a una hipótesis."
      exact hfxV
    · Hint (hidden := true) "Para ver que un conjunto está contenido en otro, toma
      un elememento arbitrario."
      intro z
      Hint (hidden := true) "Puede ser útil simplificar la expresión del objetivo."
      simp only [mem_preimage]
      Hint (hidden := true) "Ahora puedes aplicar una de las hipótesis."
      apply hVU

end topo
