import Game.Levels.Bases.InterseccionElementosBase

open espacio_topologico Set


World "Bases"
Level 4
Title "Cuándo una familia de abiertos es una base."

Introduction "Ahora vamos a ver un criterio para determinar que una familia de abiertos es una base.
"

variable {X : Type} [espacio_topologico X] (B : Set (Set X)) (hB : base B)

/--
Dada una base $𝓑$, y una familia de abiertos $𝓑'$, $𝓑'$ es base si y sólo sí
$∀ B ∈  𝓑, ∀ x ∈ B, ∃ B' ∈ 𝓑', x ∈ B' ⊆ B$.
-/
TheoremDoc criterio_familia_abiertos_base as "criterio_familia_abiertos_base" in "Espacios Topológicos."

Statement criterio_familia_abiertos_base (B' : Set (Set X)) (hB' : B' ⊆ abiertos) :
    base B' ↔ ∀ U ∈ B, ∀ x ∈ U, ∃ U' ∈ B', x ∈ U' ∧ U' ⊆ U := by
  Hint (hidden := true) "Separa la doble implicación con dos implicaciones con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Tendrás que introducir el antecedente de la implicación
    como hipótesis."
    intro h
    Hint (hidden := true) "Será útil reformular el hecho de que `{B}` y `{B'}` son bases, usando `caracterizacion_base`."
    rw [caracterizacion_base] at h hB
    Hint (hidden := true) "Ahora `{h}` y `{hB}` están compuestos de dos afirmaciones, te recomiendo separarlas
    (puedes usar la táctica `choose`)"
    choose h1 h2 using h
    choose hB1 hB2 using hB
    Hint (hidden := true) "Puesto que rienes que demostrar algo para todo elemento de `{B}`, la forma
    natural es tomar uno (y la hipótesis de que es ), usando `intro`."
    intro U hU
    Hint (hidden := true) "Fíjate en que se puede aplicar `{h2}` para demostrar el objetivo."
    apply h2
    Hint (hidden := true) "Hay dos hipótesis que te permiten concluir que algo es un abierto. Piensa
    en cual puedes aplicar a `{U}`."
    apply hB1
    exact hU
  · Hint (hidden := true) "Tendrás que introducir el antecedente de la implicación
    como hipótesis."
    intro h
    Hint (hidden := true) "Será útil reformular el hecho de que  `{B'}` es base, usando `caracterizacion_base`."
    rw [caracterizacion_base]
    Hint (hidden := true) "Como el objetivo está formado por dos afirmaciones, puedes separarlo
    con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Tienes una hipótesis que asegura exactamente el objetivo."
      exact hB'
    · Hint (hidden := true) "Como tienes que demostrar algo para todo abierto y todo punto de él,
      puedes tomar unos arbitrarios con `intro`."
      intro U hU x hx
      Hint (hidden := true) "Puede ser útil reescribir `{hB}` usando la caracterización de las bases."
      rw [caracterizacion_base] at hB
      Hint (hidden := true) "Como `{hB}`  está formado por dos afirmaciones, puedes tomarlas por
      separado con `cases'` o `choose`."
      choose hB1 hB2 using hB
      Hint (hidden := true) "Observa que como `{U}` es un abierto (por `{hU}`) y `{x}` está en `{U}`
      (por `{hx}`), puedes aplicarles
      `{hB2}` para obtener una nueva hipótesis específica sobre `{U}`."
      Hint (hidden := true) "Usa `have h3 := {hB2} {U} {hU} {x} {hx}`. "
      have h3 := hB2 U hU x hx
      Hint (hidden := true) "Ahora puedes elegir uno de los `V` que `{h3}` te asegura que existen,
      y sus correspondientes hipótesis."
      choose V hVB hxV hVU using h3
      Hint (hidden := true) "Ahora podemos obtener una nueva hipótesis con `{h}` aplicada
      al caso particular de `{V}`, `{hVB}`, `{x}` y `{hx}`."
      have h4 := h V hVB x hxV
      Hint (hidden := true) "Podemos tomar uno de los `U'` que `{h4}` nos asegura que existen."
      Hint (hidden := true) "Usa `choose U' hU'B' hxU' hU'V using {h4}`"
      choose U' hU'B' hxU' hU'V using h4
      Hint (hidden := true) "¿Cual puede ser el elemento de `{B'}` que debemos usar?"
      use U'
      Hint (hidden := true) "Recuerda que la táctica para separar un objetivo formado por varias
      hipótesis es `fconstructor`."
      fconstructor
      · Hint (hidden := true) "El objetivo es exactamente una de tus hipótesis."
        exact hU'B'
      Hint (hidden := true) "Hay que volver a separar el objetivo en varias hipótesis."
      fconstructor
      · Hint (hidden := true) "El objetivo es exactamente una de tus hipótesis."
        exact hxU'
      · Hint (hidden := true) "Para demostrar un contenido entre conjuntos, lo habitual es
        tomar un elemento del primero y ver que está en el segundo."
        intro y hy
        Hint (hidden := true) "Puedes aplicar `{hVU}`."
        apply hVU
        Hint (hidden := true) "Puedes aplicar `{hU'V}`."
        apply hU'V
        Hint (hidden := true) "El objetivo es exactamente una hipótesis."
        exact hy
