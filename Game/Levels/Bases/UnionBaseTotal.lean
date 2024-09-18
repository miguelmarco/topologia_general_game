import Game.Levels.Bases.CaracterizacionBases

open espacio_topologico Set


World "Bases"
Level 2
Title "Una base llena el espacio."

Introduction "Vamos ahora con un resultado fácil: la unión de una base es el
total.
"

variable {X : Type} [espacio_topologico X]


/--
La unión de una base es el total.
-/
TheoremDoc union_base_total as "union_base_total" in "Espacios Topologicos"

/--
La unión de una base es el total.
-/
Statement union_base_total (B : Set (Set X)) (hB : base B) : ⋃₀ B = univ := by
  Hint (hidden := true) "Recuerda que la forma habitual de demostrar la igualdad
  entre conjuntos es usando el principio de extensionalidad."
  ext x
  Hint (hidden := true) "Separa el objetivo en las dos afirmaciones que lo construyen."
  fconstructor
  · Hint (hidden := true) "Habrá que introducir el antecedente."
    intro hx
    Hint (hidden := true) "El objetivo es trivial."
    trivial
  · Hint (hidden := true) "De nuevo, habrá que introducir el antecedente."
    intro hx
    Hint (hidden := true) "Puede ser útil reescribir la caracterización de base"
    Branch
      rw [caracterizacion_base] at hB
      Hint (hidden := true) "Puedes separar `{hB}` en sus componentes usando `choose`."
      choose h1 h2 using hB
      Hint (hidden := true) "Para poder usar `{h2}` necesitarás la hipótesis de que el
      total es abierto. Añadela como un nuevo objetivo usando `have`."
      have h3 : (univ : Set X) ∈ abiertos
      · apply abierto_total
      Hint  "Ahora puedes conseguir una nueva hipótesis aplicando `{h2}`
      al caso del conjunto total (gracias a `{h3}`) y a `{x}` (gracias a `{hx}`)."
      Hint (hidden := true) "Utiliza `have h4 := {h2} univ {h3} {x} {hx}`."
      have h4 := h2 univ h3 x hx
      Hint (hidden := true) "Ahora puedes elegir un elemento que `{h4}` te garantiza que existe,
      junto con sus propiedades, usando `choose`."
      choose V hV1 hV2 hV3 using h4
      Hint (hidden := true) "Piensa qué elemento de `{B}` puedes usar."
      use V
    choose h1 h2 using hB
    Hint (hidden := true) "Para poder usar `{h2}` necesitarás la hipótesis de que el
    total es abierto. Añadela como un nuevo objetivo usando `have`."
    have h3 : (univ : Set X) ∈ abiertos
    · apply abierto_total
    Hint  "Ahora puedes conseguir una nueva hipótesis aplicando `{h2}`
    al caso del conjunto total (gracias a `{h3}`) y a `{x}` (gracias a `{hx}`)."
    Hint (hidden := true) "Utiliza `have h4 := {h2} univ {h3}`."
    have h4 := h2 univ h3
    Hint "Puedes elegir una familia, cuya existencia está garantizada por `{h4}`, junto
    con sus propiedades usando `choose`."
    choose F hFB hFu using h4
    Hint (hidden := true) "Fíjate en que puedes usar `{hFu}` para reescribir otra hipótesis."
    rw [hFu] at hx
    Hint (hidden := true) "Como `{x}` está en la unión de `{F}`, puedes elegir
    un elemento de `{F}` que lo contenga."
    choose V hV1 hV2 using hx
    Hint (hidden := true) "¿Qué elemento de `{B}` puedes usar para ver que `{x}` está en él?"
    use V
    fconstructor
    · apply hFB
      exact hV1
    · exact hV2
