import Game.Levels.Interior.InteriorIdempotente


World "Interior"
Level 9
Title "Interior de una intersección."

Introduction "Veamos qué ocurre con el interior de una intersección.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

/--
Dados un conjuntos `A` y `B` en un espacio topológico,
`interior_interseccion A B` dice que `interior (A ∩ B) = (interior A) ∩ (interior B)`.
-/
TheoremDoc topo.interior_interseccion as "interior_interseccion" in "Interior"


Statement interior_interseccion (A B: Set X) : interior (A ∩ B) = interior A ∩ interior B:= by
  Hint (hidden := true) "La forma habitual de demostrar la igualdad entre dos conjuntos es
  por extensionalidad: tomar un elemento arbitrario (con `ext`) y demostrar que pertenece
  a un conjunto si y solo si pertenece al segundo."
  ext x
  Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
  fconstructor
  · intro hx
    Hint (hidden := true) "Puedes separar el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar el hecho de que el operador interior es monótono
      (pero tendrás que especificar qué conjunto contenido en `{A}` quieres usar."
      apply interior_monotono (A ∩ B) A
      Hint (hidden := true) "Puedes tomar un elemento arbitario con `intro`."
      intro y hy
      Hint (hidden := true) "Puedes obtener dos hipótesis a partir de `{hy}` con `choose`
      o `cases'`."
      choose hya hyb using hy
      exact hya
      exact hx
    · Hint (hidden := true) "Puedes aplicar el hecho de que el operador interior es monótono
      (pero tendrás que especificar qué conjunto contenido en `{B}` quieres usar."
      apply interior_monotono (A ∩ B)
      Hint (hidden := true) "Puedes tomar un elemento arbitario con `intro`."
      intro y hy
      Hint (hidden := true) "Puedes obtener dos hipótesis a partir de `{hy}` con `choose`
      o `cases'`."
      choose hya hyb using hy
      exact hyb
      exact hx
  · Hint (hidden := true) "Recuerda que hay un teorema que te asegura que, un abierto
    contenido en `{A} ∩ {B}`, está contenido en su interior. Puedes aplicarlo."
    apply interior_contiene_abierto
    · Hint (hidden := true) "Puedes aplicar que la intersección de abiertos es abierto."
      apply interseccion_abiertos
      · Hint (hidden := true) "Sabemos que el interior de algo siempre es abierto."
        apply interior_abierto
      · Hint (hidden := true) "Sabemos que el interior de algo siempre es abierto."
        apply interior_abierto
    Hint (hidden := true) "Aquí tendrás que tomar un elemento arbitrario con `intro`."
    intro x hx
    choose hxa hxb using hx
    fconstructor
    · apply interior_contenido
      exact hxa
    · apply interior_contenido
      exact hxb








end topo
