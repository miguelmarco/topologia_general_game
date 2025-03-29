import Game.Levels.Compacidad.CompactoBase

World "Compacidad"
Level 2
Title "Imagen continua de un compacto"

Introduction "Una propiedad importante de la compacidad
es que se respeta por funciones continuas
"

namespace topo
open espacio_topologico topo Set Set.Finite

variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y]

/--
Si `f : X → Y` es una aplicación continua, y `A` es un subconjunto
compacto de `X`, entonces `f '' A` es compacto.
-/
TheoremDoc topo.imagen_compacto as "imagen_compacto" in "Compacidad"

Statement imagen_compacto  (f : X → Y) (hf : continua f) (A : Set X) (hA : compacto A) :
    compacto (f '' A) := by
  Hint (hidden := true) "Puedes tomar un recubrimiento abierto
  de `{A}` con `intro`."
  intro F hFab hFA
  Hint (hidden := true) "Ahora necesitamos definir un recubrimiento
  abierto de `{A}`. En particular, el que será útil
  es el formado por las preimagenes de los abiertos de `{F}`.

  Teclea `let G := \{f ⁻¹' U | U ∈ {F}}`."
  let G := {f ⁻¹' U | U ∈ F}
  Hint (hidden := true) "Ahora necesitamos ver que `{G}`
  está formado por abiertos, y que recubre `{A}`.

  Primero, crea una nueva hipótesis que diga que
  los elementos de `{G}` son abiertos:

  teclea `have hGab : {G} ⊆ abiertos`."
  have hGab : G ⊆ abiertos
  · Hint (hidden := true) "Toma un elemento arbitrario
    de `{G}` con `intro`."
    intro U  hU
    Hint (hidden := true) "Como `{U}` está en `{G}`,
    `{hU}` nos asegura que es la preimagen de algún elemento de `{F}`.

    Elige un tal elemento con `choose`."
    choose V hV1 hVU using hU
    Hint (hidden := true) "Puedes reescribir el objetivo con `{hVU}`."
    rw [← hVU]
    Hint (hidden := true) "Ahora puedes aplicar que `{f}`
    es continua."
    apply hf
    Hint (hidden := true) "Puedes aplicar `{hFab}`."
    apply hFab
    exact hV1
  Hint (hidden := true) "Ahora necesitamos la hipótesis de que
  `{G}` recubre `{A}`. Para crearla (y pasar a demostrarla),
  teclea `have hGcub : recubrimiento {A} {G}`."
  have hGcub : recubrimiento A G
  · Hint (hidden := true) "Lo que queremos ver es que los
    puntos de `{A}` están en algún elemento de `{G}`.
    Así pues, toma un elemento de `{A}` arbitrario con `intro`."
    intro x hx
    Hint (hidden := true) "Para poder usar `{hFA}`, necesitamos ver
    que `{f} {x} ∈ {f} '' {A}`. Crea esta nueva hipótesis con `intro`,
    y pasemos a demostrarla."
    have hfx : f x ∈ f '' A
    · Hint (hidden := true) "Observa que para ver que está en `{f} '' {A}`,
      hay que dar un elemento de `{A}` tal que su imagen sea igual a `{f} '' {A}`.
      Hay una elección evidente para usar."
      use x
    Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hFA}` a `{hfx}`."
    have haux := hFA hfx
    Hint (hidden := true) "Gracias a `{haux}`, puedes elegir un elemento de
    `{F}` que contiene a `{f} {x}`."
    choose V hVF hxV using haux
    Hint (hidden := true) "Ahora ya podemos dar un elemento de `{G}` que contiene
    a `{x}`. ¿Cual puedes usar?"
    use (f ⁻¹' V)
    Hint (hidden := true) "Separa este objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Para ver que un conjunto está en `{G}`, hay que dar
      un elemento de `{F}` cuya imagen coincida con él. ¿Cual puedes usar?."
      use V
    · Hint (hidden := true) "Observa que el objetivo dice exactamente lo mismo que `{hxV}`."
      exact hxV
  Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hA}` a `{G}`, `{hGab}` y `{hGcub}`."
  have haux := hA G hGab hGcub
  Hint (hidden := true) "Puedes tomar un subrecubrimiento finito de `{G}`,
  junto con sus propiedades (con `choose`) gracias a `{haux}`."
  choose S hSF hSr1 hSr2 using haux
  Hint "Ahora tenemos que elegir un elemento de `{F}` por
  cada elemento de `{S}`. Para ello, primero necesitamos demostrar que existen,
  y después podremos tomar una función que los elija.

  Crea un nuevo objetivo que asegure que existen con
  `have hg : ∀ U ∈ S, ∃ V ∈ {F}, {f} ⁻¹' V = U`..
  "
  have hg : ∀ U ∈ S, ∃ V ∈ F,  f ⁻¹' V = U
  · Hint (hidden := true) "Toma un elemento arbitrario de `{S}` con
    `intro`."
    intro U hU
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hSF}` a `{hU}`."
    have hgU := hSF hU
    Hint (hidden := true) "Gracias a `{hgU}`, puedes elegir un elemento de
    `{F}` cuya preimagen es `{U}` (con `choose`.)"
    choose V hVF using hgU
    Hint (hidden := true) "¿Qué elemento de `{F}` puedes usar?"
    use V
  Hint "Ahora que tenemos `{hg}`, podemos definir una función que elija
  un elemento de `{F}` por cada uno de `{S}`.
  Para esto, usamos la táctica `choose!`.

  Teclea `choose! g hg1 hg2 using {hg}`."
  choose! g hg1 hg2 using hg
  Hint (hidden := true) "Ahora ya podemos dar nuestro subrecubrimiento finito
  de `{F}`. Estará formado por las imágenes de los elementos de `{S}` por `{g}`.

  Es decir, que puedes usar `{g} '' {S}`."
  use g '' S
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Toma un elemento de `{g} '' {S}` con `intro`."
    intro V hV
    Hint (hidden := true) "Gracias a `{hV}` puedes elegir un elemento de `{S}`
    cuya imagen es `{V}` (con `choose`)."
    choose U hUS hUV using hV
    rw [← hUV]
    Hint (hidden := true) "Puedes aplicar `{hg1}`."
    apply hg1
    exact hUS
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes aplicar el teorema `Finite.image`, que dice
    que la imagen de un conjunto finito es finita."
    apply Finite.image
    exact hSr1
  · Hint (hidden := true) "Toma un elemento arbitrario de `{f} '' {A}` con
    `intro`."
    intro y hy
    Hint (hidden := true) "Gracias a `{hy}`, puedes elegir un elemento de
    `{A}` cuya imagen es `{y}`."
    choose x hxA hxy using hy
    Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando
    `{hSr2} a {hxA}`."
    have hxS := hSr2 hxA
    Hint (hidden := true) "Gracias a `{hxS}, puedes elegir un elemento de `{S}` que contiene a `{x}`
    gracias a `{hxS}`."
    choose U hUS hxU using hxS
    Hint (hidden := true) "¿Qué elemento de `{g} '' {S}` puedes usar para que contenga
    a `{y}`?"
    use (g U)
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "¿Qué elemento de `{S}` puedes usar?"
      use U
    · Hint (hidden := true) "Puedes usar `{hxy}` para reescribir el objetivo."
      rw [← hxy]
      Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando
      `{hg2}` a `{U}` y `{hUS}`."
      have hg3 := hg2 U hUS
      Hint (hidden := true) "Puedes usar `{hg3}` para reescribir el objetivo."
      rw [← hg3] at hxU
      Hint (hidden := true) "Observa que el objetivo dice exactamente lo mismo
      que `{hxU}`."
      exact hxU

end topo
