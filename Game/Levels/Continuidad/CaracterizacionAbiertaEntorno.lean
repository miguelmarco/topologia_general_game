import Game.Levels.Continuidad.CaracterizacionHomeoContinuaCerrada

World "Continuidad"
Level 12
Title "Caracterización de funciones abiertas."

Introduction "Una aplicación es abierta si y solo si la imagen de cualquier entorno de un punto,
es entorno de su imagen.
"

namespace topo
open topo espacio_topologico Set Function
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

/--
Sea `f : X → Y` es una aplicación entre espacios topológicos. `f` es abierta si y solo si
`∀ x, ∀ N, entorno x N → entorno (f x) (f '' N)`.
-/
TheoremDoc topo.caracterizacion_abierta_entorno as "caracterizacion_abierta_entorno" in "Continuidad"

Statement caracterizacion_abierta_entorno : abierta f ↔ ∀ x, ∀ N, entorno x N → entorno (f x) (f '' N) := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente, y los elemenot arbitrarios que necesites, con `intro`."
    intro h x N hN
    Hint (hidden := true) "Como `{hN}` te dice que existe algún abierto intermedio entre `{x}`
    y `{N}`, puedes elegir uno (y sus propiedades) con `choose`."
    choose U hUab hxU hUN using hN
    Hint (hidden := true) "Ahora, para ver que `{f} '' {N}` es entorno de `{f} {x}`, hay que dar un
    abierto intermedio. ¿Cual puedes usar?."
    use f '' U
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Para ver que la imagen de un abierto es abierto, puedes aplicar la hipótesis
      de que `{f}` es abierta."
      apply h
      exact hUab
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Tienes que ver que `{f} {x}` es la imagen de algún elemento
      de `{U}`. ¿Cual puedes usar?"
      use x
    · Hint (hidden := true) "Toma un elemento arbitrario de `{f} '' {U}` con `intro`."
      intro y hy
      Hint (hidden := true) "Como `{hy}` te dice que `{y}` es la imagen de algún elemento
      de `{U}`, puedes elegir uno (y sus propiedades) con `choose`."
      choose z hzU hzy using hy
      Hint (hidden := true) "Tienes que ver que `{y}` es la imagen de algún elemento de `{N}`,
      ¿Cual puedes usar?"
      use z
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Observa que puedes aplicar `{hUN}`."
        apply hUN
        exact hzU
      · exact hzy
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Para ver que es abierta, debes tomar un abierto arbitrario (con `intro`)
    y demostrar que su imagen es abierta."
    intro U hU
    Hint (hidden := true) "Como `{h}` habla de entornos, te será útil reescribir que `{U}` y
    `{f} '' {U}` son abiertos en términos de entornos."
    rw [abierto_sii_entorno] at hU ⊢
    Hint (hidden := true) "Puedes tomar un elemento arbitrario de `{f} '' {U}` con `intro`."
    intro y hy
    Hint (hidden := true) "Como `{hy}` te asegura que existe alguna preimagen de `{y}` en `{U}`,
    puedes elegir una (y sus propiedades) con `choose`."
    choose x hxU hxy using hy
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) a partir de `{hU}`,
    `{x}` y `{hxU}`."
    have hUen := hU x hxU
    Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis aplicando `{h}` a `{x}`, `{U}`
    y `{hUen}`."
    have haux := h x U hUen
    Hint (hidden := true) "Prueba a reescribir `{haux}` con `{hxy}`."
    rw [hxy] at haux
    exact haux

end topo
