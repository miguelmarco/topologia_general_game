import Game.Levels.Productos.ClausuraProducto
World "Productos"
Level 4
Title "Interior de un poducto"

Introduction "
Veamos una relación entre los interiores y los productos.
"

namespace topo
open topo espacio_topologico Set


variable (X Y : Type) [espacio_topologico X] [espacio_topologico Y]



/--
Dado un producto de espacios topológicos `X × Y`, y dos subconjuntos `A` y `B` de
`X` e `Y` respectivamente, `interior_producto A B` dice que `interior A ×ˢ B = interior A ×ˢ interior B`.
-/
TheoremDoc topo.interior_producto as "interior_producto" in "Productos"



Statement interior_producto (A : Set X) (B : Set Y) : interior (A ×ˢ B ) = interior A ×ˢ interior B := by
  Hint (hidden := true) "Veamos que dos conjuntos son iguales por extensionalidad:
  toma un elemento arbitrario con `ext` y demuestra que está en uno si y solo si está en el otro."
  ext z
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro hz
    Hint (hidden := true) "Será útil reescribir la caracterización de
    los puntos interiores en términos de entornos en `{hz}`."
    rw [caracterizacion_interior_entorno] at hz
    Hint (hidden := true) "Ahora podemos usar la caracterización de los entornos
    en un producto para reescribir en `{hz}`."
    rw [caracterizacion_entorno_producto] at hz
    Hint (hidden := true) "Ahora podemos usar `{hz}` para elegir dos
    abiertos de `{X}` e `{Y}`, y sus respectivas propiedades."
    choose U V hU hV hzU hzV hUVN using hz
    Hint (hidden := true) "Observa que, en realidad,
    el objetivo son dos afirmaciones, una sobre cada componente de `{z}`.
    Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Para que esté en el interior de `{A}` tiene que
      haber un entorno intermedio. ¿Cual puedes usar?"
      use U
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Ver `{U}` está en ese conjunto es ver que cumple
        las dos condiciones. Separa el objetivo en dos con `fconstructor`."
        fconstructor
        · exact hU
        · Hint (hidden := true) "Para ver el contenido, toma un elemento arbitrario
          con `intro`."
          intro x hx
          Hint (hidden := true) "Ahora vamos a necesitar ver algo un poco más fuerte
          que el objetivo. Introduce un nuevo objetivo con `have haux : ({x}, {z}.2) ∈ {A} ×ˢ {B}`."
          have haux : (x,z.2) ∈ A ×ˢ B
          · Hint (hidden := true) "Puedes aplicar `{hUVN}`."
            apply hUVN
            Hint (hidden := true) "Esta parte que queda es trivial."
            trivial
          Hint (hidden := true) "Ahora puedes separar `{haux}` en dos
          hipótesis  (con `choose` o `cases'`.) y usar una de ellas para demostrar el objetivo."
          exact haux.1
      exact hzU
    Hint (hidden := true) "Para ver que está en el interior necesitas un abierto intermedio.
    ¿Cual puedes usar?."
    use V
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Separa el objetivo en dos con `fconstructor."
      fconstructor
      · exact hV
      · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
        intro y hy
        Hint (hidden := true) "Ahora necesitamos de nuevo un enunciado un poco
        más fuerte que el objetivo. Crea un nuevo objetivo con
        `have haux : ({z}.1, {y}) ∈ {A} ×ˢ {B}`."
        have haux : (z.1, y) ∈ A ×ˢ B
        · Hint (hidden := true) "Se puede aplicar `{hUVN}`."
          apply hUVN
          Hint (hidden := true) "Esta parte que queda es trivial."
          trivial
        Hint (hidden := true) "Ahora separa `{haux}` en dos hipótesis con
        `choose` o `cases'`."
        exact haux.2
    exact hzV
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro hz
    Hint (hidden := true) "Puedes separar `{hz}` en dos hipótesis con
    `choose` o `cases'`."
    choose hzA hzB using hz
    Hint (hidden := true) "Puede ser útil reescribir la caracterización
    de los puntos del interior de un conjunto (donde tenga sentido hacerlo)."
    rw [caracterizacion_interior] at hzA hzB ⊢
    Hint (hidden := true) "Ahora puedes elegir un abierto y sus propiedades
    (con `choose`) gracias a `{hzA}`."
    choose U hU hzU hUA using hzA
    Hint (hidden := true) "Puedes elegir un abierto y sus propiedades (con `choose`)
    gracias a `{hzB}`."
    choose V hV hzV hVB using hzB
    Hint (hidden := true) "Ahora, ¿qué abierto puedes usar?."
    use U ×ˢ V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Será útil reescribir la definición de abierto en un producto."
      rw [def_abierto_producto]
      Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
      intro z hz
      Hint (hidden := true) "¿Qué abierto de `{X}` puedes usar?"
      use U
      Hint (hidden := true) "¿Qué abierto de `{Y}` puedes usar?"
      use V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Fíjate que el objetivo son dos afirmaciones,
      una sobre cada componente de `{z}`. Puedes separarlas con `fconstructor`."
      trivial
    · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
      intro a ha
      Hint (hidden := true) "Puedes separar `{ha}` en dos afirmaciones
      con `choose` o `cases'`."
      choose haU haV using ha
      Hint (hidden := true) "Observa que el objetivo son en realidad dos afirmaciones,
      una por cada componente de `{a}`. Puedes separarlas con `fconstructor`. "
      fconstructor
      · apply hUA
        exact haU
      · exact hVB haV



end topo
