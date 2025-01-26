import Game.Levels.Productos.ProductoIAN
World "Productos"
Level 11
Title "Producto de bases de abiertos"

Introduction "
Si `BX` y `BY` son bases de abiertos de `X` e `Y`, `{ Bx ×ˢ By | (Bx ∈ BX) (By ∈ BY)}`
es base de abiertos de `X × Y`.
"



namespace topo
open topo espacio_topologico Set

variable {X Y : Type} [espacio_topologico X] [espacio_topologico Y]


/--
Si `BX` y `BY` son bases de abiertos de `X` e `Y`, `{ Bx ×ˢ By | (Bx ∈ BX) (By ∈ BY)}`
es base de abiertos de `X × Y`.
-/
TheoremDoc topo.producto_bases as "producto_bases" in "Productos"

Statement producto_bases
  {BX : Set (Set X)}
  {BY : Set (Set Y)}
  (hBX : base BX)
  (hBY : base BY)
  :
    base { Bx ×ˢ By | (Bx ∈ BX) (By ∈ BY)}  := by
  Hint (hidden := true) "Será útil reescribir las hipótesis y el objetivo usando
  la caracterización de las bases."
  rw [caracterizacion_base] at hBX hBY ⊢
  Hint (hidden := true) "Puedes separar `{hBX}` y `{hBY}` en dos hipótesis, usando
  `choose` o `cases'`."
  choose hBX1 hBX2 using hBX
  choose hBY1 hBY2 using hBY
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Para ver el contenido, toma un elemento arbitrario con
    `intro`."
    intro W hW
    Hint (hidden := true) "Gracias a `{hW}`, puedes elegir (con `choose`) un elemento
    de `{BX}` (con sus propiedades)."
    choose Bx hBx By hBy hBxBy using hW
    Hint (hidden := true) "Reescribe el objetivo usando `{hBxBy}`."
    rw [← hBxBy]
    Hint (hidden := true) "Prueba a reescribir la definición de abierto en un producto."
    rw [def_abierto_producto]
    Hint (hidden := true) "Toma un punto arbitrario con `intro`."
    intro z hz
    Hint (hidden := true) "¿Qué abierto de `{X}` puedes usar?"
    use Bx
    Hint (hidden := true) "¿Qué abierto de `{Y}` puedes usar?"
    use By
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar `{hBX1}`."
      apply hBX1
      exact hBx
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar `{hBY1}`."
      apply hBY1
      exact hBy
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hz
    Hint (hidden := true) "Esto es trivial."
    trivial
  · Hint (hidden := true) "Toma un abierto arbitrario, y un punto en él, con `intro`."
    intro W hW z hz
    Hint (hidden := true) "Puedes reescribir la definición de abierto en un producto en
    `{hW}`."
    rw [def_abierto_producto] at hW
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`) aplicando
    `{hW}` a `{z}` y `{hz}`."
    have hWz := hW z hz
    Hint (hidden := true) "Ahora, usando `{hWz}`, puedes elegir (con choose) abiertos
    de `{X}` e `{Y}` cuyo producto contiene a `{z}` y está contenido en `{W}`."
    choose U1 V1 hU1 hV1 hzU1V1 hU1V1U using hWz
    Hint (hidden := true) "Puedes separar `{hzU1V1}` en dos hipótesis (con `choose` o `cases'`.)"
    choose hz1 hz2 using hzU1V1
    Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hBX2}` a `{U1}`, `{hU1}`, `{z}.1` y `{hz1}`."
    have hBXU := hBX2 U1 hU1 z.1 hz1
    Hint (hidden := true) "Gracias a `{hBXU}` puedes elegir un elemento de `{BX}`
    con ciertas propiedades."
    choose U hU hzU hUU1 using hBXU
    Hint (hidden := true) "Obten una nueva hipótesis (con `have`) aplicando
    `{hBY2}` a `{V1}`, `{hV1}`, `{z}.2` y `{hz2}`."
    have hBYV := hBY2 V1 hV1 z.2 hz2
    Hint (hidden := true) "Usa `{hBYV}` para elegir (con `choose`) un elemento de `{BY}`
    y sus propiedades."
    choose V hV hzV hVV1 using hBYV
    Hint (hidden := true) "¿Qué abierto intermedio puedes usar?"
    use U ×ˢ V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "¿Qué abierto de `{X}` pùedes usar?"
      use U
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · exact hU
      Hint (hidden := true) "¿Qué abierto de `{Y}` puedes usar?"
      use V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que en realidad, el objetivo son dos afirmaciones
      (una para cada componente)."
      fconstructor
      · exact hzU
      · exact hzV
    · Hint (hidden := true) "Para demostrar el contenido, toma un elemento arbitrario con
      `intro`."
      intro t ht
      Hint (hidden := true) "Puedes separar `{ht}` en dos hipótesis con `choose` o `cases'`."
      choose ht1 ht2 using ht
      Hint (hidden := true) "Puedes aplicar `{hU1V1U}`."
      apply hU1V1U
      Hint (hidden := true) "Observa que el objetivo son en realidad dos afirmaciones.
      Separalo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Puedes aplicar `{hUU1}`"
        apply hUU1
        exact ht1
      · Hint (hidden := true) "Puedes aplicar `{hVV1}`."
        apply hVV1
        exact ht2



end topo
