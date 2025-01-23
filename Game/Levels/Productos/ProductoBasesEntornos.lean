import Game.Levels.Productos.ProductoEntornos
World "Productos"
Level 9
Title "Producto de bases de entornos"

Introduction "
Si `x` e `y` son puntos en los espacios topológicos `X` e `Y`, y
`𝓑x` y `𝓑y` son bases de entornos de esos puntos, entonces
`{Bx ×ˢ By} | (Bx ∈ 𝓑x) (By ∈ 𝓑y)}` es una base de entornos de `(x,y)`

"



namespace topo
open topo espacio_topologico Set

variable {X Y : Type} [espacio_topologico X] [espacio_topologico Y]


/--
Si `x` e `y` son puntos en los espacios topológicos `X` e `Y`, y
`𝓑x` y `𝓑y` son bases de entornos de esos puntos, entonces
`{Bx ×ˢ By} | (Bx ∈ 𝓑x) (By ∈ 𝓑y)}` es una base de entornos de `(x,y)`
-/
TheoremDoc topo.producto_bases_entornos as "producto_bases_entornos" in "Productos"

Statement producto_bases_entornos
  {x : X}
  {y : Y}
  {Bx : Set (Set X)}
  {By : Set (Set Y)}
  (hBx : base_de_entornos x Bx)
  (hBy : base_de_entornos y By)
  :
    base_de_entornos (x , y)  { Nx ×ˢ Ny | (Nx ∈ Bx) (Ny ∈ By) }  := by
  Hint (hidden := true) "Observa que `{hBx}` y `{hBy}` en realidad
  afirman dos cosas cada una. Puedes separarlas con `choose` o `cases'`."
  choose hBx1 hBx2 using hBx
  choose hBy1 hBy2 using hBy
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
    intro N hN
    Hint (hidden := true) "`{hN}` asegura que existen elementos de `{Bx}`
    y `{By}` con ciertas propiedades. Puedes elegirlos con `choose`."
    choose Nx hNx Ny hNy hNxNy using hN
    Hint (hidden := true) "Puedes usar `{hNxNy}` para reescribir el objetivo."
    rw [← hNxNy]
    Hint (hidden := true) "Puedes aplicar el teorema que asegura que el producto
    de entornos es entorno."
    apply producto_entornos
    · Hint (hidden := true) "Puedes aplicar `{hBx1}`."
      apply hBx1
      exact hNx
    · Hint (hidden := true) "Puedes aplicar `{hBy1}`."
      apply hBy1
      exact hNy
  · intro N hN
    Hint (hidden := true) "Será útil reescribir la caracterización de entorno
    en un producto con en `{hN}`."
    rw [caracterizacion_entorno_producto] at hN
    Hint (hidden := true) "`{hN}` te asegura que existen abiertos
    con ciertas propiedades. Eligelos con `choose`."
    choose U V hU hV hxU hyV hUVN using hN
    Hint (hidden := true) "Ahora necesitamos probar un objetivo secundario:
    En particular, necesitaremos que existe un elemento de `{Bx}` contenido
    en `{U}`.

    Introduce este nuevo objetivo con `have haux1 : ∃ Nx ∈ {Bx}, Nx ⊆ {U}`.
    "
    have hx : ∃ Nx ∈ Bx , Nx ⊆ U
    · Hint (hidden := true) "Puedes probarlo aplicando `{hBx2}`."
      apply hBx2
      use U
    Hint (hidden := true) "Ahora necesitamos otro objetivo secundario
    igual que antes, pero con `{By}` y `{V}` en lugar de `{Bx}` y `{U}`."
    have hy : ∃ Ny ∈ By, Ny ⊆ V
    · apply hBy2
      use V
    Hint (hidden := true) "Como `{hx}` nos asegura que existe un cierto
    elemento de `{Bx}`, puedes elegir uno con `choose`."
    choose Nx hNx hNxU using hx
    Hint (hidden := true) "Puedes elegir un elemento de `{By}` gracias
    a `{hy}` con `choose`."
    choose Ny hNy hNyV using hy
    Hint (hidden := true) "¿Qué elemento de la familia puedes usar?"
    use Nx ×ˢ Ny
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "¿Qué elemento de `{Bx}` puedes usar?"
      use Nx
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · exact hNx
      Hint (hidden := true) "¿Qué elemento de `{By}` puedes usar?."
      use Ny
    · Hint (hidden := true) "Toma un elemento arbitrario de `{Nx} ×ˢ {Ny}`
      con `intro`."
      intro z hz
      Hint (hidden := true) "Observa que `{hz}` dice trealmente dos cosas,
      separalas con `choose` o `cases'`."
      choose hz1 hz2 using hz
      Hint (hidden := true) "Puedes aplicar `{hUVN}`."
      apply hUVN
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Puedes aplicar `{hNxU}`."
        apply hNxU
        exact hz1
      · Hint (hidden := true) "Puedes aplicar `{hNyV}`."
        apply hNyV
        exact hz2


end topo
