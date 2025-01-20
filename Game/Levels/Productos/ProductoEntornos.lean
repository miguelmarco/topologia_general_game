import Game.Levels.Productos.SeparableProducto
World "Productos"
Level 8
Title "Producto de entornos."

Introduction "
Si `x` e `y` son puntos en espacios topológicos `X` e `Y`, y
`Nx`, `Ny` son entornos suyos, `Nx ×ˢ Ny` es entorno de `(x, y)`.

"

namespace topo
open topo espacio_topologico Set

variable {X Y : Type} [espacio_topologico X] [espacio_topologico Y]


/--
Si `x` e `y` son puntos en espacios topológicos `X` e `Y`, y
`Nx`, `Ny` son entornos suyos, `Nx ×ˢ Ny` es entorno de `(x, y)`.
-/
TheoremDoc topo.producto_entornos as "productoentorno_s" in "Productos"

Statement producto_entornos
  {x : X}
  {y : Y}
  {Nx : Set X}
  {Ny : Set Y}
  (hNx : entorno x Nx)
  (hNy : entorno y Ny)
  :
    entorno (x , y)  (Nx  ×ˢ Ny)  := by
  Hint (hidden := true) "Recuerda la definición de entorno. `{hNx}`
  y `{hNy}` nos aseguran que existen abiertos con ciertas propiedades.
  Puedes elegir unos con `choose`."
  choose U hU hxU hUN using hNx
  choose V hV hyV hVN using hNy
  Hint (hidden := true) "Será útil reescribir el objetivo usando
  la caracterización de entornos en un producto."
  rw [caracterizacion_entorno_producto]
  Hint (hidden := true) "¿Qué abiertos en `{X}` e `{Y}` puedes usar?"
  use U
  use V
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hU
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hV
  fconstructor
  · exact hxU
  fconstructor
  · exact hyV
  Hint (hidden := true) "Para ver el contenido, hay que tomar un elemento
  arbitrario con `intro`."
  intro t ht
  Hint (hidden := true) "Observa que `{ht}` son realmente dos afirmaciones
  (una por cada componente). Separalas usando `choose` o `cases'`."
  choose ht1 ht2 using ht
  Hint (hidden := true) "Observa que el objetivo son realmente dos
  afirmaciones. Sepáralas con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes aplicar `{hUN}`."
    apply hUN
    exact ht1
  · apply hVN
    exact ht2


end topo
