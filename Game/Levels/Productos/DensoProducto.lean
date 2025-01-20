import Game.Levels.Productos.ContinuaProducto
World "Productos"
Level 6
Title "Producto de conjuntos densos."

Introduction "
Vamos con una demostración cortita: el producto de densos es denso.
"

namespace topo
open topo espacio_topologico Set


variable {X Y : Type} [espacio_topologico X] [espacio_topologico Y]

/--
El producto de conjuntos densos es denso.
-/
TheoremDoc topo.producto_densos as "producto_densos" in "Productos"

Statement producto_densos (A : Set X) (B : Set Y) (hA : denso A) (hB : denso B) :
    denso (A ×ˢ B) := by
  Hint (hidden := true) "Prueba a reescribir la definición de denso en
  las hipótesis y en el objetivo."
  rw [def_denso] at hA hB ⊢
  Hint (hidden := true) "Tenemos un teorema que nos dice cual es
  la clausura de un producto. Usalo para reescribir el objetivo."
  rw [clausura_producto]
  Hint (hidden := true) "Puedes usar `{hA}` y `{hB}` para reescribir el objetivo."
  rw [hA]
  rw [hB]
  Hint (hidden := true) "Esto se puede ver simplificando."
  simp only [univ_prod_univ]


end topo
