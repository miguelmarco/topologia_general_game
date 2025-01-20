import Game.Levels.Productos.DensoProducto
World "Productos"
Level 7
Title "Producto de conjuntos densos."

Introduction "
El producto de espacios separables es separable.

Para esto necesitaremos usar que el producto de conjuntos contables
es contable. El teorema `producto_contables` dice exactamente eso.
"

namespace topo
open topo espacio_topologico Set

variable {X Y : Type} [espacio_topologico X] [espacio_topologico Y]

theorem producto_contables (A : Set X) (B : Set Y) (hA : contable A) (hB : contable B) : contable (A ×ˢ B) := by
  cases' hA with hA hA
  · left
    rw [hA]
    simp only [empty_prod]
  · cases' hB with hB hB
    · left
      rw [hB]
      simp only [prod_empty]
    · right
      choose f1 hf1 using hA
      choose f2 hf2 using hB
      let ⟨g,gi,hg,hgi⟩  := Nat.pairEquiv
      simp only [Function.LeftInverse, Prod.forall] at hg
      simp only [Function.RightInverse, Function.LeftInverse] at hgi
      fconstructor
      · intro n
        exact (f1 (gi n).1, f2 (gi n).2)
      ext
      fconstructor
      · intro hx
        choose hx1 hx2 using hx
        rw [hf1] at hx1
        rw [hf2] at hx2
        choose n1 hn1 using hx1
        choose n2 hn2 using hx2
        use g (n1,n2)
        simp only [hg, simp_proj_1, proj_simp_1, hn1, Prod.snd_comp_mk, cancela_inver, hn2,
          simp_proj_2, Prod.mk.eta]
      · intro hx
        choose n hn using hx
        fconstructor
        · rw [hf1]
          use (gi n).1
          rw [← hn]
        · rw [hf2]
          use (gi n).2
          rw [← hn]

/--
El producto de dos conjuntos contables, es contable.
-/
TheoremDoc topo.producto_contables as "producto_contables" in "Producto"

NewTheorem topo.producto_contables




/--
Si `X` e `Y` son espacios separables. `X × Y` es separable.
-/
TheoremDoc topo.producto_separables as "producto_separables" in "Productos"

Statement producto_separables (hX : separable X) (hY : separable Y) : separable (X × Y) := by
  Hint (hidden := true) "Recuerda la definición de ser separable. `{hX}` y `{hY}` aseguran
  que existen densos numearbles en `{X}` e `{Y}`. Elígelos con `choose`."
  choose SX hsXd hsXc using hX
  choose SY hsYd hsYc using hY
  Hint (hidden := true) "Tienes que ver que existe un denso numerable en
  `{X} × {Y}`. Lo natural es usar `{SX} ×ˢ {SY}`."
  use SX ×ˢ SY
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Aquí puedes aplicar el resultado del nivel anterior."
    exact producto_densos SX SY hsXd hsYd
  · Hint (hidden := true) "Puedes aplicar `producto_contables`."
    apply producto_contables
    · exact hsXc
    · exact hsYc




end topo
