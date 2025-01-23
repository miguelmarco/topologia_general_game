import Game.Levels.Productos.ProductoBasesEntornos
World "Productos"
Level 10
Title "Producto de espacios 1-numerables"

Introduction "
Si los espacios topológicos `X` e `Y` son `IAN`, entonces
su producto también lo es.

En esta demostración vamos a demostrar que, dadas dos familias
contables de conjuntos, la familia de todos los productos de elementos
suyos, es también contable. Este teorema se llama `producto_familias_contables`.
"



namespace topo
open topo espacio_topologico Set

variable {X Y : Type} [espacio_topologico X] [espacio_topologico Y]


theorem productos_familias_contables (A : Set (Set X)) (B : Set (Set Y)) (hA : contable A) (hB : contable B) :
    contable { U ×ˢ V | (U ∈ A) (V ∈ B)} := by
  have haux := producto_contables A B hA hB
  cases' haux
  · left
    simp only [prod_eq_empty_iff] at h
    cases' h
    rw [h_1]
    simp
    rw [h_1]
    simp
  · right
    choose f hf1 using h
    fconstructor
    · intro n
      let S := f n
      exact S.1 ×ˢ S.2
    · ext S
      simp only [mem_setOf_eq, simp_proj_1, simp_proj_2]
      fconstructor
      · intro
        choose U hU V hV hUVS using a
        have hUAB : (U, V) ∈ A ×ˢ B
        · exact ⟨ hU,hV⟩
        rw [hf1] at hUAB
        choose n hn using hUAB
        use n
        rw [hn]
        exact hUVS
      · intro h
        choose n hn using h
        let W := f n
        let AW := W.1
        let BW := W.2
        have hW : (AW, BW) ∈ A ×ˢ B
        · rw [hf1]
          use n
        use AW
        fconstructor
        · exact hW.1
        use BW
        fconstructor
        · exact hW.2
        exact hn

/--
Si `A` y `B` son familias contables de subconjuntos de `X` e `Y` respectivamente,
entonces la familia `{ U ×ˢ V | (U ∈ A) (V ∈ B)}` es también contable.
-/
TheoremDoc topo.productos_familias_contables as "producto_familias_contables" in "Productos"

NewTheorem topo.productos_familias_contables


/--
Si `X` e `Y` son espacios `IAN`, entonces `X × Y` también lo es.
-/
TheoremDoc topo.producto_IAN as "producto_IAN" in "Productos"

Statement producto_IAN
  (hX : IAN X)
  (hY : IAN Y)
  :
    IAN (X × Y)  := by
  Hint (hidden := true) "Como ser `IAN` es una propiedad
  sobre cada punto, toma un punto arbitrario con `intro`."
  intro z
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hX}`  a la primera coordenada de `{z}`."
  have hx := hX z.1
  Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
  aplicando `{hY}`  a la segunda coordenada de `{z}`."
  have hy := hY z.2
  Hint (hidden := true) "Como `{hx}` te asegura que existen bases
  de entornos contables de `{z}.1`, puedes elegir una con `choose`."
  choose Bx hBx hBxcont using hx
  Hint (hidden := true) "Como `{hy}` te asegura que existen bases
  de entornos contables de `{z}.2`, puedes elegir una con `choose`."
  choose By hBy hBycont using hy
  Hint (hidden := true) "Si recuerdas la demostración en papel, la
  familia que hay que usar es `\{Nx ×ˢ Ny | (Nx ∈ {Bx}) (Ny ∈ {By})}`."
  use { Nx ×ˢ Ny | (Nx ∈ Bx) (Ny ∈ By)}
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  Hint (hidden := true) "Para ver que es base de entornos, podemos
  aplicar el resultado del nivel anterior."
  apply producto_bases_entornos
  · exact hBx
  · exact hBy
  Hint (hidden := true) "Aquí podemos aplicar `productos_familias_contables`."
  apply productos_familias_contables
  · exact hBxcont
  · exact hBycont


end topo
