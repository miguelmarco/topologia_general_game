import Game.Levels.Separacion.CaracterizacionT2
World "Productos"
Level 1
Title "Entornos en un producto"

Introduction "
Dado el producto de dos espacios topológicos, se le puede dar
una estructura de espacio topológico forzando a que las proyecciones
sean aplicaciones contínuas.

En particular, se definen los abiertos de `X × Y` como los subconjuntos `S`
que cumplen que
`∀ z ∈ S, ∃ (U : Set X) (V : Set Y), U ∈ abiertos ∧ V ∈ abiertos ∧ z ∈ U ×ˢ V ∧ U ×ˢ V ⊆ S `.

El teorema `def_abierto_producto` recoge esa definición.

Veamos ahora una caracterización de los entornos de un punto en un producto.
"

TheoremTab "Productos"

namespace topo
open topo espacio_topologico Set


variable (X Y : Type) [espacio_topologico X] [espacio_topologico Y]


instance : espacio_topologico (X × Y) where
  abiertos := {S  | ∀ z ∈ S, ∃ (U : Set X) (V : Set Y), U ∈ abiertos ∧ V ∈ abiertos ∧ z ∈ U ×ˢ V ∧ U ×ˢ V ⊆ S}
  abierto_vacio := by
    intro z hz
    cases hz
  abierto_total := by
    intro z hz
    use univ
    use univ
    simp only [abierto_total, univ_prod_univ, mem_univ, subset_univ, and_self]
  union_abiertos := by
    intro F hF z hz
    choose S hSF hzS using hz
    specialize hF hSF z hzS
    choose U V hU hV hzUV hUV using hF
    use U
    use V
    fconstructor
    exact hU
    fconstructor
    exact hV
    fconstructor
    exact hzUV
    exact subset_sUnion_of_subset F S hUV hSF
  interseccion_abiertos := by
    intro S1 S2 hS1 hS2
    intro z hz
    specialize hS1 z hz.1
    specialize hS2 z hz.2
    choose U1  V1 hU1 hV1 hzU1 hU1V1 using hS1
    choose U2 V2 hU2 hV2 hzU2 hU2V2 using hS2
    use (U1 ∩ U2)
    use (V1 ∩ V2)
    fconstructor
    · apply interseccion_abiertos
      exact hU1
      exact hU2
    fconstructor
    · apply interseccion_abiertos
      exact hV1
      exact hV2
    fconstructor
    · fconstructor
      · exact ⟨hzU1.1,hzU2.1⟩
      · exact ⟨hzU1.2,hzU2.2⟩
    intro t ht
    fconstructor
    · apply hU1V1
      fconstructor
      · apply ht.1.1
      · apply ht.2.1
    · apply hU2V2
      fconstructor
      · apply ht.1.2
      · apply ht.2.2

theorem def_abierto_producto (S : Set (X × Y)) :
    S ∈ abiertos ↔ ∀ z ∈ S, ∃ U V, U ∈ abiertos ∧ V ∈ abiertos ∧ z ∈ U ×ˢ V ∧ U ×ˢ V ⊆ S := by
  rfl


/--
Dados dos espacios topológicos `X, Y` y un conjunto `S ⊆ X × Y`, `def_abierto_producto S`
dice que `S ∈ abiertos ↔ ∀ z ∈ S, ∃ U V, U ∈ abiertos ∧ V ∈ abiertos ∧ z ∈ U ×ˢ V ∧ U ×ˢ V ⊆ S`.
-/
TheoremDoc topo.def_abierto_producto as "def_abierto_producto" in "Productos"

NewTheorem topo.def_abierto_producto


abbrev π₁ {X Y : Type} : X × Y → X := fun z ↦ z.1
abbrev π₂ {X Y : Type} : X × Y → Y := fun z ↦ z.2

@[simp]
theorem simp_proj_1 (z : X × Y) : z.1 = π₁ z := rfl

@[simp]
theorem simp_proj_2 (z : X × Y) : z.2 = π₂ z := rfl

@[simp]
theorem proj_simp_1 (x : X) (y : Y) : π₁ (x , y) = x := rfl

@[simp]
theorem proj_simp_2 (x : X) (y : Y) : π₂ (x , y) = y := rfl


/--
Dado un punto `z` en un espacio producto `X × Y` y un conjunto `N ⊆ X × Y`,
`entorno_producto_sii z N` dice que `N` es entorno de `z` si y solo si existen
abiertos `U` y `V` en `X` e `Y` tales que `z ∈ U ×ˢ V` y `U ×ˢ V ⊆ N`.
-/
TheoremDoc topo.caracterizacion_entorno_producto as "caracterizacion_entorno_producto" in "Productos"


Statement caracterizacion_entorno_producto (z : X × Y) (N : Set (X × Y)) : entorno z N ↔ ∃ U V, U ∈ abiertos ∧ V ∈ abiertos ∧ z.1 ∈ U ∧ z.2 ∈ V ∧ U ×ˢ V ⊆ N := by
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antededente con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reescribir la definición de entorno en `{h}`."
    rw [def_entorno] at h
    Hint (hidden := true) "Puedes elegir un abierto intermedio (con `choose`) usando `{h}`."
    choose S hS hzS hSN using h
    Hint (hidden := true) "Como `{S}` es un abierto en un espacio producto,
    puedes reescribir `{hS}` con la definición de abiertos de un producto."
    rw [def_abierto_producto] at hS
    Hint (hidden := true) "Ahora puedes obtener (con `have`) una nueva hipótesis
    aplicando `{hS}` a `{z}` y `{hzS}`."
    have hS2 := hS z hzS
    Hint (hidden := true) "Ahora, gracias a `{hS2}`, puedes elegir abiertos en
    `{X}` e `{Y}` con las propiedades correspondientes."
    choose U V hU hV hzUV hUVS using hS2
    Hint (hidden := true) "Ahora, ¿qué abierto de `{X}` puedes usar?"
    use U
    Hint (hidden := true) "¿Y qué abierto de `{Y}` puedes usar?"
    use V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hV
    Hint (hidden := true) "Puedes simplificar `{hzUV}`."
    simp only [mem_prod, simp_proj_1, simp_proj_2] at hzUV
    Hint (hidden := true) "Puedes separar `{hzUV}` en dos hipótesis con `choose` o `cases'`."
    choose hzU hzV using hzUV
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hzU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hzV
    · Hint (hidden := true) "Para ver que un conjunto está contenido en otro, toma un elemento
      arbitrario con `intro`."
      intro x hx
      Hint (hidden := true) "Puedes aplicar `{hSN}`."
      apply hSN
      Hint (hidden := true) "Puedes aplicar `{hUVS}`."
      apply hUVS
      exact hx
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Gracias a `{h}`, puedes elegir abiertos
    de `{X}` e `{Y}` con ciertas proiedades (con `choose`)."
    choose U V hU hV hzU hzV hUVN using h
    Hint (hidden := true) "Puedes reescribir la definición de entorno."
    rw [def_entorno]
    Hint (hidden := true) "¿Qué abierto del producto puedes usar?"
    Hint (hidden := true) "Recuerda que el producto de dos *subconjuntos*
    se escribe con `×ˢ`."
    use U ×ˢ V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Tendrás que reescribir la definición de abierto
      en el producto."
      rw [def_abierto_producto]
      Hint (hidden := true) "Toma un elemento arbitrario con `intro`."
      intro z hzUV
      Hint (hidden := true) "¿Qué abierto de `{X}` puedes usar?"
      use U
      Hint (hidden := true) "¿Qué abierto de `{Y}` puedes usar?"
      use V
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Prueba a simplificar el objetivo."
      simp only [mem_prod, simp_proj_1, simp_proj_2]
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · exact hzU
      · exact hzV
    · exact hUVN



end topo
