import Game.Levels.Productos.ProyeccionContinua
World "Productos"
Level 3
Title "Clausura de un poducto"

Introduction "
Veamos una relación entre las clausuras y los productos.
"

namespace topo
open topo espacio_topologico Set


variable (X Y : Type) [espacio_topologico X] [espacio_topologico Y]



theorem proyeccion_continua_2 : continua (π₂ : X × Y → Y) := by
  intro U hU
  rw [abierto_sii_entorno]
  intro z hz
  simp only [mem_preimage] at hz
  rw [caracterizacion_entorno_producto]
  use univ
  use U
  fconstructor
  · exact abierto_total
  fconstructor
  · exact hU
  fconstructor
  · trivial
  fconstructor
  · exact hz
  · intro a ha
    simp only [mem_preimage]
    simp only [mem_prod, simp_proj_1, mem_univ, simp_proj_2, true_and] at ha
    exact ha


/--
Dado un producto de espacios topológicos `X × Y`, `proyeccion_continua_2` dice
que la proyección `π₂ : X × Y → Y` es contínua.
-/
TheoremDoc topo.proyeccion_continua_2 as "proyeccion_continua_2" in "Productos"

NewTheorem topo.proyeccion_continua_2



/--
Dado un producto de espacios topológicos `X × Y`, y dos subconjuntos `A` y `B` de
`X` e `Y` respectivamente, `clausura_producto A B` dice que `clausura A ×ˢ B = clausura A ×ˢ clausura B`.
-/
TheoremDoc topo.clausura_producto as "clausura_producto" in "Productos"


Statement clausura_producto (A : Set X) (B : Set Y) : clausura (A ×ˢ B) = clausura A ×ˢ clausura B := by
  ext z
  fconstructor
  · intro hz
    rw [caracterizacion_clausura] at hz
    fconstructor
    · rw [caracterizacion_clausura]
      intro U hU hzU
      have hfU := proyeccion_continua_1 X Y U hU
      have hz2 := hz (π₁ ⁻¹' U) hfU hzU
      choose y hyU hyA hyB using hz2
      use π₁ y
      fconstructor
      · exact hyU
      · exact hyA
    · rw [caracterizacion_clausura]
      intro U hU hzU
      have hfU := proyeccion_continua_2 X Y U hU
      have hz2 := hz (π₂ ⁻¹' U) hfU hzU
      choose y hyU hyA hyB using hz2
      use π₂ y
      fconstructor
      · exact hyU
      · exact hyB
  · intro hz
    choose hzA hzB using hz
    rw [caracterizacion_clausura_entornos]
    intro N hN
    rw [caracterizacion_entorno_producto] at hN
    choose U V hU hV hzU hzV hUVN using hN
    rw [caracterizacion_clausura] at hzA hzB
    have hzAU := hzA U hU hzU
    have hzBV := hzB V hV hzV
    choose y1 hy1U hy1A using hzAU
    choose y2 hy2V hy2B using hzBV
    use (y1, y2)
    fconstructor
    · apply hUVN
      fconstructor
      · exact hy1U
      · exact hy2V
    · simp only [mem_prod]
      fconstructor
      · exact hy1A
      · exact hy2B





end topo
