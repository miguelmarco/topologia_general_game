import Game.Levels.Separacion.CaracterizacionT2




namespace topo
open topo espacio_topologico Set Set.Notation

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
    S ∈ abiertos ↔ ∀ z ∈ S, ∃ (U : Set X) (V : Set Y), U ∈ abiertos ∧ V ∈ abiertos ∧ z ∈ U ×ˢ V ∧ U ×ˢ V ⊆ S := by
  rfl


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


theorem continua_proyeccion_1 : continua (π₁ : X × Y → X)   := by
  intro U hU
  rw [def_abierto_producto]
  intro z hz
  use U
  use univ
  fconstructor
  · exact hU
  fconstructor
  · exact abierto_total
  fconstructor
  · simp only [mem_prod, simp_proj_1, simp_proj_2, mem_univ, and_true]
    exact hz
  · intro x hx
    simp only [mem_prod, simp_proj_1, simp_proj_2, mem_univ, and_true] at hx
    exact hx

theorem continua_proyeccion_2 : continua (π₂ : X × Y → Y)   := by
  intro V hV
  rw [def_abierto_producto]
  intro z hz
  use univ
  use V
  fconstructor
  · exact abierto_total
  fconstructor
  · exact hV
  fconstructor
  · simp only [mem_prod, simp_proj_1, mem_univ, simp_proj_2, true_and]
    exact hz
  · intro x hx
    simp only [mem_prod, simp_proj_1, mem_univ, simp_proj_2, true_and] at hx
    exact hx

theorem abierta_proyeccion_1 : abierta (π₁ : X × Y → X) := by
  intro U hU
  rw [abierto_sii_entorno]
  intro x hx
  simp only [mem_image, Prod.exists] at hx
  choose a b hab habx using hx
  simp only [proj_simp_1] at habx
  rw [def_abierto_producto] at hU
  have hUx := hU (a, b) hab
  choose V1 V2 hV1 hV2 habV hV1V2U using hUx
  choose haV1 hbV2 using habV
  simp only at haV1
  simp only at hbV2
  use V1
  fconstructor
  · trivial
  fconstructor
  · rw [habx] at haV1
    exact haV1
  · intro z hz
    use (z, b)
    fconstructor
    · apply hV1V2U
      fconstructor
      · simp only
        exact hz
      · simp only
        exact hbV2
    · trivial

theorem abierta_proyeccion_2 : abierta (π₂ : X × Y → Y) := by
  intro U hU
  rw [abierto_sii_entorno]
  intro x hx
  simp only [mem_image, Prod.exists] at hx
  choose a b hab habx using hx
  simp only [proj_simp_2] at habx
  rw [def_abierto_producto] at hU
  have hUx := hU (a, b) hab
  choose V1 V2 hV1 hV2 habV hV1V2U using hUx
  choose haV1 hbV2 using habV
  simp only at haV1
  simp only at hbV2
  use V2
  fconstructor
  · trivial
  fconstructor
  · rw [ habx] at hbV2
    exact hbV2
  · intro z hz
    use (a, z)
    fconstructor
    · apply hV1V2U
      fconstructor
      · simp only
        exact haV1
      · simp only
        exact hz
    · trivial



theorem producto_abiertos (U : Set X) (V : Set Y) (hU : U ∈ abiertos) (hV : V ∈ abiertos) :
    U ×ˢ V ∈ abiertos := by
  rw [def_abierto_producto]
  intro z hz
  use U
  use V


theorem clausura_producto (A1 : Set X) (A2 : Set Y) : clausura (A1 ×ˢ A2) = clausura A1 ×ˢ clausura A2 := by
  ext z
  fconstructor
  · intro hz
    rw [caracterizacion_clausura] at hz
    simp only [mem_prod]
    fconstructor
    · rw [caracterizacion_clausura]
      intro U hU hzU
      have haux : ∃ y, y ∈ (U ×ˢ univ) ∩  (A1 ×ˢ A2 )
      · apply hz
        apply producto_abiertos
        exact hU
        exact abierto_total
        simp only [mem_prod, simp_proj_1, simp_proj_2, mem_univ, and_true]
        exact hzU
      choose y hy1 hy2 using haux
      use y.1
      fconstructor
      · simp only [mem_prod, simp_proj_1, simp_proj_2, mem_univ, and_true] at hy1
        exact hy1
      · choose hy3 hy4 using hy2
        exact hy3
    · rw [caracterizacion_clausura]
      intro U hU hz2
      have haux : ∃ y, y ∈ (univ ×ˢ U) ∩ (A1 ×ˢ A2)
      · apply hz
        apply producto_abiertos
        apply abierto_total
        exact hU
        simp only [mem_prod, simp_proj_1, mem_univ, simp_proj_2, true_and]
        exact hz2
      choose y hy1 hy2 using haux
      use y.2
      fconstructor
      · simp only [mem_prod, simp_proj_1, mem_univ, simp_proj_2, true_and] at hy1
        exact hy1
      · choose hy3 hy4 using hy2
        exact hy4
  · intro h
    rw [caracterizacion_clausura]
    intro U hU hz
    choose h1 h2 using h
    rw [caracterizacion_clausura] at h1
    rw [caracterizacion_clausura] at h2
    rw [def_abierto_producto] at hU
    have hUz := hU z hz
    choose U1 U2 hU1 hU2 hzU1U2 hU1U2U using hUz
    choose hzU1 hzU2 using hzU1U2
    have h1z := h1 U1 hU1 hzU1
    have h2z := h2 U2 hU2 hzU2
    choose y1 hy1U hy1A1 using h1z
    choose y2 hy2U hy2A2 using h2z
    use ⟨y1,y2⟩
    fconstructor
    · apply hU1U2U
      fconstructor
      · exact hy1U
      · exact hy2U
    · fconstructor
      · exact hy1A1
      · exact hy2A2

theorem interior_producto (A1 : Set X) (A2 : Set Y) : interior (A1 ×ˢ A2) = interior A1 ×ˢ interior A2 := by
  ext z
  fconstructor
  · intro h
    rw [caracterizacion_interior] at h
    choose U hU hzU hUA1A2 using h
    rw [def_abierto_producto] at hU
    have hU2 := hU z hzU
    choose U1 U2 hU1 hU2 hzU1U2 hU1U2U using hU2
    fconstructor
    · rw [caracterizacion_interior]
      use U1
      fconstructor
      · exact hU1
      fconstructor
      · exact hzU1U2.1
      intro x hx
      have hxaux : (x, π₂ z) ∈ A1 ×ˢ A2
      · apply hUA1A2
        apply hU1U2U
        fconstructor
        · exact hx
        · simp only [simp_proj_2]
          exact hzU1U2.2
      exact hxaux.1
    · rw [caracterizacion_interior]
      use U2
      fconstructor
      · exact hU2
      fconstructor
      · exact hzU1U2.2
      intro y hy
      have hyaux : (π₁ z,y) ∈ A1 ×ˢ A2
      · apply hUA1A2
        apply hU1U2U
        fconstructor
        · exact hzU1U2.1
        · exact hy
      exact hyaux.2
  · intro h
    rw [caracterizacion_interior]
    use interior A1 ×ˢ interior A2
    fconstructor
    · apply producto_abiertos
      apply interior_abierto
      apply interior_abierto
    fconstructor
    · exact h
    · intro x hx
      choose hx1 hx2 using hx
      fconstructor
      · apply interior_contenido
        exact hx1
      · apply interior_contenido
        exact hx2

theorem caracterizacion_contina_producto (Z : Type) [espacio_topologico Z] (f : Z → X ×  Y) : continua f ↔ continua (π₁ ∘ f : Z → X) ∧ continua (π₂ ∘ f : Z → Y):= by
  fconstructor
  · intro hf
    fconstructor
    · apply composicion_continuas
      · exact hf
      · apply continua_proyeccion_1
    · apply composicion_continuas
      · exact hf
      · apply continua_proyeccion_2
  · intro h
    choose h1 h2 using h
    intro U hU
    rw [abierto_sii_entorno]
    intro z hz
    simp only [mem_preimage] at hz
    rw [def_abierto_producto] at hU
    have hUz := hU (f z) hz
    choose U1 U2 hU1 hU2 hzU1U2 hU1U2U using hUz
    have h1U1 := h1 U1 hU1
    have h2U2 := h2 U2 hU2
    use (π₁ ∘ f) ⁻¹' U1 ∩  (π₂ ∘ f )⁻¹' U2
    fconstructor
    · apply interseccion_abiertos
      · exact h1U1
      · exact h2U2
    fconstructor
    · exact hzU1U2
    · intro t ht
      simp only [mem_preimage]
      apply hU1U2U
      exact ht
















end topo
