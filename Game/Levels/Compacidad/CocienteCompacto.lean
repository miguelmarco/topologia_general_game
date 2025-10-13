import Game.Levels.Compacidad.CompactoT2

World "Compacidad"
Level 5
Title "Cocientes de compactos"

Introduction "Vamos a ver un resultado fácil:
la imagen de un conjunto compacto en un cociente
es compacto.

También es cierto que el producto de compactos es compacto,
pero eso no lo demostraremos, sino que vamos a dar por
visto el teorema `producto_compacto`, que dice exactamente eso.
"

namespace topo
open espacio_topologico topo Set Set.Finite

variable {X: Type} [Nonempty X] [espacio_topologico X]

/--
Si `U` es un conjunto infinito dentro de un compacto `K`, entonces
`U` tiene algún punto de acumulación.
-/
TheoremDoc topo.compacto_acumulacion as "compacto_acumulacion" in "Compacidad"


theorem compacto_acumulacion (K U : Set X) (hK : compacto K) (hU : U ⊆ K) (hinf : ¬ Set.Finite U) :
    (derivado U : Set X) ≠ ∅ := by
  intro hneg
  apply hinf
  have haux := clausura_union_derivado_aislado U
  rw [hneg] at haux
  simp only [empty_union] at haux
  have haix : aislados U = U
  · ext x
    fconstructor
    · rw [def_aislados]
      intro h
      simp only [unipuntual_sii, mem_inter_iff, and_imp, mem_setOf_eq] at h
      choose V hVab hV1 hV2  using h
      exact hV1.2
    · intro h
      rw [← haux]
      apply clausura_contiene
      exact h
  have hcer : U ∈ cerrados
  · rw [caracterizacion_cerrado_clausura]
    rw [haux]
    rw [haix]
  have haux2 := cerrado_compacto K U hK hcer hU
  have hrec : ∀ x ∈ U, ∃ V ∈ abiertos, V ∩ U = {x}
  · intro x hx
    rw [← haix] at hx
    rw [def_aislados] at hx
    exact hx
  choose! f hf1 hf2  using hrec
  let F := f '' U
  have hF1 : F ⊆ abiertos
  · intro V hV
    choose x hx1 hx2 using hV
    rw [← hx2]
    apply hf1
    exact hx1
  have hF2 : recubrimiento U F
  · intro x hx
    use f x
    fconstructor
    · use x
    · have hx1 := hf2 x hx
      simp only [unipuntual_sii, mem_inter_iff, and_imp] at hx1
      tauto
  have hC := haux2 F hF1 hF2
  choose S hS1 hS2 hS3 using hC
  rw [def_recubrimiento] at hS3
  have hS4 : ∀ V ∈ S, ∃ x ∈ U,  f x = V
  · intro V hV
    have hS5 := hS1 hV
    choose x hx hx2 using hS5
    use x
  choose! g hg1 hg2 using hS4
  have hf : ∀ (x y), x ∈ U → y ∈ U → f x = f y → x = y
  · intro x y hx hy hxy
    have hf1x := hf2 x hx
    have hf2x := hf2 y hy
    rw [← hxy] at hf2x
    simp only [unipuntual_sii, mem_inter_iff, and_imp] at hf2x
    choose hx1 hx2 using hf2x
    apply hx2
    simp only [unipuntual_sii, mem_inter_iff, and_imp] at hf1x
    tauto
    exact hx
  have hUS : U = g '' S
  · ext x
    fconstructor
    · intro hx
      specialize hS3 hx
      choose V hV1 hV2 using hS3
      have hxV : x = g  V
      · apply hf
        exact hx
        apply hg1
        exact hV1
        rw [hg2]
        specialize hS1 hV1
        choose y hy1 hy2 using hS1
        have hf2y := hf2 y hy1
        have hf2x := hf2 x hx
        rw [← hy2] at hV2
        simp only [unipuntual_sii, mem_inter_iff, and_imp] at hf2y
        choose hxyh1 hxy2 using hf2y
        specialize hxy2 x hV2 hx
        rw [hxy2,hy2]
        exact hV1
      use V
      tauto
    · intro hx
      choose V hV hV2 using hx
      rw [← hV2]
      apply hg1
      exact hV
  rw [hUS]
  apply Finite.image
  exact hS2

theorem compacto_producto_base {Y : Type} [espacio_topologico Y] (KX : Set X) (KY : Set Y) (x0 : X) (y0 : Y) (hx0 : x0 ∈ KX) (hy0 : y0 ∈ KY)  :
    compacto (KX ×ˢ KY)  ↔ ∀ (F : Set (Set (X × Y))), (F ⊆ abiertos → recubrimiento (KX ×ˢ KY) F → (∀ W ∈ F, ∃ (U : Set X) (V : Set Y) , (U ∈ abiertos) ∧ (V ∈ abiertos) ∧  W = U ×ˢ V) →
    ∃ S ⊆ F, Set.Finite S ∧ recubrimiento (KX ×ˢ KY) S) := by
  fconstructor
  · intro h
    intro F hFab hFrec hF
    apply h
    exact hFab
    apply hFrec
  · intro h
    intro F hFab hrec
    have hF1 : ∀ p ∈ (KX ×ˢ KY), ∃ (W : Set (X × Y)) (U : Set X) (V : Set Y), U ∈ abiertos ∧ V ∈ abiertos ∧ W ∈ F ∧ p ∈ U ×ˢ V ∧ U ×ˢ V ⊆ W
    · intro p hp
      have hpF := hrec hp
      choose W hWF hpW using hpF
      use W
      have hWab := hFab hWF
      rw [def_abierto_producto] at hWab
      have hpUV := hWab p hpW
      tauto
    choose! fW fU fV hfU hfV hfW hfpUV hfUVW using hF1
    let G := { fU p ×ˢ fV p | p ∈ KX ×ˢ KY}
    have hGab : G ⊆ abiertos
    · intro W hW
      choose p hp hpW using hW
      rw [← hpW]
      rw [def_abierto_producto]
      intro z hz
      use fU p
      use fV p
      tauto
    have hGrec : recubrimiento (KX ×ˢ KY) G
    · intro p hp
      use fU p ×ˢ fV p
      tauto
    have hGUV : ∀ W ∈ G, ∃ U V, U ∈ abiertos ∧ V ∈ abiertos ∧ W = U ×ˢ V
    · intro W hW
      choose p hpKXY hpW using hW
      use fU p
      use fV p
      tauto
    specialize h G hGab hGrec hGUV
    choose S hSG hSfin hSrec using h
    have hS : ∀ s ∈ S, ∃ W ∈ F, s ⊆ W
    · intro s hs
      specialize hSG hs
      choose p hp hpUV  using hSG
      use fW p
      fconstructor
      · apply hfW
        exact hp
      · rw [← hpUV]
        apply hfUVW
        exact hp
    choose! g hgF hsgs using hS
    use g '' S
    fconstructor
    · intro s hs
      choose p hp hps using hs
      rw [← hps]
      apply hgF
      exact hp
    fconstructor
    · apply Finite.image
      exact hSfin
    · intro z hz
      specialize hSrec hz
      choose s hs hsz using hSrec
      use g s
      fconstructor
      · use s
      · apply hsgs
        apply hs
        apply hsz

/--
El producto de espacios compactos no vaciós es compacto.
-/
TheoremDoc topo.producto_compacto as "producto_compacto" in "Compacidad"

theorem producto_compacto {Y : Type} [espacio_topologico Y] [Nonempty Y] (KX : Set X) (KY : Set Y) (x0 : X) (y0 : Y) (hx0 : x0 ∈ KX) (hy0 : y0 ∈ KY)  :
    compacto (KX ×ˢ KY)  ↔ compacto KX ∧ compacto KY := by
  fconstructor
  · intro h
    fconstructor
    · have haux : KX = π₁ '' (KX ×ˢ KY)
      · ext x
        simp only [mem_image, mem_prod, simp_proj_1, simp_proj_2, Prod.exists, proj_simp_1,
          Prod.snd_comp_mk, cancela_inver, exists_and_right, exists_and_left, exists_eq_right,
          iff_self_and]
        intro hx
        use y0
      rw [haux]
      apply imagen_compacto
      apply proyeccion_continua_1
      exact h
    · have haux : KY = π₂ '' (KX ×ˢ KY)
      · ext y
        simp only [mem_image, mem_prod, simp_proj_1, simp_proj_2, Prod.exists, proj_simp_1,
          Prod.snd_comp_mk, cancela_inver, exists_eq_right, exists_and_right, iff_and_self]
        intro hy
        use x0
      rw [haux]
      apply imagen_compacto
      apply proyeccion_continua_2
      apply h
  · intro h
    rw [compacto_producto_base]
    choose h1 h2 using h
    intro F hFab hFrec hFW
    choose! U V hU hV hUVW using hFW
    have hauxbuena : ∀ x ∈ KX, ∃ Sx ⊆ F, Set.Finite Sx ∧ recubrimiento ({x} ×ˢ KY) Sx ∧ ∀ w ∈ Sx, x ∈ U w
    · intro x hx
      let Wx := { v  | ∃ w ∈ F, v = V w ∧ x ∈ U w}
      specialize h2 Wx ?_ ?_
      · intro w hw
        choose a b c d using hw
        rw [c]
        exact hV a b
      · intro y hy
        have hxy : (x,y) ∈ KX ×ˢ KY
        · exact ⟨hx,hy⟩
        rw [def_recubrimiento] at hFrec
        specialize hFrec hxy
        choose fxy hfxyF hxyfxy using hFrec
        use V fxy
        fconstructor
        · use fxy
          simp only [hfxyF, true_and]
          specialize hUVW fxy hfxyF
          rw [hUVW] at hxyfxy
          apply hxyfxy.1
        · specialize hUVW fxy hfxyF
          rw [hUVW] at hxyfxy
          apply hxyfxy.2
      choose Sx hSxF hSXfin hSxS using h2
      have hg : ∀ v ∈ Sx, ∃ w ∈ F, v = V w ∧ x ∈ U w
      · intro v hv
        apply hSxF
        exact hv
      choose! g hg1 hg2 hg3 using hg
      use g '' Sx
      fconstructor
      · intro w hw
        choose a ha ha2 using hw
        rw [← ha2]
        apply hg1
        apply ha
      fconstructor
      · apply Finite.image
        exact hSXfin
      fconstructor
      intro (x',y) hz
      simp only [singleton_prod, mem_image, Prod.mk.injEq, exists_eq_right_right] at hz
      specialize hSxS hz.1
      choose v hv using hSxS
      use g v
      fconstructor
      · use v
        simp only [hv.1, and_self]
      · rw [← hz.2]
        specialize hg1 v hv.1
        rw [hUVW _ hg1]
        fconstructor
        · simp only
          apply hg3
          exact hv.1
        · simp only
          rw [← hg2]
          exact hv.2
          exact hv.1
      intro w hw
      choose a ha ha2 using hw
      rw [← ha2]
      apply hg3
      exact ha

    choose! Wx hWxF hWxFin hWcrec hWxx using hauxbuena
    have haux2 : ∀ x ∈ KX, ∃ Ux ∈ abiertos, x ∈ Ux ∧ ∀ w ∈ Wx x, Ux ⊆ U w
    · intro x hx
      use ⋂₀ (U '' (Wx x))
      fconstructor
      · apply interseccion_finita_abiertos
        apply Finite.image
        apply hWxFin
        exact hx
        intro u hu
        choose a ha1 ha2 using hu
        rw [← ha2]
        apply hU
        specialize hWxF x hx
        apply hWxF
        apply ha1
      fconstructor
      · intro u hu
        choose w hw1 hw2 using hu
        rw [← hw2]
        apply hWxx
        exact hx
        exact hw1
      · intro w hw x' hx'
        specialize hx' (U w)
        apply hx'
        use w
    choose! Ux hUxab hxUx hUxw using haux2
    specialize h1 (Ux '' KX) ?_ ?_
    · intro UX hUX
      choose a ha ha2 using hUX
      rw [← ha2]
      apply hUxab
      exact ha
    · intro p xp
      use Ux p
      fconstructor
      · use p
      · apply hxUx
        exact xp
    choose Sx hSx hSxfin hSxrec using h1
    have hg : ∀ SX ∈ Sx, ∃ p ∈ KX,  Ux p = SX
    · intro SX hSX
      specialize hSx hSX
      exact hSx
    choose! g hg1 hg2  using hg
    use ⋃₀ (Wx '' (g '' Sx))
    fconstructor
    · intro a ha
      choose b hb hb2 using ha
      simp only [mem_image, exists_exists_and_eq_and] at hb
      choose y hy hy2 using hb
      rw [← hy2] at hb2
      specialize hWxF (g y) ?_ hb2
      apply hg1
      exact hy
      exact hWxF
    fconstructor
    · apply Set.Finite.sUnion
      apply Set.Finite.image
      apply Set.Finite.image
      exact hSxfin
      intro t ht
      choose a ha ha2 using ht
      rw [← ha2]
      apply hWxFin
      choose b hb1 hb2 using ha
      rw [← hb2]
      exact hg1 b hb1
    intro (x,y) hxy
    choose hx hy using hxy
    simp only at hx hy
    specialize hSxrec  hx
    choose SX hSX hxSX using hSxrec
    specialize hSx hSX
    choose U1 hU1 hU2 using hSx
    rw [← hU2] at hxSX
    specialize hg1 SX hSX
    specialize hWcrec (g SX) hg1 ?_
    · exact ((g SX),y)
    · fconstructor
      simp only [mem_singleton_iff]
      exact hy
    choose T hT1 hT2  using hWcrec
    use T
    fconstructor
    · use Wx (g SX)
      fconstructor
      · use g SX
        simp only [mem_image, and_true]
        use SX
      · exact hT1
    specialize hWxF _ hg1 hT1
    specialize hUVW _ hWxF
    rw [hUVW] at hT2 ⊢
    fconstructor
    · specialize hUxw (g SX) hg1 T hT1
      rw [hU2] at hxSX

      simp only
      apply hUxw
      rw [hg2]
      exact hxSX
      exact hSX
    · exact hT2.2
    exact x0
    exact y0
    exact hx0
    exact hy0

NewTheorem topo.producto_compacto topo.compacto_acumulacion

/--
Si `K` es un conjunto compacto en un espacio `X` con
una relación de equivalencia `R`, la imagen de
`K` en `X /' R` es compacto.
-/
TheoremDoc topo.cociente_compacto as "cociente_compacto" in "Compacidad"

Statement cociente_compacto [R : Equiv X] (K : Set X) (h : compacto K) : compacto ((π '' K) : Set (X /' R)) := by
  Hint (hidden := true) "Puedes aplicar que la imagen continua
  de un compacto es compacto."
  apply imagen_compacto
  Hint (hidden := true) "Puedes aplicar que la aplicación
  cociente es continua."
  apply cociente_continua
  exact h

end topo
