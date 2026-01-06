import Game.Levels.Compacidad.CocienteCompacto

World "Compacidad"
Level 6
Title "Compacidad local"

Introduction "
Un espacio `X` se dice **localmente compacto** si cada punto tiene una
base de entornos compactos.
"

namespace topo
open espacio_topologico topo Set Set.Finite

def localmente_compacto (X : Type) [espacio_topologico X] :=
    ∀ (x : X), ∃ (F : Set (Set X )), (base_de_entornos x F ∧ (∀ K ∈ F, compacto K))

/--
Un espacio `X` se dice **localmente compacto** si cada punto tiene una
base de entornos compactos.
-/
DefinitionDoc topo.localmente_compacto as "localmente_compacto"

variable {X: Type}  [espacio_topologico X] [Nonempty X]

lemma inter_sInter (A B : Set X) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  simp only [mem_inter_iff, sInter_insert, sInter_singleton]

theorem def_localmente_compacto : localmente_compacto X ↔ ∀ (x : X), ∃ (F : Set (Set X )), (base_de_entornos x F ∧ (∀ K ∈ F, compacto K)) := by rfl

/--
Dado un espacio `X`, `def_localmente_compacto X` dice que
`localmente_compacto X ↔ ∀ (x : X), ∃ (F : Set (Set X )), (base_de_entornos x F ∧ (∀ K ∈ F, compacto K))`.
-/
TheoremDoc topo.def_localmente_compacto as "def_localmente_compacto" in "lemas-definición"

NewTheorem topo.def_localmente_compacto

NewDefinition topo.localmente_compacto


theorem T2_separa_punto_compacto (hT2 : T2 X) (x : X) (K : Set X) (hx : x ∉ K) (hK : compacto K) :
    ∃ U ∈ abiertos, x ∈ U ∧  clausura U ∩ K = ∅ := by
  have h1 : ∀ y ∈ K, ∃ (Uy Vy : Set X), Uy ∈ abiertos ∧ Vy ∈ abiertos ∧ Uy ∩ Vy = ∅ ∧ x ∈ Uy ∧ y ∈ Vy
  · intro y  hy
    apply hT2
    intro hxy
    apply hx
    rw [hxy]
    exact hy
  choose! f g hf1 hf2 hfg hg1 hg2 using h1
  let F := g '' K
  have hF1 : F ⊆ abiertos
  · intro U hU
    choose y hy1 hy2 using hU
    rw  [← hy2]
    apply hf2
    exact hy1
  have hF2 : recubrimiento K F
  · intro y hy
    use g y
    constructor
    · use y
    · apply hg2
      exact hy
  have h2 := hK F hF1 hF2
  choose S hS1 hS2 hS3 using h2
  simp [F] at hS1
  have haux : ∀ W ∈ S, ∃ y ∈ K,  g y = W
  · intro W hW
    specialize hS1 hW
    exact hS1
  choose! l hl1 hl2  using haux
  use ⋂₀ (f '' (l '' S))
  constructor
  · apply interseccion_finita_abiertos
    apply Finite.image
    apply Finite.image
    exact hS2
    intro A hA
    choose B hB hB2 using hA
    choose C hC hC2 using hB
    rw [← hB2,← hC2]
    apply hf1
    apply hl1
    exact hC
  constructor
  · intro A hA
    choose B hB hB2 using hA
    choose C hC hC2 using hB
    rw [← hB2,← hC2]
    apply hg1
    apply hl1
    exact hC
  · ext y
    simp only [sInter_image, mem_image, iInter_exists, biInter_and', iInter_iInter_eq_right,
      mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hy
    rw [caracterizacion_clausura] at hy
    intro hyK
    specialize hS3  hyK
    choose V hV1 hV2 using hS3
    specialize hl1 V hV1
    specialize hl2 V hV1
    specialize hy V ?_ hV2
    · rw [← hl2]
      exact hf2 (l V) hl1
    choose z hzV hz2 using hy
    simp only [mem_iInter] at hz2
    specialize hz2 V hV1
    rw [← hl2 ] at hzV
    specialize hfg _ hl1
    suffices : z ∈ (∅ : Set X)
    · exact this
    rw [← hfg]
    tauto




theorem localmente_compacto_T2 (hT2 : T2 X) : localmente_compacto X ↔ ∀ x, ∃ (K : Set X), entorno x K ∧ compacto K := by
  fconstructor
  · intro h
    intro x
    have hx := h x
    choose F hF1 hF2 using hx
    choose hFent hF1 using hF1
    have htot := hF1 univ
    have haux : entorno x univ
    · use univ
      fconstructor
      exact abierto_total
      trivial
    have haux2 := htot haux
    choose B hB1 _ using haux2
    use B
    fconstructor
    · apply hFent
      exact hB1
    · apply hF2
      exact hB1
  · intro h
    intro x
    specialize h x
    choose K hxK jKcomp using h
    choose U hxU hUab using hxK
    use clausura '' { V | x ∈ V ∧ V ∈ abiertos ∧ V ⊆ U}
    fconstructor
    fconstructor
    · intro C hC
      choose V hV hV2 using hC
      simp only [mem_setOf_eq] at hV
      use V
      fconstructor
      · exact hV.2.1
      fconstructor
      · exact hV.1
      · rw [← hV2]
        apply clausura_contiene
    · intro N hN
      choose W hWab hxW hWN using hN
      have haux := T2_separa_punto_compacto hT2 x (K \ (U ∩ W)) ?_ ?_
      choose V hV1 hV2 hV3 using haux
      use clausura (V ∩ U)
      constructor
      · use (V ∩ U)
        simp only [mem_setOf_eq, mem_inter_iff, hV2, hUab, and_self, inter_subset_right, and_true,
          true_and]
        apply interseccion_abiertos
        exact hV1
        exact hxU
      intro y hy
      apply hWN
      by_contra hneg
      have h1 : y ∈ clausura V
      . apply clausura_subconjunto _ _ _ hy
        simp only [inter_subset_left]
      have h2 : y ∈ K \ (U ∩ W)
      · simp only [mem_diff, mem_inter_iff, not_and]
        constructor
        · have haux : V ∩ U ⊆ K
          · intro z hz
            apply hUab.2 hz.2
          apply clausura_contenida_cerrado (V ∩ U)
          apply compacto_t2_cerrado hT2 jKcomp
          exact haux
          exact hy
        · intro
          exact hneg
      change y ∈ (∅ : Set X)
      rw [← hV3]
      tauto
      simp only [mem_diff, mem_inter_iff, not_and, not_forall, not_not, exists_prop]
      tauto
      apply cerrado_compacto K
      exact jKcomp
      have haux : K \ (U ∩ W) = K ∩ (U ∩ W)ᶜ
      · ext y
        simp only [mem_diff, mem_inter_iff, not_and, mem_compl_iff]
      rw [haux,def_cerrado,compl_inter]
      rw [← sUnion_pair]
      apply union_abiertos
      simp only [compl_involutive, Function.Involutive.comp_self, cancela_inver]
      intro A hA
      simp only [mem_insert_iff, mem_singleton_iff] at hA
      cases hA
      · rw [h,← def_cerrado]
        apply compacto_t2_cerrado hT2 jKcomp
      · rw [h]
        apply interseccion_abiertos
        exact hxU
        exact hWab
      intro y
      simp only [mem_diff, mem_inter_iff, not_and, and_imp]
      tauto
    intro C hC
    choose V hV1 hV2 using hC
    simp only [mem_setOf_eq] at hV1
    apply cerrado_compacto K
    exact jKcomp
    rw [← hV2]
    apply clausura_cerrado
    rw [← hV2]
    apply clausura_contenida_cerrado
    apply compacto_t2_cerrado hT2 jKcomp
    apply subset_trans hV1.2.2 hUab.2

/--
Si `X` es un espacio `T2`, `X` es localmente compacto si y solo si cada punto tiene un entorno compacto.
-/
TheoremDoc topo.localmente_compacto_T2 as "localmente_compaacto_T2" in "Compacidad"


inductive compactificacion (X : Type)
| punto (x : X) : compactificacion X
| ω : compactificacion X

open compactificacion Function



instance alexandroff (h1 : T2 X) (h2 : localmente_compacto X) : espacio_topologico (compactificacion X) where
  abiertos := { ((punto '' U) : Set (compactificacion X)) | U  ∈ (abiertos :Set (Set X)) } ∪ { U | compacto (punto ⁻¹' U)ᶜ}
  abierto_vacio := by
    left
    use ∅
    simp only [image_empty, and_true]
    exact abierto_vacio
  abierto_total := by
    right
    simp only [mem_setOf_eq, preimage_univ, compl_univ]
    intro F _ _
    use ∅
    simp only [empty_subset, finite_empty, true_and]
    intro x hx
    cases hx
  union_abiertos := by
    intro F hF
    let A := { x ∈ F | ∃ U ∈ abiertos, punto '' U = x}
    let B := { x ∈ F | compacto (punto ⁻¹' x)ᶜ}
    have hA : ⋃₀ A ∈ {x | ∃ U ∈ abiertos, punto '' U = x}
    · use ⋃₀ {U | punto '' U ∈ A}
      fconstructor
      · apply union_abiertos
        intro U hU
        simp [A] at hU
        choose _ hU2 using hU
        choose U_1 hU_1 hU_2 using hU2
        have hUU : U_1 = U
        ext x
        fconstructor
        · intro hx
          have hauxx : punto x ∈ punto '' U_1
          · use x
          rw [hU_2] at hauxx
          simp at hauxx
          exact hauxx
        · intro hx
          have hauxx : punto x ∈ punto '' U
          · use x
          rw [<- hU_2] at hauxx
          simp at hauxx
          exact hauxx
        cases hUU
        exact hU_1
      ext x
      simp only [mem_image, mem_sUnion, mem_setOf_eq]
      aesop
    have hB : (∃ b, b ∈ B) → ⋃₀ B ∈ {U | compacto (punto ⁻¹' U)ᶜ}
    · intro hcas
      choose b hb using hcas
      simp only [mem_setOf_eq]
      choose hb1 hb2 using hb
      apply cerrado_compacto _ _ hb2
      rw [def_cerrado,compl_compl]
      have haux : punto ⁻¹' (⋃₀ B) = ⋃₀ {punto ⁻¹' U | U ∈ B}
      · ext
        simp only [preimage_sUnion, mem_iUnion, mem_preimage, exists_prop, mem_sUnion, mem_setOf_eq,
          exists_exists_and_eq_and]
      rw [haux]
      apply union_abiertos
      intro U hU
      simp only [mem_setOf_eq] at hU
      choose U1 hU1B hU1U using hU
      choose h11 _ using hU1B
      specialize hF h11
      cases hF
      · choose V hVab hVU using h
        rw [← hU1U, ← hVU]
        have haux2 : punto ⁻¹' (punto '' V) = V
        · ext t
          simp only [mem_preimage, mem_image, punto.injEq, exists_eq_right]
        rw [haux2]
        exact hVab
      · simp only [mem_setOf_eq] at h
        rw [← hU1U]
        have haux := compacto_t2_cerrado h1 h
        simp only [def_cerrado, compl_involutive, Involutive.comp_self, cancela_inver] at haux
        exact haux
      intro x
      simp only [preimage_sUnion, compl_iUnion, mem_iInter, mem_compl_iff, mem_preimage]
      intro hx
      apply hx
      fconstructor
      · exact hb1
      · exact hb2
    have hFAB : F = A ∪ B
    · ext U
      aesop
      save
    save
    by_cases hbB : ∃ b, b ∈ B
    · right
      rw [hFAB]
      rw [sUnion_union]
      specialize hB hbB
      apply cerrado_compacto _ _ hB
      · rw [preimage_union,compl_union]
        rw [inter_sInter]
        apply cerrado_interseccion
        intro U hU
        simp only [mem_insert_iff, mem_singleton_iff] at hU
        cases hU
        · rw [h]
          rw [def_cerrado,compl_compl]
          choose U hU hU2 using hA
          rw [← hU2]
          have hUU : punto ⁻¹' (punto '' U) = U
          · ext x
            simp only [mem_preimage, mem_image, punto.injEq, exists_eq_right]
          rw [hUU]
          exact hU
        · rw [h]
          apply compacto_t2_cerrado h1
          apply hB
      intro x
      simp only [preimage_union, preimage_sUnion, compl_union, compl_iUnion, mem_inter_iff,
        mem_iInter, mem_compl_iff, mem_preimage, and_imp, imp_self, implies_true]
    · save
      left
      have hBempt : B = ∅
      · ext x
        simp only [mem_empty_iff_false, iff_false]
        intro hx
        apply hbB
        use x
      rw [hFAB,hBempt,union_empty]
      exact hA
  interseccion_abiertos := by
    intro A B  hA hB
    cases' hA with hA hA
    · choose U hU hUA using hA
      cases' hB with hB hB
      · left
        choose V hV hVB using hB
        rw [←hUA, ← hVB]
        use U ∩  V
        fconstructor
        · apply interseccion_abiertos
          exact hU
          exact hV
        · ext x
          aesop
          save
      · left
        use U ∩ (punto ⁻¹' B)
        fconstructor
        · apply interseccion_abiertos
          exact hU
          have haux : (punto ⁻¹' B)ᶜ ∈ cerrados
          · apply compacto_t2_cerrado
            exact h1
            exact hB
          rw [def_cerrado,compl_compl] at haux
          exact haux
        simp [← hUA]
        ext x
        aesop
        save
    · cases' hB with hB hB
      · left
        choose V hV hVB using hB
        use (punto ⁻¹' A) ∩ V
        fconstructor
        · apply interseccion_abiertos
          · have haux : (punto ⁻¹' A)ᶜ   ∈ cerrados
            · apply compacto_t2_cerrado
              exact h1
              exact hA
            rw [def_cerrado, compl_compl] at haux
            exact haux
          · exact hV
        · rw [← hVB]
          ext x
          aesop
          save
      · right
        have haux1 : punto ⁻¹' (A ∩ B) = punto ⁻¹' A ∩ punto ⁻¹' B
        · ext x
          aesop
        save
        simp only [mem_setOf_eq, haux1]
        rw [compl_inter]
        apply union_compactos
        exact hA
        exact hB

theorem compactificacion_t2 (h1 : T2 X) (h2 : localmente_compacto X) : @T2  (compactificacion X) (alexandroff  h1 h2):= by
  intro x y hxy
  cases' x with x x
  · cases' y with y y
    have hxyd : x ≠ y
    · intro h
      apply hxy
      rw [h]
    have haux := h1 x y hxyd
    choose U V hU hV hUV hxU hyV using haux
    use punto '' U
    use punto '' V
    fconstructor
    · left
      use U
    fconstructor
    · left
      use V
    fconstructor
    · ext p
      simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false, not_and, not_exists,
        forall_exists_index, and_imp]
      intro q hq hqp y hy hyp
      rw [← hyp] at hqp
      simp only [punto.injEq] at hqp
      have haux : q ∈ U ∩ V
      · fconstructor
        exact hq
        rw [hqp]
        exact hy
      rw [hUV] at haux
      exact haux
    fconstructor
    · use x
    · use y
    rw [localmente_compacto_T2 h1 ] at h2
    have haux := h2 x
    choose K hK hxK using haux
    choose U hU  hxU hUK using hK
    use punto '' U
    use (punto '' K)ᶜ 
    fconstructor
    left
    use U
    fconstructor
    right
    simp only [mem_setOf_eq, preimage_compl, compl_involutive, Involutive.comp_self, cancela_inver]
    have haux : punto ⁻¹' (punto '' K) = K
    · ext
      simp only [mem_preimage, mem_image, punto.injEq, exists_eq_right] 
    rw [haux]
    exact hxK
    fconstructor
    ext p
    simp only [mem_inter_iff, mem_image, mem_compl_iff, not_exists, not_and, mem_empty_iff_false,
      iff_false, not_forall, not_not, exists_prop, forall_exists_index, and_imp]
    aesop
    fconstructor
    use x
    simp only [mem_compl_iff, mem_image, and_false, exists_const, not_false_eq_true]
  · cases' y with y y
    rw [localmente_compacto_T2 h1] at h2
    have hK := h2 y
    choose K hyK hK using hK
    choose U hU hyU hUK using hyK
    use (punto '' K)ᶜ 
    use punto '' U
    fconstructor
    · right
      simp only [mem_setOf_eq, preimage_compl,compl_compl]
      have haux : punto ⁻¹' (punto '' K) = K
      · ext
        simp only [mem_preimage, mem_image, punto.injEq, exists_eq_right] 
      rw [haux]
      exact hK
    fconstructor
    · left
      use U
    fconstructor
    · ext p
      simp only [mem_inter_iff, mem_compl_iff, mem_image, not_exists, not_and, mem_empty_iff_false,
        iff_false]
      aesop
      save
    fconstructor
    intro ho
    choose q hq  hq2 using ho
    cases hq2
    use y
    simp only [ne_eq, not_true_eq_false] at hxy


end topo
