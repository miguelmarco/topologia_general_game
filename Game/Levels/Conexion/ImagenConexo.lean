import Game.Levels.Conexion.ConexionFrontera
import Mathlib.Data.Set.Subset

World "Conexión"
Level 4
Title "Imagen continua de un conexo"

Introduction "En este nivel vamos a ver que la imagen continua
de un espacio conexo es conexo.

Recuerda que la imagen es un subconjunto del espacio de llegada,
por lo tanto, tenemos que usar la topología de subespacio.

Para trabajar con la conexión de subespacios, podemos
usar el lema `caracterizacion_subespacio_conexo`,
que premite reescribir la conexión de un subespacio (como
espacio topológico en sí mismo) en términos de lo que
ocurre en el espacio ambiente."

namespace topo
open topo Set espacio_topologico

variable (X : Type) [espacio_topologico X] (A : Set X)



open Set.Notation

instance subespacio : espacio_topologico ↥A where
  abiertos := { (A ↓∩  U) | U ∈ abiertos}
  abierto_vacio := by
    use ∅
    simp only [abierto_vacio,preimage_empty, and_true]
  abierto_total := by
    use univ
    simp only [abierto_total, preimage_univ, and_self]
  union_abiertos := by
    intro F hF
    use ⋃₀ { U ∈ abiertos | A ↓∩ U ∈ F}
    fconstructor
    · apply union_abiertos
      simp only [sep_subset]
    · ext x
      fconstructor
      · intro h
        simp only [preimage_sUnion, mem_setOf_eq, mem_iUnion, mem_preimage, exists_prop] at h
        choose U hU hU2 using h
        use A ↓∩ U
        simp only [mem_preimage]
        exact ⟨hU.2,hU2⟩
      · intro h
        choose U hUF hxU using h
        specialize hF  hUF
        choose V hV1 hV2 using hF
        -- simp only [preimage_sUnion, mem_setOf_eq, mem_iUnion, mem_preimage, exists_prop]
        use V
        fconstructor
        fconstructor
        · exact hV1
        · rw [hV2]
          exact hUF
        · rw [← hV2] at hxU
          exact hxU
  interseccion_abiertos := by
    intro U V hU hV
    choose UX hUX hUX2 using hU
    choose VX hVX hVX2 using hV
    use UX ∩ VX
    fconstructor
    · apply interseccion_abiertos
      exact hUX
      exact hVX
    · simp only [preimage_inter, hUX2, hVX2]

/--
Un dado un subconjunto `C` de un espacio topológico `X`,
`C` es conexo como subespacio si y solo si no hay dos abiertos
`A , B` en `X` que intersequen a `C`, y tales que su intersección en `C`
sea vacía y su unión llene `C`.
-/
TheoremDoc topo.caracterizacion_subespacio_conexo as "caracterizacion_subespacio_conexo" in "Conexión"

lemma caracterizacion_subespacio_conexo (C : Set X) : conexo C ↔ ¬ ∃ (A B : Set X), A ∈ abiertos ∧ B ∈ abiertos ∧
    A ∩ C ≠ ∅ ∧ B ∩ C ≠ ∅ ∧ A ∩ B ∩ C = ∅ ∧ C ⊆ A ∪ B := by
  fconstructor
  · intro h
    intro hneg
    apply h
    choose A B hA hB hAC hBC hABC hC using hneg
    use C ↓∩ A
    use C ↓∩ B
    fconstructor
    · use A
    fconstructor
    · use B
    fconstructor
    · simp at hAC ⊢
      choose y hyA hyC using hAC
      use y
    fconstructor
    · simp at hBC ⊢
      choose y hyB hyC using hBC
      use y
    fconstructor
    · ext ⟨y,hy⟩
      simp
      intro hyA
      intro hyB
      have haux : y ∈ A ∩ B ∩ C
      · trivial
      rw [hABC ] at haux
      exact haux
    ext y
    cases' y with y hy
    simp
    have h2 := hC hy
    exact h2
  · intro h
    intro hneg
    apply h
    choose A B hA hB hAo hBo hABp hABU using hneg
    choose AX hAXab hAX using hA
    choose BX hBXab hBX using hB
    use AX
    use BX
    fconstructor
    · exact hAXab
    fconstructor
    · exact hBXab
    fconstructor
    · rw [← hAX] at hAo
      simp at hAo
      simp
      choose a haC haX using hAo
      use a
    fconstructor
    · rw [← hBX] at hBo
      simp at hBo ⊢
      aesop
    fconstructor
    · ext y
      simp
      intro hyA hyB hyC
      have h1 : ⟨y,hyC⟩ ∈ A
      · rw [← hAX]
        simp [hyA]
      have h2 : ⟨y,hyC⟩ ∈ B
      · rw [← hBX]
        simp [hyB]
      have haux : ⟨y,hyC⟩ ∈ A ∩ B := ⟨h1,h2⟩
      rw [hABp] at haux
      exact haux
    · intro x hx
      have haux : ⟨x,hx⟩ ∈ A ∪ B
      · rw [hABU]
        trivial
      rw [← hAX,← hBX] at haux
      simp at haux
      exact haux


/--
Un espacio es conexo si y solo si lo es como subespacio de si mismo.
-/
TheoremDoc topo.caracterizacion_conexo_total as "caracterizacion_conexo_total" in "Conexion"

theorem caracterizacion_conexo_total : conexo X ↔ conexo (univ : Set X) := by
  rw [caracterizacion_subespacio_conexo]
  simp only [conexo, ne_eq, no_vacio, exists_and_left, not_exists, not_and, forall_exists_index,
    inter_univ, univ_subset_iff]

NewTheorem topo.caracterizacion_subespacio_conexo topo.caracterizacion_conexo_total


/--
La imagen continua de un conexo es conexo.
-/
TheoremDoc topo.imagen_conexo as "imagen_conexo" in "Conexión"

Statement imagen_conexo  {Y : Type} [espacio_topologico Y] (f : X → Y) (hf : continua f) (A : Set X) (hA : conexo A) :
    conexo (f '' A : Set Y) := by
  Hint (hidden := true) "Puedes reescribir la conexion de subespacios en terminos
  de la topologia ambiente."
  rw [caracterizacion_subespacio_conexo] at hA ⊢
  Hint (hidden := true) "Como tienes que demostrar que algo no es cierto,
  supon que lo es (con `intro`) y pasa a demostrar que hay una contradicción."
  intro hneg
  Hint (hidden := true) "Como `{hA}` te asegura que algo no es cierto,
  puedes aplicarlo, y asi demostrando que de hecho es cierto, habras probado
  la contradicción."
  apply hA
  Hint (hidden := true) "Gracias a `{hneg}` puedes elegir dos abiertos con sus propiedades."
  choose U V hU hV hUfA hVfA  hUVfA hfA using hneg
  Hint (hidden := true) "Ahora, el abierto que puedes usar es `{f} ⁻¹' {U}`."
  use f ⁻¹' U
  Hint (hidden := true) "Ahora, el abierto que puedes usar es `{f} ⁻¹' {V}`."
  use f ⁻¹' V
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Basta aplicar `{hf}`."
    apply hf
    exact hU
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Basta aplicar `{hf}`."
    apply hf
    exact hV
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes simplificar el objetivo y `{hUfA}`."
    simp at hUfA ⊢
    Hint (hidden := true) "Gracias a `{hUfA}`, puedes elegir puntos en `{U}` y en `{A}`."
    choose y hyU x hxA hxy using hUfA
    Hint (hidden := true) "Usa `{x}`."
    use x
    Hint (hidden := true) "Reescribe el objetivo con `{hxy}`."
    rw [hxy]
    tauto
  Hint (hidden := true) "Separa el pbjetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes simplificar el objetivo y `{hVfA}`."
    simp at hVfA ⊢
    Hint (hidden := true) "Gracias a `{hUfA}`, puedes elegir puntos en `{V}` y en `{A}`."
    choose y hyU x hxA hxy using hVfA
    Hint (hidden := true) "Usa `{x}`."
    use x
    Hint (hidden := true) "Usa `{hxy}` para reescribir el objetivo."
    rw [hxy]
    tauto
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Para ver la igualdad de conjuntos por extensionalidad,
    usa `ext`, para ver que un elemento pertenece a uno si y solo si peretenece al otro."
    ext x
    Hint (hidden := true) "Puedes simplificar el objetivo."
    simp
    Hint (hidden := true) "Introduce los antecedentes con `intro`."
    intro hfxU hfxV hxA
    Hint (hidden := true) "Ahora, para llegar a contradicción, tenemos que
    ver que `{f} {x}` está en `{U} ∩ {V} ∩ {f} '' {A}` (que sabemos que es vacío).
    Teclea `have haux : {f} {x} ∈ {U} ∩ {V} ∩ {f} '' {A}`."
    have haux : f x ∈ U ∩ V ∩ f '' A
    · Hint (hidden := true) "Puedes reescribir con `{hfxU}`y `{hfxV}` y simplificar."
      simp [hfxU,hfxV]
      Hint (hidden := true) "El punto que puedes usar es `{x}`."
      use x
    Hint (hidden := true) "Ahora puedes reescribir `{haux}` usando `{hUVfA}`."
    rw [hUVfA] at haux
    Hint (hidden := true) "Aplicando `{haux}` tienes la contradicción."
    apply haux
  Hint (hidden := true) "Puedes simplificar `{hfA}`."
  simp at hfA
  exact hfA

end topo
