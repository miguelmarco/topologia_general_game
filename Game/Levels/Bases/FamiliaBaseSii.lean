import Game.Levels.Bases.InterseccionElementosBase

open espacio_topologico Set


World "Bases"
Level 4
Title "Cuándo una familia de abiertos es una base."

Introduction "Ahora vamos a ver un criterio para determinar que una familia de abiertos es una base.
"

variable {X : Type} [espacio_topologico X] (B : Set (Set X)) (hB : base B)

/--
Dada una base $𝓑$, y una familia de abiertos $𝓑'$, $𝓑'$ es base si y sólo sí
$∀ B ∈  𝓑, ∀ x ∈ B, ∃ B' ∈ 𝓑', x ∈ B' ⊆ B$.
-/
TheoremDoc criterio_familia_abiertos_base as "criterio_familia_abiertos_base" in "Espacios Topológicos."

Statement criterio_familia_abiertos_base (B' : Set (Set X)) (hB' : B' ⊆ abiertos) :
    base B' ↔ ∀ U ∈ B, ∀ x ∈ U, ∃ U' ∈ B', x ∈ U' ∧ U' ⊆ U := by
  Hint (hidden := true) "Separa la doble implicación con dos implicaciones con `fconstructor`."
  fconstructor
  · intro h
    rw [caracterizacion_base] at h hB
    choose h1 h2 using h
    choose hB1 hB2 using hB
    intro U hU
    apply h2
    apply hB1
    exact hU
  · intro h
    rw [caracterizacion_base]
    fconstructor
    · exact hB'
    · intro U hU x hx
      rw [caracterizacion_base] at hB
      choose hB1 hB2 using hB
      have h3 := hB2 U hU x hx
      choose V hVB hxV hVU using h3
      have h4 := h V hVB x hxV
      choose U' hU'B' hxU' hU'V using h4
      use U'
      fconstructor
      · exact hU'B'
      fconstructor
      · exact hxU'
      · intro y hy
        apply hVU
        apply hU'V
        exact hy
