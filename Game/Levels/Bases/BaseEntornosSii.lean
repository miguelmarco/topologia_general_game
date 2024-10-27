import Game.Levels.Bases.BasesEntornosBase

open espacio_topologico Set


World "Bases"
Level 6
Title "Una base de entornos dada otra."

Introduction "Ahora vamos a ver que, si tenemos una familia $𝒟$ de entornos de un punto y
queremos comprobar si es una base de entornos, no hace falta comprobar la propiedad
de las bases de entornos para todo entorno del punto: basta hacerlo para los entornos
de otra base de entornos $ℬ$ dada.

Recuerda que puedes introducir $ℬ$ y $𝒟$ con `\\McB` y `\\McD` respectivamente.
"

variable {X : Type} [espacio_topologico X]





/--
Dado un punto $x$ y una base de entornos $ℬ$, una familia $𝒟$ de entornos de $x$ es base
de entornos de $x$ si y solo si $∀ B ∈ ℬ, ∃ D ∈ 𝒟, D ⊆ B$.
-/
TheoremDoc familia_entornos_base_sii as "familia_entornos_base_sii" in "Espacios Topológicos"

Statement familia_entornos_base_sii  (x : X) (ℬ 𝒟 : Set (Set X)) (hℬ : base_de_entornos x ℬ) (h𝒟 : 𝒟 ⊆ entorno x) :
    base_de_entornos x 𝒟 ↔ ∀ B ∈ ℬ, ∃ D ∈ 𝒟, D ⊆ B := by
  fconstructor
  · intro h
    intro B hB
    choose h1 h2 using h
    choose h3 h4 using hℬ
    apply h2
    apply h3
    exact hB
  · intro h
    fconstructor
    · exact h𝒟
    · intro N hN
      choose h1 h2 using hℬ
      have h3 := h2 N hN
      choose B hB hB2 using h3
      have h4 := h B hB
      choose D hD1 hD2 using h4
      use D
      fconstructor
      · exact hD1
      · intro a ha
        apply hB2
        apply hD2
        exact ha
