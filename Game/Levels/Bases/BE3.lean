import Game.Levels.Bases.BE2

World "Bases"
Level 9
Title "En la intersección de dos entornos básicos cabe otro entorno básico."

Introduction "Una nueva propiedad de las bases de entornos: en la intersección de dos
entornos básicos cabe otro entorno básico."
namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]


/--
Si `ℬ x` es una base de entornos de un punto, entonces `∀ N1 ∈ ℬ x , ∀ N2 ∈ ℬ x,   ∃ N3 ∈ (ℬ x), N3 ⊆ N1 ∩ N2 `.
-/
TheoremDoc topo.BE3 as "BE3" in "Bases"

Statement BE3 {ℬ : X → Set (Set X)} (hℬ : ∀ x : X, base_de_entornos x (ℬ x) ) (x : X) :
    ∀ N1 ∈ ℬ x , ∀ N2 ∈ ℬ x,   ∃ N3 ∈ (ℬ x), N3 ⊆ N1 ∩ N2 := by
  Hint (hidden := true) "Como queremos demostrar que algo
  se cumple para elementos cualesquiera de `{ℬ} {x}`, habrá que introducir los
  objetos arbitrarios y sus propiedades."
  intro N1 hN1 N2 hN2
  Hint (hidden := true) "Podemos obtener una nueva hipótesis sobre `{x}`
  gracias a `{hℬ}`."
  have hx := hℬ x
  Hint (hidden := true) "Puede ser buen momento para reescribir lo que significa ser
  base de entornos de `{x}`."
  rw [def_base_de_entornos] at hx
  Hint (hidden := true) "Puedes separar `{x}` en dos hipótesis con `cases'`
  o `choose`."
  cases' hx with h1 h2
  Hint (hidden := true) "¿Ves si puedes aplicar alguna hipótesis ahora?"
  apply h2
  Hint (hidden := true) "Hay otra hipótesis que implica lo que buscas."
  apply entornos_N3
  · apply h1
    exact hN1
  · apply h1
    exact hN2

end topo
