import Game.Levels.Conexion.ConexionAbiertosCerrados

World "Conexión"
Level 3
Title "Conexión en términos de fronteras"

namespace topo
open topo Set espacio_topologico

variable (X : Type) [espacio_topologico X]


/--
Un espacio topológico es conexo si y sólo si la frontera de todo subconjunto
propio es no vacía.
-/
TheoremDoc topo.conexo_sii_frontera as "conexo_sii_frontera" in "Conexión"



Statement conexo_sii_frontera : conexo X ↔ ∀ (M : Set X), M ≠ ∅ → M ≠ univ →  frontera M ≠ ∅ := by
  fconstructor
  intro h
  intro M
  intro h1 h2 hM
  rw [frontera_inter_clausura_compl] at hM
  rw [caracterizacion_conexo_cerrados] at h
  apply h
  use clausura Mᶜ
  use clausura M
  fconstructor
  · apply clausura_cerrado
  fconstructor
  · apply clausura_cerrado
  fconstructor
  · intro hneg
    apply h2
    have haux : Mᶜ =  ∅
    · have haux2 := clausura_contiene Mᶜ
      rw [hneg] at haux2
      ext x
      fconstructor
      · apply haux2
      simp
    simp at haux
    exact haux
  fconstructor
  · intro hn
    apply h1
    ext x
    fconstructor
    rw [← hn]
    apply clausura_contiene
    simp
  fconstructor
  exact hM
  ext x
  simp
  by_cases hcas :x ∈ clausura M
  · right
    exact hcas
  · left
    have haux : x ∈ Mᶜ
    · intro hx
      apply hcas
      apply clausura_contiene
      exact hx
    apply clausura_contiene
    apply haux
  intro h
  rw [conexo_sii_abiertos_cerrados]
  ext U
  fconstructor
  intro hU
  specialize h U
  by_contra hneg
  apply h
  intro hn
  apply hneg
  left
  exact hn
  intro hn
  apply hneg
  right
  exact hn
  rw [frontera_compl_int_ext]
  simp
  ext x
  simp
  intro hx
  cases' hU with hUa hUc
  rw [abierto_sii_interior] at hUa
  rw  [hUa] at hx
  rw [def_exterior]
  rw [def_cerrado] at hUc
  rw [abierto_sii_interior] at hUc
  rw [hUc]
  exact hx
  intro hU
  simp at hU
  cases hU
  fconstructor
  rw [h_1]
  apply abierto_vacio
  rw [h_1]
  apply cerrado_vacio
  rw [h_1]
  fconstructor
  apply abierto_total
  apply cerrado_total


end topo
