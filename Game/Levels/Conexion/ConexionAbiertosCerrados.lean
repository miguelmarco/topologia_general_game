import Game.Levels.Conexion.Conexion

World "Conexión"
Level 2
Title "Conexión en términos de abiertos-cerrados"

namespace topo
open topo Set espacio_topologico

variable (X : Type) [espacio_topologico X]


/--
Un espacio topológico es conexo si y sólo si no existen abiertos
cerrados no triviales.
-/
TheoremDoc topo.conexo_sii_abiertos_cerrados as "conexo_sii_abiertos_cerrados" in "Conexión"

Statement conexo_sii_abiertos_cerrados : conexo X ↔ abiertos ∩ (cerrados : Set (Set X)) = {∅ , univ} := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente como una hipótesis con `intro`."
    intro h
    Hint (hidden := true) "Para demostrar la igualdad de dos conjuntos,
    usa el principio de extensionalidad con `ext`."
    ext U
    Hint (hidden := true) "Puedes reescribir la definición de conexo
    en `{h}`."
    rw [def_conexo] at h
    Hint (hidden := true) "Puedes dividir el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Introduce el antecedente como una hipótesis con `intro`."
      intro hU
      Hint (hidden := true) "Gracias a `{hU}`, puedes obtener que `{U}` es abierto
      y cerrado con `choose`."
      choose hUab hUcer using hU
      Hint (hidden := true) "Ahora puedes intentar una demostración por reducción
      al absurdo con `by_contra`."
      by_contra hneg
      Hint (hidden := true) "La contradicción vendrá de aplicar `{h}`."
      apply h
      Hint (hidden := true) "Ahora, ¿qué abierto puedes usar?"
      use U
      Hint (hidden := true) "El otro abierto, deberá ser por necesidad
      el complemento de `{U}`."
      use Uᶜ
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · exact hUab
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · exact hUcer
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · tauto
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Prueba a simplificar"
        simp only [ne_eq, compl_empty_iff]
        Hint (hidden := true) "Como quieres demostrar una negación, prueba
        a suponer la afirmación con `intro` para pasar a demostrar una contradicción."
        intro hU
        Hint (hidden := true) "La contradicción vendrá de aplicar `{hneg}`.g"
        apply hneg
        Hint (hidden := true) "Puedes usar `{hU}` para reescribir el objetivo."
        rw [hU]
        Hint (hidden := true) "Esto es tautológicamente cierto."
        tauto
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Basta con simplificar la expresión."
        simp only [inter_compl_self]
      Hint (hidden := true) "Basta con simplificar la expresión."
      simp only [union_compl_self]
    · Hint (hidden := true) "Introduce el antecedente con `intro`."
      intro hU
      Hint (hidden := true) "Puedes separar en los dos posibles casos
      de `{hU}` con `cases'`."
      cases' hU with hU hU
      · Hint (hidden := true) "Puedes reescribir el objetivo gracias a `{hU}`."
        rw [hU]
        fconstructor
        · exact abierto_vacio
        · simp [def_cerrado]
          exact abierto_total
      · rw [hU]
        fconstructor
        · exact abierto_total
        · simp [def_cerrado]
          exact abierto_vacio
  · intro h
    intro cas
    choose A B hAab hBab hAo hBo hABo hAB using cas
    have hAcer : A ∈ abiertos ∩ cerrados
    · fconstructor
      exact hAab
      rw [def_cerrado]
      have haux : Aᶜ = B
      · ext x
        simp only [mem_compl_iff]
        fconstructor
        · intro hxa
          have hxaux : x ∈ A ∪ B
          · rw [hAB]
            trivial
          cases' hxaux with hx1 hx1
          · tauto
          · exact hx1
        · intro hxb
          intro hxa
          have haux : x ∈ A ∩ B
          · tauto
          rw [hABo] at haux
          exact haux
      · rw [haux]
        exact hBab
    · rw [h] at hAcer
      simp only [mem_insert_iff, mem_singleton_iff] at hAcer
      cases' hAcer with hAc hAc
      · tauto
      · rw [hAc] at hABo
        simp only [univ_inter] at hABo
        tauto

end topo
