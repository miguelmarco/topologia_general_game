import Game.Levels.Productos.ProductoBases
World "Cocientes"
Level 1
Title "Continuidad de la aplicación cociente"

Introduction "
Dado un espacio topológico `X` y una relación de equivalencia `R`
la aplicación `π : X → X /' R` es continua.
"



namespace topo
open topo espacio_topologico Set

abbrev Equiv := Setoid

variable {X : Type} [espacio_topologico X] [R : Equiv X]

notation3 G:35 " /' " H:35 => @Quotient G H

instance :  espacio_topologico (X /' R) where
  abiertos := { S | { x | ⟦x⟧ ∈ S} ∈ abiertos}
  abierto_vacio := by
    simp only [mem_setOf_eq, mem_empty_iff_false, setOf_false]
    exact abierto_vacio
  abierto_total := by
    simp only [mem_setOf_eq, mem_univ, setOf_true]
    exact abierto_total
  union_abiertos := by
    intro F hF
    simp only [mem_setOf_eq, mem_sUnion]
    have haux : {x | ∃ t ∈ F, ⟦x⟧ ∈ t} = ⋃₀ { {x | ⟦x⟧ ∈ U} | (U ∈ F)}
    · ext x
      simp only [mem_setOf_eq, mem_sUnion, exists_exists_and_eq_and]
    rw [haux]
    apply union_abiertos
    intro U hU
    simp only [mem_setOf_eq] at hU
    choose V hV hVU using hU
    specialize hF hV
    simp only [mem_setOf_eq] at hF
    rw [hVU] at hF
    exact hF
  interseccion_abiertos := by
    intro A B hA hB
    simp only [mem_setOf_eq, mem_inter_iff] at hA hB ⊢
    apply interseccion_abiertos
    · exact hA
    · exact hB

def π {X : Type} [R : Setoid X] : X → Quotient R := fun x ↦ ⟦x⟧


theorem def_abierto_cociente (U : Set (Quotient R)) : U ∈ abiertos ↔ {x | ⟦x⟧ ∈ U} ∈ abiertos :=  by rfl

theorem def_π (x : X) : ((π x) : (Quotient R)) = ⟦x⟧ := by rfl

theorem def_clase_equiv (x y : X) : (⟦x⟧  : Quotient R) = ⟦y⟧ ↔ x ≈ y := Quotient.eq

TheoremTab "Cocientes"

/--
Si `R` es una relación de equivalencia en un espacio topológico `X`,
y `U` es un conjunto en el cociente `X / R`, entonces
`U ∈ abiertos ↔ {x | ⟦x⟧ ∈ U} ∈ abiertos`.
-/
TheoremDoc topo.def_abierto_cociente as "def_abierto_cociente" in "Cocientes"

/--
Dado un punto `x`, de un espacio topológico `X` con una relación de equivalencia
`R`; si `π : X → (Quotient R)` es la proyección, entonces `π x = ⟦x⟧`.
-/
TheoremDoc topo.def_π as "def_π" in "Cocientes"

/--
Si `x` e `y` son elementos de un conjunto con una relación de equivalencia
`R`, `⟦x⟧ = ⟦y⟧ ↔  x ≈ y`.
-/
TheoremDoc topo.def_clase_equiv as "def_clase_equiv" in "Cocientes"

NewTheorem topo.def_abierto_cociente topo.def_π topo.def_clase_equiv

/--
Si `R` es una relación de equivalencia en un espacio topológico `X`,
la aplicación `π : X → (Quotient R)`.
-/
TheoremDoc topo.cociente_continua as "cociente_continua" in "Cocientes"

Statement cociente_continua : continua (π : X → (X /' R)) := by
  Hint (hidden := true) "Como para ver la continuidad de una función hay que
  tomar un abierto arbitrario, puedes hacerlo con `intro`."
  intro U hU
  Hint (hidden := true) "Observa que `{U}` es un abierto del espacio cociente,
  puedes reescribir `{hU}` usando la definición de los abiertos en el cociente."
  rw [def_abierto_cociente] at hU
  Hint (hidden := true) "Observa que, de hecho, por la definición de `π`,
  el objetivo es exactamente equivalente a `{hU}`."
  exact hU

end topo
