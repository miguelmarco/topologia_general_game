import Game.Levels.Cocientes.CaracterizacionCerrado
World "Cocientes"
Level 3
Title "Caracterización de proyección abierta."

Introduction "
Si `R` es una relación de equivalencia definida en `X`, y `A` es un
subconjunto de `X`, el **saturado** de `A` es el conjunto de los elementos
`x` tales que `y ≈ x` para algún `y` en `A`. El teorema `def_saturado` afirma
esta igualdad.

Este conjunto coincide con `π ⁻¹' (π '' A)`. El teorema `caracterizacion_saturado`
afirma esta igualdad.

Veamos que `π` es abierta si y solo si el saturado de todo abierto es abierto.
"



namespace topo
open topo espacio_topologico Set

variable {X : Type} [espacio_topologico X] [R : Equiv X]

def saturado (A : Set X) := {x | ∃ y ∈ A, y ≈ x}

theorem def_saturado (A : Set X) : saturado A = {x | ∃ y ∈ A, y ≈ x} := by rfl

theorem caracterizacion_saturado (A : Set X) : saturado A = π ⁻¹' (π '' A) := by
  simp only [def_saturado, preimage, def_π, mem_image, Quotient.eq]

/--
Si `A` es un conjunto en un espacio con una relación de equivalencia,
`def_saturado A` dice que `saturado A = {x | ∃ y ∈ A, y ≈ x}`.
-/
TheoremDoc topo.def_saturado as "def_saturado" in "Cocientes"

/--
Si `A` es un conjunto en un espacio con una relación de equivalencia,
`caracterizacion_saturado A` dice que `saturado A = π ⁻¹' (π '' A)`.
-/
TheoremDoc topo.caracterizacion_saturado as "caracterizacion_saturado" in "Cocientes"

NewTheorem topo.def_saturado topo.caracterizacion_saturado

/--
Si `A` es un conjunto en un espacio con una relación de equivalencia,
el **saturado** de `A` es el conjunto de los elementos que son equivalentes
a algún elemento de `A`.
-/
DefinitionDoc topo.saturado as "saturado"

NewDefinition topo.saturado

/--
En un cociente, la proyección `π` es abierta si y solo si el saturado
de todo abierto es abierto.
-/
TheoremDoc topo.caracterizacion_abierta_cociente as "caracterizacion_abierta_cociente" in "Cocientes"

Statement caracterizacion_abierta_cociente : abierta (π : X → (X /' R)) ↔ ∀ U ∈ abiertos, saturado U ∈ (abiertos : Set (Set X)) := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente y un abierto arbitrario con
    `intro`."
    intro h
    intro U hU
    Hint (hidden := true) "Puede ser útil aplicar la caracterización del
    saturado para reescribir el objetivo."
    rw [caracterizacion_saturado]
    Hint (hidden := true) "Podemos aplicar el hecho de que la proyección
    es continua."
    apply cociente_continua
    Hint (hidden := true) "Ahora podemos aplicar la hipótesis `{h}`."
    apply h
    exact hU
  · Hint (hidden := true) "Introduce el antecedente y un abierto
    arbitrario con `intro`."
    intro h
    intro U hU
    Hint (hidden := true) "Puedes reescribir la definición de abierto
    en un cociente."
    rw [def_abierto_cociente]
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{h}` a `{U}` y `{hU}`."
    have h2 := h U hU
    Hint (hidden := true) "Puedes reescribir `{h2}` usando la caracterizacón
    del saturado."
    rw [caracterizacion_saturado] at h2
    Hint (hidden := true) "Observa que el objetivo es realmente lo mismo
    que `{h2}`."
    exact h2


end topo
