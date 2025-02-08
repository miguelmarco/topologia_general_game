import Game.Levels.Cocientes.SaturadoAbierto
World "Cocientes"
Level 4
Title "Caracterización de proyección cerrada."

Introduction "
Veamos que `π` es cerrada si y solo si el saturado de todo cerrado es cerrada.
"



namespace topo
open topo espacio_topologico Set

variable {X : Type} [espacio_topologico X] [R : Equiv X]


/--
En un cociente, la proyección `π` es cerrada si y solo si el saturado
de todo cerrado es cerrado.
-/
TheoremDoc topo.caracterizacion_cerrada_cociente as "caracterizacion_cerrada_cociente" in "Cocientes"

Statement caracterizacion_cerrada_cociente : cerrada (π : X → (X /' R)) ↔ ∀ U ∈ cerrados, saturado U ∈ (cerrados : Set (Set X)) := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente y un cerrado arbitrario con
    `intro`."
    intro h
    intro C hC
    Hint (hidden := true) "Puede ser útil aplicar la caracterización del
    saturado para reescribir el objetivo."
    rw [caracterizacion_saturado]
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{h}` a `{C}` y `{hC}`."
    have h2 := h C hC
    Hint (hidden := true) "Puedes reescribir la definición de cerrado."
    rw [def_cerrado] at h2 ⊢
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    que diga que `π ⁻¹ ((π '' {C})ᶜ)` es un abierto. Al hacerlo, tendrás que
    pasar a demostrarla."
    have h3 : π ⁻¹' (π '' C)ᶜ ∈ abiertos
    · Hint (hidden := true) "Puedes aplicar el hecho de que la aplicación
      cociente es continua."
      apply cociente_continua
      exact h2
    Hint (hidden := true) "Observa que el objetivo es exactamente `{h3}`."
    exact h3
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h C hC
    Hint (hidden := true) "Puedes reescribir la caracterización de cerrados
    en el cociente."
    rw [caracterizacion_cerrado_cociente]
    Hint (hidden := true) "Puedes reescribir la caracterización del saturado."
    rw [← caracterizacion_saturado]
    Hint (hidden := true) "Prueba a aplicar `{h}`."
    apply h
    exact hC

end topo
