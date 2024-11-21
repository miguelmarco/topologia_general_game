import Game.Levels.Continuidad.CompContinua


World "Continuidad"
Level 2
Title "Continuidad en términos de cerrados."

Introduction "Veamos ahora que la continuidad de una función de puede caracterizar también en términos
de preimagenes de cerrados.
"
namespace topo
open topo espacio_topologico Set
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

/--
Dada una aplicación `f : X → Y` entre espacios topológicos, `continua_sii_cerrados f` dice
que `continua f ↔ ∀ U ∈ cerrados, f ⁻¹' U ∈ cerrados`.
-/
TheoremDoc topo.continua_sii_cerrados as "continua_sii_cerrados" in "Continuidad"

/--
Una aplicación es continua si y sólo si la preimagen de cualquier cerrado es un cerrado.
-/
Statement continua_sii_cerrados : continua f ↔ ∀ U ∈ cerrados, f ⁻¹' U ∈ cerrados := by
  Hint (hidden := true) "Habrá que separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes introducir el antecedente como una hipótesis
    con `intro`."
    intro h
    Hint (hidden := true) "Puedes tomar un cerrado arbitrario con `intro`."
    intro C hC
    Hint (hidden := true) "Puede ser útil reescribir la definición de cerrado en el objetivo
    y las hipótesis."
    rw [def_cerrado] at hC ⊢
    Hint (hidden := true) "También puedes reescribir la definición de continua."
    rw [def_continua] at h
    Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis particularizando
    `{h}` a `{C}ᶜ` y `{hC}`."
    have h2 := h _ hC
    Hint (hidden := true) "Puedes probar a simplificar `{h2}`."
    simp only [preimage_compl] at h2
    Hint (hidden := true) "Ahora el objetivo es exactamente igual a una hipótesis."
    exact h2
  · Hint (hidden := true) "Introduce el antecedente de la implicación que quieres
    probar como una hipótesis."
    intro h
    Hint (hidden := true) "Puedes reescribir la definición de continua."
    rw [def_continua]
    Hint (hidden := true) "Puedes tomar un abierto arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Para poder usar `{h}`, necesitarás ver que un cierto
    conjunto es cerrado. ¿Cual puede ser?  Recuerda que la táctica para introducir
    una nueva hipótesis probándola como nuevo objetivo es `have`."
    have hU' : Uᶜ ∈ cerrados
    · Hint (hidden := true) "Prueba a reescribir la definición de cerrado."
      rw [def_cerrado]
      Hint (hidden := true) "Necesitarás simplificar la expresión."
      simp only [compl_compl]
      Hint (hidden := true) "Ahora tu objetivo es exactamente una hipótesis."
      exact hU
    Hint (hidden := true) "Ya puedes obtener una nueva hipótesis usando `{h}`
    `{U}ᶜ` y `{hU'}`."
    have h2 := h Uᶜ hU'
    Hint (hidden := true) "Prueba a reescribir la definición de cerrado."
    rw [def_cerrado] at h2
    Hint (hidden := true) "Puede ser útil simplificar `{h2}`."
    simp only [preimage_compl, compl_compl] at h2
    exact h2

end topo
