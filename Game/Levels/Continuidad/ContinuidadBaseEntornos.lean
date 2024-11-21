import Game.Levels.Continuidad.ContinuidadBase

World "Continuidad"
Level 5
Title "Continuidad en términos de bases de entornos."

Introduction "Veamos ahora que, si tenemos una subbase de entornos
en el espacio de llegada, basta ver que se cumple la definición de
continuidad puntual para entornos básicos.
"
namespace topo
open topo espacio_topologico Set
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)


/--
Si `f : X → Y` es una aplicación entre espacios topológicos, y `x` un punto
de `X`, y  `B` una base de entornos de `f x`, `caracterizacion_continua_en_base` dice que
`continua_en f x ↔ ∀ N ∈ B, entorno x (f ⁻¹' U )`.
-/
TheoremDoc topo.caracterizacion_continua_en_base as "caracterizacion_continua_en_base" in "Continuidad"

Statement caracterizacion_continua_en_base (x : X) (B : Set (Set Y)) (hB : base_de_entornos (f x) B) :
    continua_en f x ↔ ∀ U  ∈ B, entorno x (f ⁻¹' U) := by
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes tomar un elemento arbitrario de `B`
    con `intro`."
    intro U hU
    Hint (hidden := true) "Puede ser un buen momento para reescribir la
    definición de continuidad."
    rw [def_continua_en] at h
    Hint (hidden := true) "Observa que `{h}` implica el objetivo,
    así que puedes aplicarla."
    apply h
    Hint (hidden := true) "Ahora necesitas usar que `{B}` es una base de entornos,
    tendrás que reescribir la definición de base."
    rw [def_base_de_entornos] at hB
    Hint (hidden := true) "Puedes obtener dos hipótesis a partir
    de `{hB}`usando `choose` o `cases'`."
    choose hB1 hB2 using hB
    Hint (hidden := true) "Observa que puedes aplicar `{hB1}`."
    apply hB1
    Hint (hidden := true) "Y ahora el objetivo es exactamente una de las hipótesis."
    exact hU
  · Hint (hidden := true) "Introduce el antecedente como hipótesis, con `intro`."
    intro h
    Hint (hidden := true) "Puede ser un buen momento para reescribir la definición
    de continuidad en un punto."
    rw [def_continua_en]
    Hint (hidden := true) "Puedes tomar un entorno arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Prueba a reescribir la definición de base de entornos."
    rw [def_base_de_entornos] at hB
    Hint (hidden := true) "Puedes obtener dos hipótesis de `{hB}` con `choose`
    o `cases'`."
    choose hB1 hB2 using hB
    Hint (hidden := true) "Observa que puedes obtener una nueva hipótesis
    (con `have`) si particularizas `{hB2}` a `{U}` y `{hU}`."
    have h2 := hB2 U hU
    Hint (hidden := true) "Como `{h2}` te asegura que existen ciertos
    elementos de `B`, puedes elegir uno (y sus propiedades) con `choose`."
    choose N hN1 hN2 using h2
    Hint (hidden := true) "Como tienes un elemento de `{B}`, puedes
    obtener una nueva hipótesis si particularizas `{h}` a `{N}` y `{hN1}`."
    have h3 := h  N hN1
    Hint (hidden := true) "Ahora puedes proceder 'a mano` (reescribiendo)
    la definición de entorno y trabajando con los abiertos), o recordar
    que hay una propiedad de los entornos que te permitirá demostrar el objetivo."
    Branch
      have h4 :=  entornos_N4 x (f ⁻¹' N) (f ⁻¹' U)
      Hint (hidden := true) "Ahora puedes aplicar `{h4}`."
      apply h4
      exact h3
      Hint (hidden := true) "Deberías tomar un elemento arbitrario del primer conjunto."
      intro z
      Hint (hidden := true) "Prueba a simplificar la expresión."
      simp only [mem_preimage]
      apply hN2
    rw [def_entorno] at h3 ⊢
    Hint (hidden := true) "Como `{h3}` te asegura que existen ciertos abiertos,
    puedes elegir uno con `choose`."
    choose V hV1 hV2 hV3 using h3
    Hint (hidden := true) "¿Qué abierto puedes usar? No tienes muchas opciones."
    use V
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · exact hV1
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hV2
    · Hint (hidden := true) "Deberías tomar un elemento arbitrario con `intro`."
      intro z hz
      Hint (hidden := true) "Puede ser útil simplificar objetivo."
      simp only [mem_preimage]
      Hint (hidden := true) "Observa que puedes aplicar `{hN2}`."
      apply hN2
      Hint (hidden := true) "Observa que puedes aplicar `{hV3}`."
      apply hV3
      exact hz

end topo
