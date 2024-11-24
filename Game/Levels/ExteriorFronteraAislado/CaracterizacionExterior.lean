import Game.Levels.ExteriorFronteraAislado.ExteriorDisjuntoInterior
World "ExteriorFronteraAislado"
Level 4
Title "Caracterización de los puntos del exterior."

Introduction "Veamos que un punto está en el exterior de un conjunto
si y sólo si hay un abierto que contiene al punto, y es disjunto con
el conjunto.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`  en un espacio topológico, y `x`  un punto,
`caracterizacion_exterior A x` dice que `x ∈ exterior A ↔ ∃ U ∈ abiertos, x ∈ U ∧ U ∩ A = ∅`.
-/
TheoremDoc topo.caracterizacion_exterior as "caracterizacion_exterior" in "Exterior/Frontera/Aislado"


Statement caracterizacion_exterior (x : X) : x ∈ exterior A ↔ ∃ U ∈ abiertos, x ∈ U ∧ U ∩ A = ∅:= by
  Hint (hidden := true) "Reescribe la definición de exterior con `def_exterior`."
  rw [def_exterior]
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Usa la caracterización de los puntos del interior
    para reescribir `{h}`."
    rw [caracterizacion_interior] at h
    Hint (hidden := true) "Puedes elegir un abierto (con `choose`)
    gracias a `{h}`."
    choose U hUan hxU hUAc using h
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · exact hUan
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hxU
    · Hint (hidden := true) "Para ver la igualdad de dos conjuntos,
      toma un elemento arbitrario (con `ext`) y demuestra que está en
      uno si y sólo si no está en el otro."
      ext y
      Hint (hidden := true) "Puedes simplificar la expresión."
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      Hint (hidden := true) "Viene a ser lo mismo que dice `{hUAc}`, así
      que puedes aplicarlo."
      apply hUAc
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Usa la caracterización de los puntos del interior
    para reescribir el objetivo."
    rw [caracterizacion_interior]
    Hint (hidden := true) "Puedes elegir un abierto (con `choose`)
    gracias a `{h}`."
    choose U hUan hxU hUAc using h
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · exact hUan
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hxU
    · Hint (hidden := true) "Para ver el contenido de dos conjuntos, toma
      un elemento arbitrario con `intro`."
      intro y hy
      Hint (hidden := true) "Para ver que `{y}` no está en `{A}`,
      lo que puedes hacer es suponer que está (`intro` también sirve
      para esto, cuando el objetivo es una negación)."
      intro hyA
      Hint (hidden := true) "Como `{y}` está en `{U}` y en `{A}`,
      puedes demostrar que está en `{U} ∩ {A}`. Crea un nuevo objetivo
      (con `have`) para probar esto."
      have h2 : y ∈ U ∩ A
      · fconstructor
        · exact hy
        · exact hyA
      Hint (hidden := true) "Ahora puedes usar `{hUAc}` para reescribir `{h2}`."
      rw [hUAc] at h2
      Hint (hidden := true) "Ahora `{h2}` es exactamente la contradicción
      que necesitamos."
      apply h2

end topo
