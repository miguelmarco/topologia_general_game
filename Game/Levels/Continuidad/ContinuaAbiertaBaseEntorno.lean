import Game.Levels.Continuidad.CaracterizacionAbiertaEntorno

World "Continuidad"
Level 13
Title "Imagen de una base de entornos."

Introduction "Una aplicación continua y abierta envia bases de entornos a bases de entornos.
"

namespace topo
open topo espacio_topologico Set Function
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

/--
Si `f : X → Y` es una función contínua y abierta, `x` un punto de `x` y `ℬ` es una base
de entornos de `x`, entonces `{ f '' B | B ∈ ℬ}` es una base de entornos de `f x`.
-/
TheoremDoc topo.imagen_base_entornos as "imagen_base_entornos" in "Continuidad"

Statement imagen_base_entornos (hfcon : continua f) (hfab : abierta f) (x : X) (B : Set (Set X)) (hB : base_de_entornos x B) :
    base_de_entornos (f x) {f '' U | U ∈  B} := by
  Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce un elemento arbitrario y sus propiedades con `intro`."
    intro V hV
    Hint (hidden := true) "Puedes elegir un objeto y sus propiedades, con `choose`, gracias a `{hV}`."
    choose N hN hNV using hV
    Hint (hidden := true) "Puedes elegir un objeto y sus propiedades, con `choose`, gracias a `{hB}`."
    choose hB1 hB2 using hB
    Hint (hidden := true) "Puedes obtener una nueva hipótesis con `have`, aplicando `{hB1}` a `{N}` y `{hN}`."
    have hBx := hB1 N hN
    Hint (hidden := true) "Puedes elegir un abierto intermedio y sus propiedades, con `choose`, gracias a `{hBx}`."
    choose U hUab hxU hUN using hBx
    Hint (hidden := true) "¿Qué abierto intermedio puedes usar?"
    use f '' U
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · apply hfab
      exact hUab
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "¿Qué elemento de `{U}` puedes usar?"
      use x
    · Hint (hidden := true) "Puedes usar `{hNV}` para reescribir."
      rw [←hNV]
      Hint (hidden := true) "Introduce un elemento arbitrario y sus propiedades con `intro`."
      intro z hz
      Hint (hidden := true) "Puedes elegir un objeto y sus propiedades, con `choose`, gracias a `{hz}`."
      choose w hwU hwz using hz
      Hint (hidden := true) "¿Qué elemento de `{N}` puedes usar?"
      use w
      Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
      fconstructor
      · apply hUN
        exact hwU
      · exact hwz
  · Hint (hidden := true) "Introduce un elemento arbitrario y sus propiedades con `intro`."
    intro N hN
    Hint (hidden := true) "Puedes separar `{hB}` en sus partes con `choose`."
    choose hB1 hB2 using hB
    Hint (hidden := true) "Puedes elegir un abierto intermedio y sus propiedades, con `choose`, gracias a `{hN}`."
    choose U hUab hfxU hUN using hN
    Hint (hidden := true) "¿Qué puedes concluir a partir de `{hfcon}` y `{hUab}`? Enuncialo con `have` y pasa
    a demostrarlo."
    have haux : f ⁻¹' U ∈ abiertos
    · apply hfcon
      exact hUab
    Hint (hidden := true) "Puedes reescribir `{haux}` en términos de entornos."
    rw [abierto_sii_entorno] at haux
    Hint (hidden := true) "Puedes obtener una nueva hipótesis con `have`, aplicando `{haux}` a `{x}` y `{hfxU}`."
    have hxfU : entorno x  (f ⁻¹' U)
    · apply haux
      exact hfxU
    Hint (hidden := true) "Puedes obtener una nueva hipótesis con `have`, aplicando `{hB2}` a `{f} ⁻¹' {U}` y `{hxfU}`."
    have haux2 := hB2 (f ⁻¹' U) hxfU
    Hint (hidden := true) "Puedes elegir un objeto y sus propiedades, con `choose`, gracias a `{haux2}`."
    choose B1 hB1B hB1fU using haux2
    Hint (hidden := true) "¿Qué elemento del conjunto en cuestión puedes usar?"
    use f '' B1
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "¿Qué elemento de `{B}` puedes usar?"
      use B1
    · Hint (hidden := true) "Introduce un elemento arbitrario y sus propiedades con `intro`."
      intro y hy
      Hint (hidden := true) "Puedes elegir un objeto y sus propiedades, con `choose`, gracias a `{hy}`."
      choose x hxB1 hxy using hy
      apply hUN
      Hint (hidden := true) "Puedes usar `{hxy}` para reescribir."
      rw [← hxy]
      apply hB1fU
      exact hxB1

end topo
