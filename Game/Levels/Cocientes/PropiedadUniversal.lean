import Game.Levels.Cocientes.SaturadoCerrado
World "Cocientes"
Level 5
Title "Propiedad universal de los cocientes."

Introduction "
Veamos cómo son las aplicaciones continuas del cociente de un espacio
topológico en otro.
"



namespace topo
open topo espacio_topologico Set

variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] [R : Equiv X]


/--
Si `X`, e `Y` son espacios topológicos, y `R` una relación de equivalencia en
`X`, una aplicación `f : X /' R  → Y` es continua si y solo si `f ∘ π : X → Y` es continua.
-/
TheoremDoc topo.continua_de_cociente_sii as "continua_de_cociente_sii" in "Cocientes"

Statement continua_de_cociente_sii  (f : X /' R → Y) : continua f ↔ continua (f ∘ π : X → Y) := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes aplicar el teorema que dice que la composición
    de aplicaciones continuas es continua."
    apply composicion_continuas
    · Hint (hidden := true) "Tienes un teorema que te dice eso."
      apply cociente_continua
    · apply h
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Puedes reescribir lo que significa ser abierto en
    un cociente."
    rw [def_abierto_cociente]
    Hint (hidden := true) "Si te fijas, el conjunto que quieres ver
    que es abierto, es exactamente `π ⁻¹' ({f} ⁻¹' {U})`, así que
    puedes aplicar `{h}`."
    apply h
    exact hU


end topo
