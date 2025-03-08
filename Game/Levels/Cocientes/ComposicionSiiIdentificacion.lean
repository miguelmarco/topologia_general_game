import Game.Levels.Cocientes.IdentificacionComposicion

World "Cocientes"
Level 12
Title "Una identificación compuesta con una aplicación."

Introduction "
Veamos ahora que si `f`  es una composición, entonces `g ∘ f` es una composición
si y solo si `g` lo es.

Esta demostración será fácil gracias a lo demostrado en los niveles anteriores.
"

namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]

/--
Si `f : X → Y` es una identificación, y `g : Y → Z` es continua,
entonces `g ∘ f` es una identificación si y solo si `g` lo es.
-/
TheoremDoc topo.composicion_sii_identificacion as "composicion_sii_identificacion" in "Cocientes"

Statement composicion_sii_identificacion  {Z : Type} [espacio_topologico Z] (f : X → Y) (g : Y → Z) (hg : continua g) (hf : identificacion f):
    identificacion (g ∘ f) ↔ identificacion g := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Tenemos un teorema que nos dice exactamente esto
    (suponiendo alguna condición extra),
    aplícalo."
    apply identificacion_composicion
    · Hint (hidden := true) "Necesitamos ver que `{f}` es continua,
      pero tenemos un teorema que nos dice que las identificaciones lo son. Aplícalo."
      apply identificacion_continua
      exact hf
    · exact hg
  · Hint (hidden := true) "En los niveles anteriores hemos demostrado un teorema que
    podemos aplicar aquí."
    apply composicion_identificaciones
    exact hf

end topo
