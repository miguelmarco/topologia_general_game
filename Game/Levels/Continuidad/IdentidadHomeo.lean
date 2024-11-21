import Game.Levels.Continuidad.CorolarioBaseEntornos

World "Continuidad"
Level 7
Title "Homeomorfismos."

Introduction "Una aplicación entre espacios topológicos es un *homeomorfismo*
si es contínua, biyectiva, y su inversa es contínua.

Veamos algunas propiedades de los homeomorfismos
"

namespace topo
open topo espacio_topologico Set
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)


def homeomorfismo := continua f ∧ ∃ g : Y →  X, continua g ∧ g ∘ f = id ∧ f ∘ g = id

theorem def_homeomorfismo : homeomorfismo f ↔ continua f ∧ ∃ g : Y →  X, continua g ∧ g ∘ f = id ∧ f ∘ g = id  := by rfl

/--
Si `f : X → Y` es una aplicación entre espacios topológicos, `def_homeomorfismo`
dice que `homeomorfismo f ↔ continua f ∧ ∃ g : Y →  X, continua g ∧ g ∘ f = id ∧ f ∘ g = id `.
-/
TheoremDoc topo.def_homeomorfismo as "def_homeomorfismo" in "Continuidad"

/--
Una aplicación entre espacios topológicos es un *homeomorfismo*
si es contínua, biyectiva, y su inversa es contínua.
-/
DefinitionDoc homeomorfismo as "homeomorfismo"

NewDefinition homeomorfismo

NewTheorem topo.def_homeomorfismo

/--
La aplicación identidad `id: X → X` es un homeomorfismo.
-/
TheoremDoc topo.homeomorfismo_identidad as "homeomorfismo_identidad" in "Continuidad"

Statement homeomorfismo_identidad : homeomorfismo (id : X → X) := by
  Hint (hidden := true) "Empieza reescribiendo la definición de homeomorfismo."
  Hint (hidden := true) "`rw [def_homeomorfismo]`."
  rw [def_homeomorfismo]
  Hint (hidden := true) "Puedes separar el objetivo en varios usando `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Si no recuerdas cómo probar que una función es
    continua, reescribe la definición de continuidad."
    rw [def_continua]
    Hint (hidden := true) "Ahora puedes tomar un abierto arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Si no ves claro qué es la preimagen por la
    aplicación identidad de `{U}`, prueba a simplificar con `simp`."
    simp only [preimage_id_eq, id_eq]
    Hint (hidden := true) "Ahora el objetivo es exactamente una de tus hipótesis."
    exact hU
  · Hint (hidden := true) "Para ver que hay inversa a la aplicación identidad,
    ¿qué aplicación puedes usar?"
    use id
    Hint (hidden := true) "Ahora puedes separar el objetivo en varios con
    `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Como para ver que una aplicación es continua
      hay que ver que la preimagen de un abierto es un abierto, puedes
      tomar un abierto arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Aunque estén escritos de forma distinta,
      el objetivo y `{hU}` dicen lo mismo. Así que `exact `{hU}`
      funcionaría. Si no lo ves claro y prefieres ir más paso a paso, prueba a
      simplificar el objetivo con `simp`."
      exact hU
    fconstructor
    · Hint (hidden := true) "Esto se puede probar simplemente simplificando
      (con `simp`)."
      simp only [Function.comp_id]
    · Hint (hidden := true) "Ahora hay que volver a probarlo. De hecho es
      también es cierto por definición, así que se puede probar con `rfl`."
      rfl

end topo
