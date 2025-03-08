import Game.Levels.Cocientes.ComposicionIdentificaciones

World "Cocientes"
Level 11
Title "Aplicaciones cuya composición es una identificación."

Introduction "
Veamos ahora que si la composición de aplicaciones continuas es una identificación,
la última aplicación debe ser también una identificación.
"




namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]

/--
Si `f : X → Y` y `g : Y → Z` son aplicaciones continuas, y `g ∘ f` es una identificación,
entonces `g` debe ser una identificación.
-/
TheoremDoc topo.identificacion_composicion as "identificacion_composicion" in "Cocientes"


Statement identificacion_composicion  {Z : Type} [espacio_topologico Z] (f : X → Y) (g : Y → Z) (hf : continua f) (hg : continua g) (h: identificacion (g ∘ f)) :
    identificacion g:= by
  Hint (hidden := true) "Puedes separar `{h}` en dos afirmaciones con `choose` o `cases'`."
  choose h1 h2 using h
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Para ver que es suprayectiva, toma un elemento arbitrario
    con `intro`, y pasemos a ver que tiene preimagen."
    intro z
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{h1}` a `{z}`."
    have hz := h1 z
    Hint (hidden := true) "Gracias a `{hz}`, puedes elegir un elemento de `{X}`
    que sea preimagen."
    choose x hx using hz
    Hint (hidden := true) "¿Qué elemento de `{Y}` puedes usar que sea una
    preimagen de `{z}`?"
    use f x
    exact hx
  · Hint (hidden := true) "Toma un conjunto arbitrario con `intro`."
    intro U
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar que `{g}` es continua."
      apply hg
    · Hint (hidden := true) "Puedes reescribir el objetivo gracias a `{h2}`."
      rw [h2]
      Hint (hidden := true) "Ahora puedes aplicar que `{f}` es continua."
      apply hf

end topo
