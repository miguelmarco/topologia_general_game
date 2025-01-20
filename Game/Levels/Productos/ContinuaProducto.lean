import Game.Levels.Productos.InteriorProducto
World "Productos"
Level 5
Title "Aplicaciones continas sobre productos"

Introduction "
Veamos como son las aplicaciones contínuas sobre un producto.
"

namespace topo
open topo espacio_topologico Set


variable {X Y Z : Type} [espacio_topologico X] [espacio_topologico Y] [espacio_topologico Z]


/--
Dados espacios topológicos `Z, X ,Y`, una aplicación `f : Z → X × Y` es continua
si y solo si las composiciones con las proyecciones `π₁ ∘ f` `π₂ ∘ f`  son
continuas.
-/
TheoremDoc topo.caracterizacion_continua_producto as "caracterizacion_continua_producto" in "Productos"

Statement caracterizacion_continua_producto (f : Z → (X × Y)) :
    continua f ↔ continua (π₁ ∘ f) ∧ continua (π₂ ∘ f) := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que tienes una composición de aplicaciones.
      Puedes aplicar el teorema que asegura que la composición de continuas es continua."
      apply composicion_continuas
      exact h
      Hint (hidden := true) "Puedes aplicar un teorema que dice exactamente eso."
      exact proyeccion_continua_1 X Y
    · apply composicion_continuas
      Hint (hidden := true) "Observa que tienes una composición de aplicaciones.
      Puedes aplicar el teorema que asegura que la composición de continuas es continua."
      exact h
      Hint (hidden := true) "Puedes aplicar un teorema que dice exactamente eso."
      exact proyeccion_continua_2 X Y
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes separar `{h}` en dos hipótesis con `choose`
    o `cases'`."
    choose h1 h2 using h
    Hint (hidden := true) "Aquí será útil reescribir el objetivo
    en términos de ser continua en cada punto."
    rw [continua_sii_continua_en]
    Hint (hidden := true) "Toma un punto arbitrario, y un entorno
    suyo con `intro`."
    intro z N hN
    Hint (hidden := true) "Será útil reescribir `{hN}` teniendo en cuenta
    que estamos en un producto."
    rw [caracterizacion_entorno_producto] at hN
    Hint (hidden := true) "Ahora puedes usar `{hN}` para elegir abiertos
    en `{X}` e `{Y}`, y sus propiedades."
    choose U V hU hV hzU hzV hUVN using hN
    Hint (hidden := true) "Piensa con cuidado qué abierto intermedio
    entre `{z}` y `{N}` puedes usar.
    Haz la demostración con papel y lápiz si hace falta."
    Hint (hidden := true) "Usa `(π₁ ∘ f) ⁻¹' {U} ∩ (π₂ ∘ f) ⁻¹' {V}`."
    use (π₁ ∘ f) ⁻¹' U ∩ (π₂ ∘ f) ⁻¹' V
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que es una intersección de dos conjuntos.
      Puedes aplicar un teorema para este caso."
      apply interseccion_abiertos
      · Hint (hidden := true) "Aquí es donde puedes aplicar la continuidad de
        `π₁ ∘ {f}`."
        apply h1
        exact hU
      · Hint (hidden := true) "Aquí es donde puedes aplicar la continuidad de
        `π₂ ∘ {f}`."
        apply h2
        exact hV
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Observa que el objetivo dice exactamente
        lo mismo que una hipótesis."
        exact hzU
      · exact hzV
    Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
    toma un elemento arbitrario con `intro`."
    intro t ht
    Hint (hidden := true) "Prueba a aplicar `{hUVN}`."
    apply hUVN
    exact ht


end topo
