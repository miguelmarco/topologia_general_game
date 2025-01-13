import Game.Levels.Productos.EntornoProducto
World "Productos"
Level 2
Title "Las proyecciones son contínuas"

Introduction "
Ahora vamos a ver que las proyecciones de un producto en sus factores son continuas.

En particular haremos la demostración de la primera proyección.
"

namespace topo
open topo espacio_topologico Set


variable (X Y : Type) [espacio_topologico X] [espacio_topologico Y]


/--
Dado un producto de espacios topológicos `X × Y`, `proyeccion_continua_1` dice
que la proyección `π₁ : X × Y → X` es contínua.
-/
TheoremDoc topo.proyeccion_continua_1 as "proyeccion_continua_1" in "Productos"


Statement proyeccion_continua_1 : continua (π₁ : X × Y → X) := by
  Hint (hidden := true) "Para ver que una función es contínua, hay que ver
  que la preimagen de un abierto es abierto. Toma un abierto arbitrario con
  `intro`."
  intro U hU
  Hint (hidden := true) "Aquí será útil reescribir el objetivo en términos
  de entornos."
  rw [abierto_sii_entorno]
  Hint (hidden := true) "Toma pues un punto arbitrario con `intro`."
  intro z hz
  Branch
    simp only [mem_preimage] at hz
    Hint (hidden := true) "Podemos usar el resultado anterior
    para reescribir el objetivo."
    rw [caracterizacion_entorno_producto]
    Hint (hidden := true) "Hay que dar un abierto de `{X}`, ¿cual puedes usar?."
    use U
    Hint (hidden := true) "Ahora no tienes disponible ningún subconjunto de `{Y}`.
    ¿Sabes de algún conjunto de `{Y}` que puedas asegurar que es abierto?"
    use univ
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar un teorema que asegura esto."
      exact abierto_total
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hz
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Esto es trivial."
      trivial
    · Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
      toma un elemento (con `intro`) y demuestra que está en el segundo."
      intro a ha
      Hint (hidden := true) "Prueba a simplificar `{ha}` y el objetivo."
      simp only [mem_preimage]
      simp only [mem_prod, simp_proj_1, simp_proj_2, mem_univ, and_true] at ha
      exact ha
  Hint (hidden := true) "Podemos usar el resultado anterior
  para reescribir el objetivo."
  rw [caracterizacion_entorno_producto]
  Hint (hidden := true) "Hay que dar un abierto de `{X}`, ¿cual puedes usar?."
  use U
  Hint (hidden := true) "Ahora no tienes disponible ningún subconjunto de `{Y}`.
  ¿Sabes de algún conjunto de `{Y}` que puedas asegurar que es abierto?"
  use univ
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hU
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes aplicar un teorema que asegura esto."
    exact abierto_total
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · exact hz
  Hint (hidden := true) "Separa el objetivo con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Esto es trivial."
    trivial
  · Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
    toma un elemento (con `intro`) y demuestra que está en el segundo."
    intro a ha
    Hint (hidden := true) "Prueba a simplificar `{ha}` y el objetivo."
    simp only [mem_preimage]
    simp only [mem_prod, simp_proj_1, simp_proj_2, mem_univ, and_true] at ha
    exact ha




end topo
