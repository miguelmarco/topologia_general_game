import Game.Levels.EspaciosTopologicos.Entornos

open espacio_topologico Set



World "EspaciosTopologicos"
Level 8
Title "Propiedades de entornos: N1."

Introduction "Recordemos que, dado un punto de un espacio topológico, hay una familia
de conjuntos formada por los entornos del punto.

En este nivel y los siguientes comprobaremos que las familias
de los entornos de los puntos en un espacio topológico cumplen ciertas propiedades.

Concretamente, en este nivel veremos que cumplen una propiedad muy simple, llamada
$N_1$. Esta propiedad simplemente afirma que para cualquier punto, existe algún entorno.
"

variable (X : Type)  [espacio_topologico X]

/--
Dado un punto cualquiera de un espacio topológico, existe algún entorno.
-/
TheoremDoc N1 as "N1" in "Espacios Topológicos"

/--
Dado un punto cualquiera de un espacio topológico, existe algún entorno.
-/
Statement N1 : ∀ (x : X), ∃ U , entorno x U := by
  Hint (hidden := true) "Como hay que demostrar una propiedad para todo punto, puedes tomar un
  punto arbitrario con `intro x`."
  intro x
  Hint "Ahora hay que demostrar que existe algún entorno de `{x}`. Para ello, deberíamos
  dar uno. ¿Se te ocurre cual puede ser?"
  Hint (hidden := true) "Recuerda que el conjunto total de `{X}` se denota con `univ`,
  y que la táctica para decir qué conjunto usar para demostrar una existencia es `use`."
  use univ
  Hint (hidden := true) "Si no sabes qué hacer, prueba a reescribir la definición de ser
  entorno, con `rw [def_entorno]`."
  rw [def_entorno]
  Hint "Ahora de nuevo hay que demostrar que existe un abierto que contiene a `x` y está
  dentro del entorno. ¿Cual puedes asegurar que es?"
  Hint (hidden := true) "El único abierto no vacío que siempre puedes asegurar que existe,
  es, de nuevo, `univ`."
  use univ
  Hint (hidden := true) "Recuerda que para separar un objetivo que está formado por varios,
  puedes usar la táctica `fconstructor`."
  fconstructor
  · Hint (hidden := true) "¿Hay algún resultado que puedas aplicar?"
    Hint (hidden := true) "Te pueden servir tanto `apply abierto_total` como `exact abierto_total`."
    exact abierto_total
  · Hint (hidden := true) "De nuevo, recuerda que para separar un objetivo en sus partes,
    se puede usar la táctica `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Esto se cumple trivialmente. Así que puedes usar la táctica `trivial`."
      trivial
    · Hint (hidden := true) "Esto se cumple trivialmente. Así que puedes usar la táctica `trivial`."
      trivial
