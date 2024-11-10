import Game.Levels.Clausura.ClausuraUnion
open espacio_topologico Set Function

World "Clausura"
Level 10
Title "La clausura son los puntos para los que el complementario no es entorno."

Introduction "
La clausura de un conjunto $A$ es el conjunto de los $x$ para los
que $X \\setminus A$ no es entorno.
"

variable {X : Type} [espacio_topologico X] (A: Set X)


/--
Dados un conjunto  `A`, ` clausura A = { x | ¬ entorno x  Aᶜ}`
-/
TheoremDoc clausura_no_entorno as "clausura_no_entorno" in "Clausura"

Statement clausura_no_entorno : clausura A = { x | ¬ entorno x  Aᶜ} := by
  Hint (hidden := true) "Para demostrar la igualdad entre dos conjuntos,
  usa el principio de extensionalidad con `ext`."
  ext x
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro hx
    Hint (hidden := true) "Para ver que una afirmación no es cierta,
    lo habitual es suponer que lo es y llegar a una contradicción.

    Puedes hacerlo con `intro`."
    intro hn
    Hint (hidden := true) "Gracias a `{hn}`, sabemos que existe un abierto
    intermedio entre `{x}` y `{A}ᶜ`. Elige uno con `choose`."
    choose U hUab hxU hUAc using hn
    Hint (hidden := true) "Puede ser útil reescribir `{hx}` en términos
    de abiertos que contienen a `{x}`."
    rw [caracterizacion_clausura] at hx
    Hint (hidden := true) "Ahora podemos obtener una nueva hipótesis
    aplicando `{hx}` a `{U}` y sus propiedades."
    have h2 := hx U hUab hxU
    Hint (hidden := true) "Como `{h2}` nos asegura que existen
    puntos con ciertas propiedades, puedes elegir uno con `choose`."
    choose y hy1 h2 using h2
    Hint (hidden := true) "Gracias a `{hUAc}` podemos obtener una
    nueva hipótesis que nos asegura que `{y}` está en `{A}ᶜ`."
    have h3 := hUAc  hy1
    Hint (hidden := true) "Ahora ya podemos dar una contradicción, aplicando
    `{h3}`."
    apply h3
    exact h2
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reescribir el objetivo en términos
    de abiertos."
    rw [caracterizacion_clausura]
    Hint (hidden := true) "Ahora puedes tomar un abierto intermedio
    arbitrario con `intro`."
    intro U hU hxU
    Hint (hidden := true) "Prueba a simplificar `{h}`."
    simp only [mem_setOf_eq] at h
    Hint (hidden := true) "En este punto, parece que no podemos encontrar un
    `y` como pide el objetivo, así que habrá que probar una demostración
    por contradicción.

    Usa `by_contra`."
    by_contra hn
    Hint (hidden := true) "Prueba a simplificar `{hn}`."
    simp at hn
    Hint (hidden := true) "Ahora la contradicción nos la puede dar `{h}`,
    ya que es la única hipótesis en la que se afirma que algo no ocurre.

    Usa `apply {h}`."
    apply h
    Hint (hidden := true) "Para demostrar que es un entorno de `{x}`, hay
    que usar un abierto intermedio, ¿cual puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · exact hxU
    · exact hn
