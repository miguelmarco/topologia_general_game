import Game.Levels.EspaciosTopologicos.N5

open espacio_topologico Set


World "Bases"
Level 1
Title "Caracterización de las bases."

Introduction "Si $X$ es un espacio topológico, y $τ$ es la familia de
todos los abiertos, una subfamilia de abiertos $B$ se dice que es una
base si para cualquier abierto $U$ hay una familia de abiertos $F⊆B$
tal que $\\bigcup F = U$.

Veamos que se puede dar una caracterización de este concepto que
en ocasiones puede resultar útil.

La demostración no es difícil, pero es larga porque tiene varios pasos
y hay que prestar atención para no perderse.
"

variable {X : Type} [espacio_topologico X]


def  base (B : Set (Set X)) := B ⊆ abiertos ∧ ∀ U ∈ abiertos, ∃ F ⊆ B, U = ⋃₀ F
/--
Si $X$ es un espacio topológico, y $τ$ es la familia de
todos los abiertos, una subfamilia de abiertos $B$ se dice que es una
base si para cualquier abierto $U$ hay una familia de abiertos $F⊆B$
tal que $\bigcup F = U$.
-/
DefinitionDoc base as "base"

NewDefinition base

TheoremTab  "Bases"

/--
Una familia `F` de subconjuntos abiertos  de un espacio topológico `X` es una base
si y sólo si para todo abierto `U` y para todo punto `x ∈ U`,
existe un `B ∈ F` tal que `x ∈ B ⊆ U`.
-/
TheoremDoc caracterizacion_base as "caracterizacion_base" in "Bases"

Statement caracterizacion_base (B : Set (Set X)) : base B ↔ B ⊆ abiertos ∧ ∀ U ∈ abiertos, ∀ x ∈ U, ∃ V ∈ B, x ∈ V ∧ V ⊆ U := by
  Hint (hidden := true) "Como siempre que tengas una doble implicación,
  puedes descomponerla en dos implicaciones con `fconstructor`."
  fconstructor
  · Hint "Empezamos demostrando que el ser base implica las propiedades descritas."
    Hint (hidden := true) "Introduce el antecedente como una nueva hipótesis con `intro h`."
    intro h
    Hint (hidden := true) "La hipótesis `{h}`, consiste en dos afirmaciones
    (recuerda la definición de base). Puedes obtenerlas con `choose` o `cases'`."
    choose h1 h2 using h
    Hint (hidden := true)  "De nuevo, hay que dividir el objetivo en dos, usando
    `fconstructor`."
    fconstructor
    · exact h1
    · Hint (hidden := true) "Toma un abierto arbitrario y un punto en él
      con `intro U hU x hx`."
      intro U hU x hx
      Hint (hidden := true) "Puedes obtener una nueva hipótesis si usas `{h2}`
      con `{U}` y `{hU}`. Recuerda que la táctica para ello es `have`."
      have h3 := h2 U hU
      Hint (hidden := true) "`{h3}` nos garantiza la existencia de subfamilias
      de `{B}` con ciertas propiedades. Puedes elegir una con `choose F hFB hxV hFU using {h3}`."
      choose F hFB hFU using h3
      Hint (hidden := true) "Observa que puedes usar `{hFU}` para reescribir
      el valor de `{U}` en `{hx}`. La táctica para ello es `rw`."
      rw [hFU] at hx
      Hint (hidden := true) "Como `{x}` está en `⋃₀ {F}`, podemos elegir
      un elemento de `{F}` que contenga a `{x}`."
      Hint (hidden := true) "La táctica para ello es `choose V hVF hxV using {hx}`."
      choose V hVF hxV using hx
      Hint (hidden := true) "¿Qué elemento de `{B}` puedes usar para demostrar la existencia
      de uno con las propiedades necesarias?"
      Hint (hidden := true) "Usa `use {V}`."
      use V
      Hint (hidden := true) "Como siempre que hay un objetivo construido como conjunción
      de varios, podemos descomponerlo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Observa que podemos aplicar que `{F} ⊆ {B}`."
        apply hFB
        exact hVF
      Hint (hidden := true) "Hay que volver a separar el objetivo en las partes que lo construyen."
      fconstructor
      · exact hxV
      · Hint (hidden := true) "Puede ser útil reescribir el valor de `{U}`."
        Hint (hidden := true) "Usa `rw [{hFU}]`."
        rw [hFU]
        Hint (hidden := true) "Para ver el contenido de conjuntos, hay que tomar un elemento
        arbitrario del primero."
        intro y hy
        Hint (hidden := true) "Para ver que `{y}` pertenece la unión de todos los conjuntos de
        `{F}`, hay que demostrar que existe un conjunto en `{F}` al cual pertenece `{y}`.
        ¿Cual puedes usar?"
        use V
  · Hint "Ya hemos demostrado la primera implicación. Veamos ahora la segunda: que si se cumplen
    las propiedades descritas,  la familia `{B}` debe ser una base."
    Hint (hidden := true) "Como siempre que hay que demostrar una implicación, podemos introducir
    el antecedente con `intro h`."
    intro h
    Hint (hidden := true) "Observa que `{h}` está formada por varias afirmaciones distintas.
    Podemos obtenerlas por separado usando `choose` o `cases'`."
    choose hBab hB using h
    Hint (hidden := true) "Si no recuerdas la definición de base, puedes desplegarla con `unfold base`
    o `rw [base]`."
    rw [base]
    Hint (hidden := true) "De nuevo, tenemos un objetivo construido con dos afirmaciones."
    Hint (hidden := true)  "Puedes usar `fconstructor` para separarlo."
    fconstructor
    · exact hBab
    · Hint (hidden := true) "Como hay que demostrar una propiedad para todo abierto, tendrás
      que tomar uno arbitrario con `intro U hU`."
      intro U hU
      Hint "Observa que `{hB}` asegura que para todo abierto se cumplen ciertas propiedades,
      Como sabemos que `{U}` es un abierto (gracias a `{hU}`), podemos obtener una nueva hipótesis
      que nos aegure que `{U}` cumple dichas propiedades."
      Hint (hidden := true) "Puedes tener esa hipótesis con `have h2 := {hB} {U} {hU}`."
      have h2 := hB U hU
      Hint "Ahora estamos en una situaciónv algo distinta a lo que estamos acostumbrados.
      ¿Cómo podemos encontrar el `F` que nos pide el objetivo?

      Si te paras a pensar (intenta hacer la demostración con lápiz y papel), deberíamos
      ir recorriendo los `V` que `{h2}` nos asegura que existen para cada `x ∈ {U}`.
      Es decir, necesitamos considerar una función que tome puntos de `X` y produzca conjuntos
      en `B`, y considerar imagen de `{U}` por dicha función.

      Podemos intuir que `{h2}` es la hipótesis clave para obtener la función que necesitamos.
      Cuando tengamos una hipótesis que afirma que para todo objeto en un conjunto existe otro
      con una cierta propiedad, podemos obtener una *función de elección* con la táctica `choose!`.

      En este caso, concreto, `choose f hf using {h2}` nos generará una función `f` y una
      hipótesis `hf` asegurando que las imágenes de `f` cumplen la propiedad que nos viene dada
      por `{h2}`. "
      choose! f hf using h2
      Hint "Ahora tenemos la función que queríamos. La familia que buscamos para demostrar el objetivo
      es precisamente la imagen de `{U}` por `{f}`.  Recuerda que esto se denota como `{f} '' {U}`."
      Hint (hidden := true) "Usa `use {f} '' {U}`."
      use f '' U
      Hint (hidden := true) "Como cada vez que tenemos un objetivo formado por dos
      afirmaciones, lo podemos separar en dos con `fconstructor`."
      fconstructor
      · Hint "Empecemos demostrando que la imagen de `{U}` está contenida en `B`."
        Hint (hidden := true) "Para demostrar el contenido, toma un elemento arbitrario de
        `{f} '' {U}` con `intro V hV`."
        intro V hV
        Hint "Observa que `{hV}` nos dice que `{V}` está en la imagen de `{U}` por `{f}`.
        Recuerda qué quería decir eso."
        Hint (hidden := true) "Si no lo tienes claro, puedes pedir a Lean que te simplifique
        la expresión de `{hV}` con `simp at {hV}`."
        Hint (hidden := true) "Como `{hV}` afirma la existencia de algún punto con ciertas
        propiedades, puedes elegir un tal punto con `choose x hxU hxV using {hV}`."
        choose x hxU hxV using hV
        Hint "Ahora observa que `{hf}` afirma que ciertas propiedades se cumplen para todo
        punto en `{U}`. Podemos obtener una nueva hipótesis si lo aplicamos al caso particular
        de `{x}` y `{hxU}`."
        Hint (hidden := true) "Teclea have hfx := {hf} {x} {hxU}`."
        have hfx := hf x hxU
        Hint (hidden := true) "Como `{hfx}` está formada por varias afirmaciones, podemos
        obtenerlas por separado con `choose`."
        choose hfxB hxfx hfxU using hfx
        Hint (hidden := true) "{hfxB} nos dice qué es `{f} {x}`. Podemos reescribirlo en
        varias hipótesis."
        rw [hxV] at hfxB
        exact hfxB
      · Hint "Una vez visto que la familia que hemos dado está contenida en `{B}`,
        veamos además que su unión es igual a `{U}`.

        Para demostrar la igualdad de dos conjunto, el principio básico es el *principio
        de extensionalidad*, que dice que dos conjuntos son iguales si pertenecer a uno es
        equivalente a pertenecer al otro. La forma de usar este principio en Lean es usar la
        táctica `ext x`, que nos permite tomar un elemento arbitrario para luego demostrar
        que pertenece al primer conjunto si y sólo si pertenece al segundo."
        ext x
        Hint (hidden := true) "De nuevo tenemos que patrir un objetivo en dos subobjetivos."
        fconstructor
        · Hint "Empecemos con el primer contenido."
          Hint (hidden := true) "Introduce el antecedente del objetivo como una hipótesis nueva."
          intro hx
          Hint "De nuevo, podemos particularizar `{hf}` al caso de `{x}` para obtener una nueva
          hipótesis."
          Hint (hidden := true)  "Teclea `hxf := {hf} {x} {hx}`."
          have hxf := hf x  hx
          Hint "Volvemos a tener una hipótesis compuesta de varias afirmaciones. Obtenlas por separado
          con `choose`."
          choose hfxB hxfx hfxU using hxf
          Hint "Piensa qué quiere decir que `{x}` esté en `⋃₀ ({f} '' {U})`."
          Hint (hidden := true) "Como hay que demostrar que existe un cierto elemento,
            piensa cual puede ser."
          Hint (hidden := true) "Si no lo ves claro, puedes pedir a Lean que simplifique la expresión."
          Branch
            simp only [sUnion_image, mem_iUnion, exists_prop]
            Hint (hidden := true) "¿Qué elemento puedes usar para ver que hay uno como te piden?"
            use x
          use f x
          Hint (hidden := true) "Otra vez hay que separar el objetivo en dos."
          fconstructor
          · Hint (hidden := true) "Si te paras a pensar qué quiere decir estar en la imagen de
            un conjunto, verás que hay que demostrar la existencia de un cierto elemento.
            ¿Cual puedes usar?"
            use x
          · exact hxfx
        · Hint "Ahora vamos con el otro contenido."
          Hint (hidden := true) "Como siempre, hay que introducir un elemento arbitrario."
          intro hx
          Hint "Piensa qué quiere decir exactamente `{hx}`."
          Hint (hidden := true) "`{hx}` nos asegura la existencia de un cierto elemento de `{U}`.
          Elígelo con `choose`."
          choose V hVfU hVx using hx
          Hint "Volvemos a tener que `{V}` está en la imagen de `{U}`. Es decir, que existe un
          punto de `{U}` cuya imagen es `{V}`. Eligelo con `choose`."
          choose y  hyU hyV using hVfU
          Hint (hidden := true) "Otra vez podemos obtener una nueva hipótesis aplicando `{hf}`
          a `{y}` y `{hyU}`, gracias a la táctica `have`."
          have hfy := hf y hyU
          Hint (hidden := true) "Separa `{hfy}` en varias hipótesis con `choose`."
          choose hfyB hyfy hfyU using hfy
          Hint (hidden := true) "Puedes aplicar `{hfyU}` con `apply`."
          apply hfyU
          Hint (hidden := true) "Observa que `{hyV}` te puede ser útil para reescribir."
          rw [hyV]
          exact hVx
