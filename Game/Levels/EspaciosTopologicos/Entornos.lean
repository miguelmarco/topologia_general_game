import Game.Levels.EspaciosTopologicos.UnionFinitaCerrados

open espacio_topologico



World "EspaciosTopologicos"
Level 7
Title "Entornos."

Introduction "En el caso de los espacios métricos, teníamos la noción
de entorno métrico, y a partir de ella definiamos la de abierto métrico.

En los espacios topológicos, la noción primitiva es la de abierto,
veremos aquí que podemos definir a partir de ella la de entorno de un
punto, de forma que la relación entre los abiertos y los entornos
es análoga a la de los abiertos métricos con los entornos métricos:
un conjunto es abierto si y solo si es entorno de todos sus puntos.

En esta demostración tendremos que introducir una hipótesis auxiliar
para reescribir un conjunto de una cierta forma.
"

variable {X : Type} [espacio_topologico X]

def entorno (x : X) (E : Set X) := ∃ U ∈ abiertos, x ∈ U ∧ U ⊆ E

lemma def_entorno (x : X) (E : Set X) : entorno x E ↔  ∃ U ∈ abiertos, x ∈ U ∧ U ⊆ E := by rfl

/--
En un espacio topológico, un conjunto `E` es entorno de un punto `x`
si y solo si existe un abierto `U` tal que `x ∈ U` y `U ⊆ E`.
-/
TheoremDoc def_entorno as "def_entorno" in "Espacios Topológicos"

NewTheorem def_entorno

/--
Dados un espacio topológico $X$, un punto $x ∈ X$ y un conjunto $E ⊆ X$,
se dice que *$E$ es un entorno de $x$* si existe un abierto $U$ tal que
$x ∈ U$ y $U ⊆ E$.

En Lean, esto se escribe como `entorno x E`.
-/
DefinitionDoc entorno as "entorno"

NewDefinition entorno

/--
Si quieres definir un objeto auxiliar en algún momento de una demostración,
puedes hacerlo con la táctica `let`.

Por ejemplo, puedes definir el conjunto `g` de los números naturales mayores que `5`
con `let g := { n : ℕ | n > 5}`.
-/
TacticDoc «let»

/--
Para probar que dos conjuntos son iguales, hay que ver que tomar un elementro arbitrario
y ver que está en uno si y solo si está en el otro.

Análogamente, para ver que dos funciones son iguales, hay que tomar un elemento arbitrario
y ver que la imagen de ese elemento por la primera función coincide con laimagen por la segunda.

Esto se llama *principio de extensionalidad*, y la forma de usarlo en Lean es mediante la
táctica `ext`.

Si tu objetivo se puede demostrar mediante extensionalidad (como por ejemplo, una igualdad
de conjuntos o funciones), la táctica `ext x` introducirá un elemento arbitrario
y cambiará el objetivo a demostrar la condición de extensionalidad correspondiente.
-/
TacticDoc ext

NewTactic «let» ext

/--
En un espacio topológico, un conjunto es abierto si y solo si
es entorno de todos sus puntos
-/
TheoremDoc abierto_sii_entorno as "abierto_sii_entorno" in "Espacios Topológicos"

/--
En un espacio topológico, un conjunto es abierto si y solo si
es entorno de todos sus puntos
-/
Statement abierto_sii_entorno (U : Set X) : U ∈ abiertos ↔ ∀ x ∈ U, entorno x U := by
  Hint (hidden := true) "Como hay que demostrar una doble implicación, puedes
  descomponerla en las dos implicaciones que la constituyen."
  fconstructor
  · Hint (hidden := true) "Como es una implicación, puedes introducir el antecedente
    como hipótesis."
    intro h
    Hint (hidden := true) "Como hay que demostrar algo para todo elemento
    de un conjunto, puedes tomar un elemento arbitrario que esté en el conjunto."
    intro x hx
    Hint (hidden := true) "Para ver que es entorno, hay que encontrar un
    abierto intermedio. ¿Se te ocurre cual puedes usar?"
    use U
  · Hint (hidden := true) "Como es una implicación, puedes introducir el antecedente
    como hipótesis."
    intro h
    Hint "Antes de poder continuar, necesitarás ver que `{U}` es igual
    a una unión de conjuntos abiertos. Recuerda que se pueden enunciar
    resultados intermedios usando la táctica `have`.

    Hay dos posibles familias de abiertos que se pueden usar. Una se
    obtiene recorriendo los abiertos intermedios que nos vaya dando la
    hipótesis `{h}` para cada elemento de `{U}` (usando la táctica `choose!`).

    La otra opción, es tomar todos los abiertos que estén contenidos en `{U}`."
    Hint (hidden := true) "Puedes continuar con `choose! f hfab hfx hfU using {h}`
    o con `let F := \{ V ∈ abiertos | V ⊆ {U}}`."
    Branch
      choose! f hf1 hf2 hf3 using h
      Hint (hidden := true) "Ahora necesitas un resultado auxiliar de que la unión de la imagen
      de `U` por `f` es igual a `U`."
      Hint (hidden := true) "Usa `have haux : U = ⋃₀ (f '' U)`."
      have haux1 : U = ⋃₀ (f '' U)
      · Hint (hidden := true) "Para tomar un elemento arbitrario puedes usar `ext x`."
        ext x
        Hint (hidden := true) "Puedes dividir la dible implicación en las dos implicaciones
        que la constituyen."
        fconstructor
        · intro h
          Hint (hidden := true) "¿Qué objeto de `{f} '' {U}` puedes
          garantizar que contiene a `{x}`?"
          use f x
          Hint (hidden := true) "Hay que separar la conjunción en las dos
          proposiciones que la forman."
          fconstructor
          · Hint (hidden  := true) "¿Qué elemento de `{U}` puedes asegurar que
            da lugar a `{f} {x}`?"
            use x
          · Hint (hidden := true) "¿Puedes aplicar alguna hipótesis que te asegure
            lo que quieres?"
            apply hf2
            exact h
        · intro h
          Hint (hidden := true) "{h} te asegura que hay algún
          elemento de `{f} '' {U}` al cual pertenece `x`. Puedes elegirlo
          con `choose`."
          choose V hV hxV using h
          Hint (hidden := true) "{hV} te asegura que `{V}` es la imagen de un
          cierto elemento de `{U}`. Puedes elegir ese elemento con `choose`."
          choose y hyU hfy using hV
          Hint (hidden := true) "Puedes obtener una nueva hipótesis si aplicas `{hf3}`
          a `{y}` y `{hyU}`."
          have h2 := hf3 y hyU
          Hint (hidden := true) "Fíjate que puedes aplicar una de tus hipótesis."
          apply h2
          Hint (hidden := true) "Puedes usar `{hfy}` para reescribir el objetivo."
          rw [hfy]
          exact hxV
      Hint (hidden := true) "Ahora que tienes `{haux1}`, puedes usarlo
      para reescribir el objetivo."
      rw [haux1]
      Hint (hidden := true) "Como tu objetivo ahora es demostrar que una
      cierta unión es un abierto, puedes aplicar un resultado que
      afirma que, bajo ciertas condiciones, eso ocurre."
      apply union_abiertos
      Hint (hidden := true) "Toma un elemento arbitrario de `{f} '' {U}`
      usando `intro`."
      intro E hE
      Hint (hidden := true) "Como `{E}` está en `{f} '' {U}`, tiene
      que existir algún elemento de `{U}` tal que su imagen es `{E}`.
      Puedes elegirlo usando `choose`."
      choose x hxU hxE using hE
      Hint (hidden := true) "Puedes usar `{hxE}` para reescribir el objetivo
      (cuidado con el sentido de la sustitución)."
      rw [← hxE]
      Hint (hidden := true) "¿Qué hipótesis puedes aplicar para ver que la imagen
      de algo es un abierto?"
      apply hf1
      exact hxU
    Hint (hidden := true) "Puedes definir el conjunto de los abiertos
    contenidos en `{U}` con `let F := \{ E ∈ abiertos | E ⊆ {U}} `."
    let F := { E ∈ abiertos | E ⊆ U}
    Hint (hidden := true) "Ahora quieres ver que `{U}` es igual a la unión de `{F}`.
    Recuerda que la táctica para enunciar y demostrar resultados intermedios es `have`.
    "
    have haux : U = ⋃₀ F
    · Hint (hidden := true) "Para tomar un elemento arbitrario, usa `ext x`."
      ext x
      Hint (hidden := true) "Usa `fconstructor` para separar en dos implicaciones."
      fconstructor
      · intro hx
        Hint (hidden := true) "Necesitas obtener una nueva hipótesis aplicando
        `{h}` a `{x}` y `{hx}`."
        have hxen := h x hx
        Hint (hidden := true) "Como `{hxen}` te asegura que hay un abierto intermedio
        entre `{x}` y `{U}`, puedes elegirlo con `choose`."
        choose V hVab hxV hVU using hxen
        Hint (hidden := true) "Quieres ver que `{x}` pertenece a algún
        conjunto de `{F}`. ¿Cual puedes usar?"
        use V
        fconstructor
        · Hint (hidden := true) "Piensa qué significa exactamente que `{V}`
          esté en `{F}`. Si no lo ves claro, puedes pedir que te simplifique
          la definición de `{F}` con `simp [{F}]`."
          trivial
        · exact hxV
      · intro hx
        Hint (hidden := true) "Como `{hx}` te asegura que `{x}` está en algún
        elemento de `{F}`, puedes elegir uno de ellos."
        choose V hV hxV using hx
        Hint (hidden := true) "Piensa qué significa exactamente que
        `{V}` esté en `{F}`. Si no lo ves claro, puedes simplificar
        la definición de `{F}` con `simp [{F}] at `{hV}`."
        simp [F] at hV
        Hint (hidden := true) "Ahora puedes usar `choose` o `cases'`
        para obtener dos hipótesis a partir de `{hV}`."
        cases' hV with hVab hVU
        Hint (hidden := true) "Ahora puedes aplicar `{hVU}`."
        apply hVU
        exact hxV
    Hint (hidden := true) "Ahora puedes usar `{haux}` para reescribir
    el objetivo."
    rw [haux]
    Hint (hidden := true) "¿Qué resultado conocido puedes aplicar
    para demostrar que una unión de conjuntos es un abierto?"
    apply union_abiertos
    Hint (hidden := true) "Deberás introducir un elemento arbitrario
    de `{F}` y demostrar que es un abierto."
    intro V hV
    Hint (hidden := true) "Como antes, `{hV}` nos dice dos cosas:
    que `{V}` es un abierto y que está contenido en `{U}`.
    Puedes usar `choose` o `cases'` para obtener esas dos afirmaciones."
    cases' hV with hVab hVU
    exact hVab
