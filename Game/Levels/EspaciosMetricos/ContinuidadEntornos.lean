import Game.Levels.EspaciosMetricos.FuncionesContinuas

variable {X : Type} {Y : Type} [espacio_metrico X] [espacio_metrico Y]
open espacio_metrico

World "EspaciosMetricos"
Level 11
Title "Caracterización de continuidad mediante entornos."

Introduction "En este nivel vamos a ver una caracterización de la continuidad de una
función entre espacios métricos, en términos de entornos.
"

/--
Dada una función $f : X → Y$ entre espacios métricos, y un punto $x ∈  X$, $f$ es continua
en $x$ si y sólo si para todo entorno $V$ de $f(x)$, existe un entorno $U$ de $x$ tal que
$f(U) ⊆ V$.
-/
TheoremDoc caracterizacion_d_continua_en_entornos as "caracterizacion_d_continua_en_entornos" in "Espacios Métricos"

/--
Dada una función $f : X → Y$ entre espacios métricos, y un punto $x ∈  X$, $f$ es continua
en $x$ si y sólo si para todo entorno $V$ de $f(x)$, existe un entorno $U$ de $x$ tal que
$f(U) ⊆ V$.
-/
Statement caracterizacion_d_continua_en_entornos (f : X → Y) (x : X) :
    d_continua_en f x ↔ ∀ V, entorno_metrico (f x) V → ∃ U, entorno_metrico x U ∧ f '' U ⊆ V := by
  Hint (hidden := true) "Al ser una doble implicación, habrá que separarla en dos implicaciones."
  fconstructor
  · Hint (hidden := true) "Tal vez sea útil usar la caracterización de continuidad en términos de bolas."
    Branch
      rw [caracterizacion_d_continua_en_bola]
      Hint (hidden := true) "Puedes introducir el antedecente como hipótesis."
      intro h
      intro V hV
      Hint (hidden := true) "Prueba a reescribir qué significa que `{V}` sea entorno de `{f} {x}`."
      rw [def_entorno_metrico] at hV
      Hint (hidden := true) "Como `{hV}` nos asegura que existen unos ciertos radios, puedes elegir uno."
      choose ε hε0 hε using hV
      Hint (hidden := true) "Ahora que tienes `{ε}`, puedes combinarlo con `{h}` para obtener
      una nueva hipótesis."
      have h2 := h ε hε0
      Hint (hidden := true) "Como existen unos ciertos `δ`, puedes elegir uno de ellos."
      choose δ hδ0 hδ using h2
      Hint (hidden := true) "¿Qué conjunto puedes usar que sea entorno de `{x}` y su imagen esté en `{V}`?"
      use bola x δ
      Hint (hidden := true) "De nuevo, habrá que separar el objetivo en dos."
      fconstructor
      · Hint (hidden := true) "Tal vez se útil reescribir lo que significa ser entorno."
        rw [def_entorno_metrico]
        Hint (hidden := true) "¿Qué radio podemos usar?"
        use δ
      · Hint (hidden := true) "Recuerda que la forma habitual de demostrar que un conjunto está
        contenido en otro es tomar un elemento arbitrario del primero y ver que está en el segundo."
        intro y hy
        Hint (hidden := true) "Como tienes una hipótesis que te asegura que un conjunto está contenido
        en `{V}`, tal vez puedas aplicarla."
        apply hε
        Hint (hidden := true) "Como tienes una hipótesis que te asegura que un conjunto está contenido
        en `bola ({f} {x}) {ε}`, tal vez puedas aplicarla."
        apply hδ
        Hint (hidden := true) "Tienes una hipótesis que afirma exactamente el objetivo."
        exact hy
    intro h
    Hint (hidden := true) "Queremos demostrar que algo es cierto para todo entorno `V`,
     así que habrá que tomar uno arbitrario."
    intro V hV
    Hint (hidden := true) "¿Qué quiere decir que `{V}` sea entorno métrico de `{f} {x}`?"
    rw [def_entorno_metrico] at hV
    Hint (hidden := true) "Al tener una hipótesis que nos asegura que existen radios con ciertas
    propiedades, podemos elegir uno de ellos."
    choose r hr0 hr using hV
    Hint (hidden := true) "Qué quiere decir que `{f}` sea d_continua en `{x}`?"
    Branch
      rw [def_d_continua_en] at h
      Hint (hidden := true) "Puedes aplicar `{h}` a `{r}` y `{hr0}` para obtener una nueva hipótesis."
      have h2 := h r hr0
      Hint (hidden := true) "De nuevo, puedes elegir un `δ`."
      choose δ hδ0 hδ using h2
      Hint (hidden := true) "¿Qué entorno puedes usar?"
      use bola x δ
      fconstructor
      · use δ
      · Hint (hidden := true) "Recuerda la forma habitual de demostrar que un cojunto está contenido
        en otro."
        intro y hy
        apply hr
        Hint (hidden := true) "Prueba a reescribir la definición de estar en la imagen de un conjunto."
        rw [def_imagen_conjunto] at hy
        Hint (hidden := true) "Al saber que existe al menos una preimagen de `{y}`, puedes elegir una."
        choose x1 hx1 hx1y using hy
        Hint (hidden := true) "Puede ser útil reescribir la definición de estar en una bola, tanto
        en el objetuvo como en las hipótesis que correspondan."
        rw [def_bola] at *
        Hint (hidden := true) "Observa que `{hx1y}` te permite reescribir algo en el objetivo...
        pero en el sentido contrario."
        rw [← hx1y]
        Hint (hidden := true) " Ahora se puede aplicar `{hδ}`."
        apply hδ
        exact hx1
    have h2 := h r hr0
    Hint (hidden := true) "De nuevo, puedes elegir un `δ`."
    choose δ hδ0 hδ using h2
    Hint (hidden := true) "¿Qué entorno puedes usar?"
    use bola x δ
    fconstructor
    · use δ
    · Hint (hidden := true) "Recuerda la forma habitual de demostrar que un cojunto está contenido
      en otro."
      intro y hy
      Hint (hidden := true) "Prueba a reescribir la definición de estar en la imagen de un conjunto."
      rw [def_imagen_conjunto] at hy
      Hint (hidden := true) "Al saber que existe al menos una preimagen de `{y}`, puedes elegir una."
      choose x1 hx1 hx1y using hy
      have h2 := hδ x1 hx1
      Hint (hidden := true) "Observa que `{hx1y}` nos permite reescribir parte de `{h2}`"
      rw [hx1y] at h2
      Hint (hidden := true) "Se puede aplicar que un cierto conjungo está contenido en `{V}`."
      apply hr
      exact h2
  · Hint "En este subobjetivo vamos a intentar aplicar algunos hechos sin necesidad de reescribirlos
    hasta su definición más básica. Si tenemos claro qué significa cada concepto, este enfoque puede
    ser más ágil."
    Hint (hidden := true) "Como de costumbre, habrá que introducir el antecedente como hipótesis."
    intro h
    Hint (hidden := true) "También habrá que introducir un `ε` arbitrario."
    intro ε hε0
    Hint (hidden := true) "¿Puedes tener una nueva hipótesis aplicando `{h}` a algún valor concreto?"
    have h2 := h (bola (f x) ε)
    Hint (hidden := true) "Ahora para poder usar `{h2}`, necesitamos una prueba de que
    `entorno_metrico ({f} {x}) (bola ({f} {x}) {ε})`. Recuerda que la táctica `have` también se
     puede usar para crear un objetivo secundario como este."
    have haux : entorno_metrico (f x) (bola (f x) ε)
    · Hint (hidden := true) "Para ver que algo es entorno métrico de un punto, hay que dar un radio adecuado."
      use ε
    Hint (hidden := true) "Ahora ya podemos tener una nueva hipótesis a partir de `{h2}` y `{haux}`."
    have h3 := h2 haux
    Hint (hidden := true) "Al tener garantizada la existencia de entornos `U`, podemos elegir uno
     de ellos."
    choose U hU hUε using h3
    Hint (hidden := true) "Recuerda que ser entorno métrico significa que existen algunos radios de bolas
    contenidas en el entorno. Así que podemos elegir uno de ellos."
    choose δ hδ0 hδ using hU
    Hint (hidden := true) "Ahora ya tenemos un radio que podemos usar."
    use δ
    Hint (hidden := true) "Como de costumbre, hay que separar el objetivo en dos."
    fconstructor
    · Hint (hidden := true) "Hay una hipótesis que afirma exactamente el objetivo."
      exact hδ0
    · Hint (hidden := true) "Habrá que tomar un punto arbitrario."
      intro x1 hx1
      Hint (hidden := true) "Fíjate que `{hUε}` nos asegura que ciertos puntos están a distancia
      menor que `{ε}` de `({f} {x})`."
      apply hUε
      Hint (hidden := true) "Para demostrar que un elemento está en la imagen del conjunto, hay que
      encontrar un elemento en el conjunto cuya imagen sea dicho elemento. ¿Cual puede ser en este caso?"
      use x1
      fconstructor
      · Hint (hidden := true) "Tenemos la garantía de que un cierto conjunto está contenido en `{U}`."
        apply hδ
        Hint (hidden := true) "Observa que, en realidad, una de las hipótesis dice exactamente lo
        que queremos demostrar."
        exact hx1
      · Hint (hidden := true) "Esto es trivialmente cierto."
        rfl
