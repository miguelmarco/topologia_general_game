import Game.Levels.EspaciosMetricos.ContinuidadEntornos

variable {X : Type} {Y : Type} [espacio_metrico X] [espacio_metrico Y]
open espacio_metrico

World "EspaciosMetricos"
Level 12
Title "Caracterización de continuidad mediante abiertos."

Introduction "En este nivel vamos a ver una caracterización de la continuidad de una
función entre espacios métricos, en términos de abiertos.

Para ello, usaremos los resultados `caracterizacion_d_continua_en_entornos`
de los niveles anteriores.

En este nivel usaremos la *preimagen* de un conjunto por una aplicación: dada una aplicación
$ f : X \\to Y$, y un conjunto $U \\subseteq Y$, $f ^\\{-1\\}(U)$ es el conjunto de los
elementos de $X$ cuya imagen está en $U$. Este conjunto se denota en lean como $f ⁻¹' U$.
Para obtener el símbolo `⁻¹` teclea `\\-1`.

El lema `def_preimagen` caracteriza los puntos que están en la preimagen de un conjunto.
"

lemma def_preimagen {X Y: Type} (f : X → Y) (U : Set Y) (x : X) : x ∈ f ⁻¹' U ↔ f x ∈ U := by
  rfl

/--
Dada una aplicación `f : X → Y`, un conjunto `U` de `Y`, y un elemento `x` de `X`,
`def_preimagen f U x`  nos dice que `x ∈ f ⁻¹' U ↔ f x ∈ U`
-/
TheoremDoc def_preimagen as "def_preimagen" in "lemas-definición"

NewTheorem def_preimagen

/--
Una función entre espacios métricos es continua si y solo si la preimagen de cualquier
abierto métrico es abierto métrico.
-/
TheoremDoc caracterizacion_d_continua_abiertos as "caracterizacion_d_continua_abiertos" in "Espacios Métricos"

/--
Una función entre espacios métricos es continua si y solo si la preimagen de cualquier
abierto métrico es abierto métrico.
-/
Statement caracterizacion_d_continua_abiertos (f : X → Y) :
    d_continua f ↔ ∀ (V : Set Y), abierto_metrico V → abierto_metrico ( f ⁻¹' V) := by
  Hint (hidden := true) "Al ser una doble implicación, habrá que separarla en dos implicaciones."
  fconstructor
  · Hint (hidden := true) "Puedes introducir el antecedente como hipótesis."
    intro h V hV
    Branch
      Hint (hidden := true ) "Puedes probar a reescribir la definición de abierto métrico."
      rw [def_abierto_metrico] at *
    Branch
      rw [def_abierto_metrico]
      Hint (hidden := true) "Habrá que tomar un punto arbitrario."
    intro x hx
    Branch
      rw [def_d_continua] at h
      Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{h}`
      al caso particular de `{x}`."
    have h2 := h x
    Hint (hidden := true) "Ahora que sabes que `f` es `d_continua` en `x`, puedes
    aprovechar la caracterización."
    rw [caracterizacion_d_continua_en_entornos] at h2
    Hint (hidden := true) "Puede ser un buen momento para reescribit lo que
    significa `{hx}`."
    Branch
      rw [def_preimagen] at hx
      Hint (hidden := true) "Antes de usar `{h2}`, necesitas ver que
      `{V}` es entorno métrico de `{f} {x}`. Puedes obtener esta nueva hipótesis aplicando `{hV}`
      al caso particular de `({f} {x})` y `{hx}`."
    have h3 := hV (f x) hx
    Hint (hidden := true) "Puedes aplicar `{h2}` a `{V}`y `{h3}`."
    have h4 := h2 V h3
    Hint (hidden := true) "Podemos usar elegir un  cierto entorno
    métrico de `{x}` usando `{h4}`."
    choose U hU hUV using h4
    Branch
      Hint (hidden := true) "Puedes reescribir lo que significa ser entorno
      métrico en `{hU}`."
      rw [def_entorno_metrico] at hU
      Hint (hidden := true) "Como sabes que existen radios cuyas bolas
      cumplen ciertas propiedades, puedes
      elegir uno."
    choose r hr0 hr using hU
    Branch
      Hint (hidden := true) "Puedes reescribir lo que significa ser entorno métrico."
      rw [def_entorno_metrico]
      Hint (hidden := true) "Como tienes que demostrar que existe un cierto
      radio, ¿cual puedes usar?"
    use r
    Hint (hidden := true) "Hay que demostrar una afirmación que está construida
    como la conjunción de otras dos."
    fconstructor
    · Hint (hidden := true) "Hay una hipótesis que afirma exactamente el objetivo."
      exact hr0
    · Hint (hidden := true) "Para ver que un conjunto está contenido en otro, puedes
      tomar un elemento arbitrario del primero."
      intro y hy
      Hint (hidden := true) "Puedes aplicar `{hUV}`."
      apply hUV
      Hint (hidden := true) "Puedes reescribir lo que significa estar en la imagen
      de un conjunto."
      rw [def_imagen_conjunto]
      Hint (hidden := true) "¿Qué punto puedes usar para demostrar la existencia?"
      use y
      Hint (hidden := true) "De nuevo, hay que demostrar una afirmación construida
      con otras dos."
      fconstructor
      · Hint (hidden := true) "Puedes aplicar que un conjunto está contenido en `{U}`."
        apply hr
        exact hy
      · Hint (hidden := true) "Esto es cierto pot definición."
        rfl
  · Hint (hidden := true) "Como quieres demostrar una implicación, puedes tomar
    el antecedente como hipótesis."
    intro h
    Hint (hidden := true) "Puedes tomar un punto arbitrario."
    intro x
    Branch
      Hint (hidden := true) "Puedes reescribir la definición de `d_continua_en`."
      rw [def_d_continua_en]
      Hint (hidden := true) "Habrá que tomar un radio arbitrario."
    intro e he0
    Hint (hidden := true) "Antes de poder aplicar `{h}`, necesitas
    ver que un cierto conjunto es abierto métrico. ¿Tienes claro cual
    va a ser?"
    Hint (hidden := true) "Necesitarás aplicarlo a la bola centrada en `f x`
    y de radio `{e}`. Puedes asegurar es es un abierto gracias a `bola_abierta`."
    Hint (hidden := true) "Teclea `h2 := bola_abierta (f {x}) {e} {he0}`."
    have h2 := bola_abierta (f x) e he0
    Hint (hidden := true) "Ahora puedes aplicar `{h}` para obtener una nueva hipótesis."
    Hint (hidden := true) "Como `{h2}` afirma que quien es un abierto es `bola (f {x}) {e}`,
    no hace falta explicitar a qué conjunto hay que aplicar `{h}`. Puedes
    teclear `have h3 := {h} _ {h2}`."
    have h3 := h _ h2
    Branch
      Hint (hidden := true) "Prueba a reescribir la definición de abierto métrico en `{h3}`."
      rw [def_abierto_metrico] at h3
      Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis aplicando
       `{h3}` a `x`, pero necesitarás demostrar que `x` está en `f ⁻¹' bola ({f} {x}) {e}`."
      Hint (hidden := true) "Recuerda que `have` permite usar hipótesis que no tenemos aún,
      añadiendolas como objetivos para demostrar más adelante."
    have h4 := h3 x ?_
    Hint (hidden := true) "Puedes reescribir la definición de entorno métrico en `{h4}`."
    rw [def_entorno_metrico] at h4
    Hint (hidden := true) "`{h4}` te asegura la existencia de radios con ciertas
    propiedades, así que puedes elegir uno."
    choose d hd0 hd using h4
    Hint ( hidden := true) "Ahora, ¿qué radio puedes usar para demostrar la existencia
    que te piden?"
    use d
    Hint (hidden := true) "Puedes separar el objetivo en dos."
    fconstructor
    · Hint (hidden := true) "Tienes una hipótesis que dice exactamente lo que quieres ver."
      exact hd0
    . Hint (hidden := true) "Como quieres ver que algo es cierto para todo `y`,
      puedes tomar uno arbitrario."
      intro y hy
      Hint (hidden := true) "Observa que lo que quieres demostrar es, por definición
      lo mismo que decir que un cierto punto está en una cierta bola."
      apply hd
      Hint (hidden := true) "Lo que quieres demostrar es lo mismo que dice
      alguna de tus hipótesis."
      exact hy
    · Hint (hidden := true) "Prueba a reescribir la definición de estar en la preimagen de un
      conjunto."
      rw [def_preimagen]
      Hint (hidden := true) "Prueba a reescribir lo que significa estar en una bola."
      rw [def_bola]
      Hint (hidden := true) "Tienes una hipótesis que te premite reescribir la
      distancia entre un punto y sí mismo como cero."
      rw [d1]
      exact he0
