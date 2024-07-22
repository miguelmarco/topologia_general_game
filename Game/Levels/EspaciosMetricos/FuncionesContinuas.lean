import Game.Levels.EspaciosMetricos.CaracterizacionEntornosMetricos

variable {X : Type} {Y : Type} [espacio_metrico X] [espacio_metrico Y]
open espacio_metrico

World "EspaciosMetricos"
Level 10
Title "Funciones contínuas entre espacios métricos."

Introduction "En este nivel vamos a tratar el concepto de función contínua entre espacios métricos.

Dados dos espacios métricos $(X,d_X)$, $(Y,d_Y)$ y $x \\in X$, una aplicación $f : X \\to Y$ se dice que es
$(d_X,d_Y)-contínua$ en $x$ si

$\\forall \\epsilon > 0, \\exists \\delta>0$ tal que
\\forall $y \\in X$, $d_X(x,y) < \\delta \\Longrightarrow d_Y(f(x),f(y)) < \\epsilon$.

Si una función es $(d_X,d_Y)-contínua$ en todo $x$, se dice símplemente que es $(d_X,d_Y)-contínua$.

Vamos a ver una caracterización de la continuidad de funciones entre espacios métricos en términos
de bolas. Para ello vamos a tener que trabajar con la *imagen de un conjunto por una función*:
Dada una función $f : X \\to Y$ y un conjunto $S \\subseteq X$, la imagen de $S$ por $f$ es el
conjunto $\\{ f(x) ∣ x \\in S}$. En Lean esto se denota como `f '' S`. El lema `def_imagen_conjunto`
caracteriza esto.
"

def d_continua_en (f : X → Y) (x : X) := ∀ ε > 0, ∃ δ > 0, ∀ y, d x y < δ → d (f x) (f y) < ε

lemma def_d_continua_en (f : X → Y)  (x : X) :
    d_continua_en f x  ↔ ∀ ε > 0, ∃ δ > 0, ∀ y, d x y < δ → d (f x) (f y) < ε := by
  rfl

def d_continua (f : X → Y) := ∀ x, d_continua_en f x

lemma def_d_continua (f : X → Y) : d_continua f ↔ ∀ x, d_continua_en f x := by
  rfl

lemma def_imagen_conjunto {X : Type} {Y : Type} (f : X → Y) (S : Set X) (y : Y) : y ∈ f '' S ↔ ∃ x, x ∈ S ∧ f x = y := by
  rfl

/--
Dados dos espacios métricos $(X,d_X)$, $(Y,d_Y)$ y $x \in X$, una aplicación $f : X \to Y$ se dice que es
$(d_X,d_Y)-contínua$ en $x$ si

$\forall \epsilon > 0, \exists \delta>0$ tal que \forall $y \in X$, $d_X(x,y) < \delta \Longrightarrow d_Y(f(x),f(y)) < \epsilon$.
-/
DefinitionDoc d_continua_en as "d_continua_en"

/--
Dada una función `f : X → Y` entre espacios métricos, y un elemento `x : X`; `def_d_continua_en` es
una prueba de que `f` es `d_continua_en` `x` si y sólo si `∀ ε > 0, ∃ δ > 0, ∀ y, d x y < δ → d (f x) (f y) < ε`.
-/
TheoremDoc def_d_continua_en as "def_d_continua_en" in "lemas-definición"

/--
Dados dos espacios métricos $(X,d_X)$, $(Y,d_Y)$, una aplicación $f : X \to Y$ se dice que es
$(d_X,d_Y)-contínua$ si  es $(d_X,d_Y)-contínua$ en todo $x \in X$.
-/
DefinitionDoc d_continua as "d_continua"

/--
Dada una función `f : X → Y` entre espacios métricos, `def_d_continua f` es una prueba de que
`d_continua f ↔ ∀ (x : X), d_continua_en f x`.
-/
TheoremDoc def_d_continua as "def_d_continua" in "lemas-definición"

/--
Dada una aplicación `f : X → Y`, `S : Set X` e `y : Y`, `def_imagen_conjunto f S y` es una prueba
de que `y ∈ f '' S ↔ ∃ x, x ∈ S ∧ f x = y`.
-/
TheoremDoc def_imagen_conjunto as "def_imagen_conjunto" in "lemas-definición"

NewDefinition d_continua_en d_continua
NewTheorem def_d_continua_en def_d_continua def_imagen_conjunto

/--
Dada una aplicación `f : X → Y` entre dos espacios métricos `x : X`, `caracterizacion_d_continua_en_bola f x`
es una prueba de que `d_continua_en f x ↔ ∀ ε >0 , ∃ δ > 0, f '' (bola x δ) ⊆ bola (f x) ε`.
-/
TheoremDoc caracterizacion_d_continua_en_bola as "caracterizacion_d_continua_en_bola" in "Espacios Métricos"

/--
Dados espacios métricos $(X, d_X)$, $(Y,d_Y)$, un punto $x \in X$, una aplicación $f : X \to Y$ es
$(d_X,d_Y)$ contínua en $x$ si y sólo si para todo $\epsilon > 0$ existe un $\delta >0$ tal que
$f(\mathbb{B}(x,δ)) \subseteq \mathbb{B}(f(x),\epsilon)$.
-/
Statement caracterizacion_d_continua_en_bola (f : X → Y) (x : X) :
    d_continua_en f x ↔ ∀ ε >0 , ∃ δ > 0, f '' (bola x δ) ⊆ bola (f x) ε := by
  Hint (hidden := true) "Al ser el objetivo una doble implicación, habrá que separarla en dos implicaciones."
  fconstructor
  · Hint (hidden := true) "Puedes empezar introduciendo la hipótesis del enunciado que quieres probar."
    intro h
    Hint (hidden := true) "Para demostrar que un enunciado es cierto para todo valor, lo habitual es tomar
    uno arbitrario."
    intro ε hε
    Hint (hidden := true) "Tal vez sea útil reescribir la definición de continuidad en un punto."
    Branch
      rw [def_d_continua_en] at h
      Hint (hidden := true) "Como tienes que `{h}` se cumple para todo valor positivo, puedes obtener
      una nueva afirmación particularizando para un valor positivo que conoces."
      Hint (hidden := true) "have he := {h} {ε} {hε} te dará el caso particular de `{h}` para `{ε}`."
    have haux := h ε hε
    Hint (hidden := true) "Como sabes que existen valores de `δ` que cumplen ciertas propiedades, puedes
    elegir uno de ellos."
    Hint (hidden := true) "`choose δ hδpos hδ using {haux}` te dará un `δ` y las propiedades que cumple."
    choose δ hδpos hδ using haux
    Hint (hidden := true) "¿Qué valor puedes usar para demostrar que existe un `δ > 0` como te pide el objetivo?"
    Hint (hidden := true) "Prueba `use {δ}`."
    use δ
    Hint (hidden := true) "De nuevo, habrá que separar el objetivo en varios."
    fconstructor
    · exact hδpos
    · Hint (hidden := true) "Para ver que un conjunto está contenido en otro, hay que tomar un elemento
      que esté en el primero, y ver que está en el segundo."
      intro y hy
      Hint (hidden := true) "Prueba a reescribir la definición de estar en la imagen de un conjunto en `{hy}`"
      rw [def_imagen_conjunto] at hy
      Hint (hidden := true) "Como sabes que existen algunos `x_1` con ciertas propiedades, puedes elegir uno."
      choose x1 hx1 hx1y using hy
      Branch
        rw [def_bola]
        rw [def_bola] at hx1
        have haux2 := hδ x1 hx1
        rw [hx1y] at haux2
        exact haux2
      Hint (hidden := true) "Ahora parece que te gustaría sustituir `{y}` por `f x1` en el objetivo, gracias
      a `hx1y`. Pero esta igualdad produciría el resultado opuesto (es decir, cambiar `f x1` por `y`).
      Recuerda que hay un modo de usar táctica `rw` para hacer sustituciones en el sentido contrario."
      rw [← hx1y]
      Hint (hidden := true) "Podría ser útil reescribir la definición de estar en una bola."
      rw [def_bola]
      Hint (hidden := true) "Ahora puedes aplicar una de tus hipótesis."
      apply hδ
      Hint (hidden := true) "Observa que `{hx1}` dice esencialmente lo mismo que el objetivo."
      exact hx1
  · Hint "Ahora probemos la implicación en sentido contrario."
    intro h
    Hint (hidden := true) "Puedes empezar desarrollando la definición de continuidad en un punto."
    rw [def_d_continua_en]
    Hint (hidden := true) "Como antes, habrá que empezar tomando un valor arbitrario."
    intro ε hε
    Hint (hidden := true) "Se puede aplicar `{h}` al caso particular que has tomado."
    have haux := h ε hε
    Hint (hidden := true) "Sabiendo que existen valores `δ` con ciertas propiedades, puedes elegir uno."
    choose δ hδpos hδ using haux
    Hint (hidden := true) "Necesitas demostrar que existe un valor con ciertas propiedades. ¿Cual puedes usar?"
    use δ
    Hint (hidden := true) "De nuevo, habrá que separar el objetivo en varios."
    fconstructor
    · exact hδpos
    · Hint (hidden := true) "De nuevo, para demostrar que algo se cumple para todo objeto con ciertas
      propiedades, hay que tomar uno arbitrario y demostrarlo para ese caso concreto."
      intro y hy
      Hint (hidden := true) "Ahora parece que la hipótesis que te puede ser útil es `{hδ}`, pero
      está escrita en términos de bolas, y tu objetivo en términos de distancias. ¿Se te ocurre qué puedes hacer?"
      rw [← def_bola]
      apply hδ
      Hint (hidden := true) "Puedes desarrollar qué significa que `{f} {y}` esté en `{f} '' bola {x} {δ}`."
      rw [def_imagen_conjunto]
      Hint (hidden := true) "Debes demostrar que existe un cierto valor. ¿Cual puede ser?"
      use y
      Hint (hidden := true) "Ahora solo queda separar el objetivo en dos subobjetivos fáciles."
      fconstructor
      · exact hy
      · rfl
