import Game.Levels.Bases.FamiliaBaseSii

open espacio_topologico Set


World "Bases"
Level 5
Title "Bases de entornos."

Introduction "En un espacio topológico $(X,𝓣)$ Una familia $ℬ^x$ asociada a cada punto $x$
es una *base de entornos* de $x$ si todos ellos son entornos de $x$, y todo entorno $N$
de $x$ tiene un elemento de $ℬ^x$ contenido en él.

Veamos ahora que si tenemos una base de entornos abiertos para cada punto,
podemos formar una base de la topología.
"

variable {X : Type} [espacio_topologico X]


/--
En un espacio topológico $(X,𝓣)$, una *base de entornos* de un punto *x*
es una familia $ℬ^x$ de entornos de $x$ tal que para todo $N$ entorno de $x$,
existe un $B ∈ 𝓑$ tal que $N ⊆ B$
-/
def base_de_entornos (x : X) (ℬ : Set (Set X)) := (∀ B ∈ ℬ, entorno x B) ∧ ∀ (N : Set X), entorno x N → ∃ B ∈ ℬ, B ⊆ N

/--
En un espacio topológico $(X,𝓣)$, una *base de entornos* de un punto *x*
es una familia $ℬ^x$ de entornos de $x$ tal que para todo $N$ entorno de $x$,
existe un $B ∈ 𝓑$ tal que $N ⊆ B$
-/
DefinitionDoc base_de_entornos as "base_de_entornos"

NewDefinition base_de_entornos


/--
Si para cada punto $x ∈ X$ tenemos una base de entornos abiertos $ℬ x$,
entonces la unión de todas ellas es una base de la topología.
-/
TheoremDoc base_de_base_de_entornos_abiertos as "base_de_base_de_entornos_abiertos" in "Espacios Topológicos"

Statement base_de_base_de_entornos_abiertos  (ℬ : X → Set (Set X)) (hab : ∀ (x : X), ℬ x ⊆ abiertos) (hent : ∀ x, base_de_entornos x (ℬ x)) :
    base (⋃₀ {(ℬ x) | x : X}) := by
  Hint (hidden := true) "Puede ser útil reformular el objetivo usando la caracterización de las bases."
  rw [caracterizacion_base]
  Hint (hidden := true) "Ahora hay que demostrar que la familia está formada por abiertos, y que se cumple
  la propiedad para cada punto. Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Para demostrar un contenido de conjuntos, habrá que tomar
    un elemento arbitrario dle primero. Usa `intro U hU`."
    intro U hU
    Hint (hidden := true) "Como `{hU}` nos dice que `{U}` está en una unión,
    podemos elegir un conjunto al que pertenece, usando `choose`."
    choose Bx hxB hUBx using hU
    Hint (hidden := true) "`{hxB}` nos dice que existe un punto tal que `{Bx}`
    es su correspondiente base de entornos, puedes elegir ese punto con `choose`."
    choose x hx using hxB
    Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando `{hab}` a `{x}` (usando la táctica `have`)."
    have h2 := hab x
    Hint (hidden := true) "La hipótesis `{h2}` se puede aplicar para ver que `{U}` es abierto."
    apply h2
    Hint (hidden := true) "Fíjate en que puedes usar `{hx}` para reescribir el objetivo."
    rw [hx]
    Hint (hidden := true) "El objetivo es ahora exactamente igual que una hipótesis."
    exact hUBx
  · Hint (hidden := true) "Como quieres demostrar algo para todo abierto y todo punto,
    puedes introducir unos arbitrarios."
    intro U hU x hxU
    Hint (hidden := true) "Puedes obtener una nueva hipótesis particularizando `{hent}` a `{x}`."
    Hint (hidden := true) "Teclea `have hent2 := hent x`."
    have hent2 := hent x
    Hint (hidden := true) "Fíjate en que `{hent2}` es en realidad dos afirmaciones
    (que `{ℬ} {x}` está formado por entornos de `{x}`, y que todo entorno de `{x}` admite
    un elemento de `{ℬ} {x}` intermedio). Puedes separarla en estas dos afirmaciones con `choose`
    o `cases'`."
    choose hent1 hent2 using hent2
    Hint (hidden := true) "Puede ser útil reescribir `{hU}` en términos
    de entornos."
    Hint (hidden := true)  "Puedes usar `abierto_sii_entorno`."
    rw [abierto_sii_entorno] at hU
    Hint (hidden := true)  "Como se cumple `{hxU}`, podemos obtener una nueva hipótesis sobre `U`
    gracias a `{hU}`."
    Hint (hidden := true) "Usa `have hUentx := {hU} {x} {hxU}`."
    have hUentx := hU x hxU
    Hint (hidden := true)  "Ahora podemos particularizar `{hent2}` al caso de `{U}
    gracias a `{hUentx}`."
    Hint (hidden := true)  "Usa `have h3 := {hent2} {U} {hUentx}`."
    have h3 :=  hent2  U hUentx
    Hint (hidden := true)  "Gracias a `{h3}` puedes elegir un `B` y sus propiedades."
    choose B hB hBU using h3
    Hint (hidden := true)  "Como tienes que demostrar que existe un cierto elemento
    de una familia, ¿ves cual puedes usar?."
    Hint (hidden := true) "`use {B}`."
    use B
    Hint (hidden := true) "Ahora tienes que separar el objetivo en varias afirmaciones con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Hay que demostrar que `{B}` pertenece a una unión, es decir,
      que está en alguno de los conjuntos que se unen. ¿Cual puedes usar?."
      Hint (hidden := true)  "`use {ℬ} {x}` (puedes teclear ℬ tecleando `\\McB`)."
      use ℬ x
      Hint (hidden := true) "De nuevo hay que separar el objetivo en varios."
      fconstructor
      · Hint (hidden := true) "Fíjate en que el objetivo te pide demostrar que existe
        un cierto punto. ¿Cual puedes usar?."
        use x
      · Hint (hidden := true)  "El objetivo es exactamente igual a una hipótesis."
        exact hB
    · Hint (hidden := true) "De nuevo hay que separar el objetivo."
      fconstructor
      · Hint (hidden := true) "Recuerda que ya probamos que un entorno de un punto contiene al punto."
        Branch
          have h4 := hent1  B hB
          Hint (hidden := true)  "Recuerda lo que significa ser entorno. Puedes reescribirlo
          usando `def_entorno` en `{h4}`."
          rw [def_entorno] at h4
          Hint (hidden := true)  "Gracias a `{h4}` sabemos que existe un cierto abierto,
          puedes tomarlo (junto con sus propiedades) con `choose`."
          choose V hVab hxV hVB using h4
          Hint (hidden := true) "Ahora puedes aplicar `{hVB}`."
          apply hVB
          exact hxV
        apply entornos_N2
        Hint (hidden := true) "Fíjate en que puedes aplicar `{hent1}`."
        apply hent1
        Hint (hidden := true)  "Ya tenemos una hipótesis que nos da el resultado."
        exact hB
      · exact hBU
