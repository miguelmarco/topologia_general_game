import Game.Levels.Bases.BasesEntornosBase

open espacio_topologico Set


World "Bases"
Level 6
Title "Una base de entornos dada otra."

Introduction "Ahora vamos a ver que, si tenemos una familia $𝒟$ de entornos de un punto y
queremos comprobar si es una base de entornos, no hace falta comprobar la propiedad
de las bases de entornos para todo entorno del punto: basta hacerlo para los entornos
de otra base de entornos $ℬ$ dada.

Recuerda que puedes introducir $ℬ$ y $𝒟$ con `\\McB` y `\\McD` respectivamente.
"

variable {X : Type} [espacio_topologico X]





/--
Dado un punto $x$ y una base de entornos $ℬ$, una familia $𝒟$ de entornos de $x$ es base
de entornos de $x$ si y solo si $∀ B ∈ ℬ, ∃ D ∈ 𝒟, D ⊆ B$.
-/
TheoremDoc familia_entornos_base_sii as "familia_entornos_base_sii" in "Bases"

Statement familia_entornos_base_sii  (x : X) (ℬ 𝒟 : Set (Set X)) (hℬ : base_de_entornos x ℬ) (h𝒟 : ∀ D ∈  𝒟, entorno x D) :
    base_de_entornos x 𝒟 ↔ ∀ B ∈ ℬ, ∃ D ∈ 𝒟, D ⊆ B := by
  Hint (hidden := true) "Como de costumbre, una doble implicación se puede separar en dos implicaciones
  con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Como hay que demostrar una implicación, podemos introducir el
    antecedente como una nueva hipótesis, usando `intro`."
    intro h
    Hint (hidden := true) "Como hay que demostrar una afirmación para todo elemento de `{ℬ}`,
    habrá que tomar uno arbitrario con `intro`."
    intro B hB
    Hint (hidden := true) "Observa que {h} y {hℬ} nos dicen que ciertas familias son bases de entornos
    de `{x}`. Podemos desarrollar la definición de ser base de entornos usando `def_base_de_entornos`
    para reescribir esas hipótesis."
    rw [def_base_de_entornos] at h hℬ
    Hint (hidden := true) "Como `{h}` y `{hℬ}` están formadas por conjunciones, podemos
    separarlas en varias afirmaciones usando `choose` o `cases'`."
    choose h1 h2 using h
    choose h3 h4 using hℬ
    Hint (hidden := true) "Observa que `{h2}` podría aplicarse para dar exactamente lo que buscamos,
    y bastaría entonces ver que `{B}` es entorno de `{x}`."
    apply h2
    Hint (hidden := true) "Hay algunas hipótesis que nos aseguran que ciertos conjuntos son entornos
    de `{x}`. ¿Cual podemos aplicar en este caso?"
    apply h3
    Hint (hidden := true) "Ahora hay que demostrar algo que es exactamente una de las hipótesis."
    exact hB
  · Hint (hidden := true) "Como hay que demostrar una implicación, podemos introducir el
    antecedente como una nueva hipótesis, usando `intro`."
    intro h
    Hint (hidden := true) "Podemos reescribir el objetivo usando `def_base_de_entornos`."
    rw [def_base_de_entornos]
    Hint (hidden := true) "Como el objetivo es una conjunción, podemos separarlo en dos subobjetivos
    con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que el objetivo dice exactamente lo mismo que una hipótesis."
      exact h𝒟
    · Hint (hidden := true) "Como hay que demostrar algo para todo entorno de `{x}`, habrá que
      tomar uno arbitrarion con `intro`."
      intro N hN
      Hint (hidden := true) "Podemos reescribir el significado de `{hℬ}` con `def_base_de_entornos`"
      rw [def_base_de_entornos] at hℬ
      Hint (hidden := true) "Podemos separar las dos partes de `{hℬ}` con `choose` o `intro`."
      choose h1 h2 using hℬ
      Hint (hidden := true) "Ahora tenemos que encontrar un elemento de `{𝒟}` contenido en `{N}`.
      Párate a pensar cómo puedes conseguirlo con las hipótesis que tienes. ¿Qué nuevos
      objetos o hipótesis puedes obtener con lo que tienes?"
      Hint (hidden := true) "Observa que obtener una nueva hipótesis si aplicas `{h2}` a `{N}`
      y `{hN}`."
      have h3 := h2 N hN
      Hint (hidden := true) "Como `{h3} nos asegura que existen ciertos `B` con unas propiedades,
      podemos elegir uno con `choose`."
      choose B hB hB2 using h3
      Hint "Ahora sería tentados usar `{B}`, ya que sabemos que está contenido en `{N}`,
      pero fíjate en que no podemos asegurar que está en `{𝒟}`. ¿Cómo podemos obtener otro conjunto
      en {𝒟} que esté contenido en `{N}`?"
      Hint (hidden := true) "Observa podemos obtener una nueva afirmación aplicando `{h}` a `{B}` y `{hB}`."
      have h4 := h B hB
      Hint (hidden := true) "Ahora, gracias a `{h4}`, podemos elegir un cierto elemento de `{𝒟}`y sus propiedades
      con `choose`."
      choose D hD1 hD2 using h4
      Hint (hidden := true) "Ahora si podemos usar `{D}` para ver que existe un conjunto como nos pide
      el objetivo."
      use D
      Hint (hidden := true) "Para separar el objetivo en dos subobjetivos, usa `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Esto sabemos que es cierto porque es exactamente lo que nos
        asegura una de las hipótesis."
        exact hD1
      · Hint (hidden := true) "Para ver que un conjunto está contenido en otro, habrá que tomar
        un elemento arbitrario del mismo con `intro`."
        intro a ha
        Hint (hidden := true) "Observa que puedes aplicar `{hB2}`."
        apply hB2
        Hint (hidden := true) "Y ahora puedes aplicar `{hD2}`."
        apply hD2
        Hint (hidden := true) "Y ahora el objetivo es exactamente una de las hipótesis."
        exact ha
