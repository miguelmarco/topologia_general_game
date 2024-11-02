import Game.Levels.Continuidad.ContinuidadBaseEntornos
open espacio_topologico Set


World "Continuidad"
Level 6
Title "Corolario de continuidad en términos de bases de entornos."

Introduction "Ahora vamos a ver una consecuencia directa de los
resultados anteriores: si tenemos una subbase de entornos
en el espacio de llegada, basta ver que se cumple la definición de
continuidad para entornos básicos.
"

variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)


/--
Si `f : X → Y` es una aplicación entre espacios topológicos, y para cada
`y` de `Y`,  `B y` es una base de entornos de `y`, `caracterizacion_continua_base_entornos` dice que
`continua f ↔ ∀ x, ∀ N ∈ B (f x), entorno x (f ⁻¹' N)`.
-/
TheoremDoc caracterizacion_continua_base_entornos as "caracterizacion_continua_en_base" in "Continuidad"

Statement caracterizacion_continua_base_entornos  (B : Y →  Set (Set Y)) (hB : ∀ y, base_de_entornos y (B y)) :
    continua f ↔ ∀ x, ∀ N ∈ B (f x), entorno x (f ⁻¹' N) := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente como hipótesis con `intro`."
    intro h
    Hint (hidden := true) "Puede set buen momento para reescribir
    la caracterización de continuidad en términos de continuidad puntual."
    rw [continua_sii_continua_en] at h
    Hint (hidden := true) "Puedes tomar un elemento arbitrario con `intro`."
    intro x
    Hint (hidden := true) "Fíjate que el objetivo se puede reescribir (al revés)
    como que `{f}` es continua en `{x}`."
    rw [← caracterizacion_continua_en_base]
    Hint (hidden := true) "Esto nos lo asegura el poder aplicar `{h}`."
    apply h
    Hint (hidden := true) "Antes hemos reescrito el objetivo suponiendo que
    `{B} ({f} {x})` es una base de entornos de `{x}`. Ahora tenemos que demostrarlo.
    Por suerte, podemos aplicar una hipótesis que lo garantiza."
    apply hB
  · Hint (hidden := true) "Ahora falta la otra mitad. Introduce el antecedente
    como de costumbre."
    intro h
    Hint (hidden := true) "Tenemos que volver a reescribir la continuidad
    en términos de continuidad puntual."
    rw [continua_sii_continua_en]
    Hint (hidden := true) "Ahora podemos tomar un punto arbitrario con `intro`."
    intro x
    Hint (hidden := true) "Fíjate en que podemos obtener una nueva hipótesis
    (con `have`) si particularizamos `{h}` en `{x}`."
    have h2 := h x
    Hint (hidden := true) "Ahora podemos reescribir en `{h2}` (al revés) la
    caracterización de continuidad puntual en términos de bases de entornos."
    rw [← caracterizacion_continua_en_base] at h2
    exact h2
    Hint (hidden := true) "Como antes, hemos supuesto que podiamos reescribir
    porque `{B} ({f} {x})` es una base de entornos de `{f} {x}`; y ahora
    tenemos que demostrarlo. Por fortuna, una hipótesis nos lo garantiza."
    apply hB
