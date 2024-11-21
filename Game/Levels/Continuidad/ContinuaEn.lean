import Game.Levels.Continuidad.CaracterizacionContinuaCerrados

World "Continuidad"
Level 3
Title "Continuidad puntual."

Introduction "Introducimos ahora el concepto de continuidad puntual.

Una aplicación `f : X → Y` entre espacios topológicos se dice
*continua en un punto* `x : X` si la preimagen de cualquier entorno de `f x`
es entorno de `x`.
"
namespace topo
open topo espacio_topologico Set
variable {X Y: Type} [espacio_topologico X] [espacio_topologico Y] (f : X → Y)

def continua_en (x : X) := ∀ N , entorno (f x) N → entorno x (f ⁻¹' N)

/--
Una aplicación `f : X → Y` entre espacios topológicos se dice
*continua en un punto* `x : X` si la preimagen de cualquier entorno de `f x`
es entorno de `x`.
-/
DefinitionDoc continua_en as "continua_en"

theorem def_continua_en (x : X) : continua_en f x ↔ ∀ N , entorno (f x) N → entorno x (f ⁻¹' N) := by rfl

/--
Si `f : X → Y` es una aplicación entre espacios topológicos y `x` es un
punto de `X`, `def_continua_en f x` dice que `continua_en f x ↔ ∀ N , entorno (f x) N → entorno x (f ⁻¹' N)`.
-/
TheoremDoc topo.def_continua_en as "def_continua_en" in "Continuidad"

NewTheorem topo.def_continua_en

/--
`f : X → Y` es una aplicación entre espacios topológicos, `continua_sii_continua_en f`
dice que `continua f ↔ ∀ x, continua_en f x`.
-/
TheoremDoc topo.continua_sii_continua_en as "continua_sii_continua_en" in "Continuidad"

/--
Una aplicación es continua si y solo si es continua en todo punto.
-/
Statement continua_sii_continua_en : continua f ↔ ∀ x, continua_en f x := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    intro x
    Hint (hidden := true) "Puede ser útil reescribir las definiciones
    de continuidad y continuidad en un punto."
    rw [def_continua] at h
    rw [def_continua_en]
    Hint (hidden := true) "Toma un entorno arbitrario con `intro`."
    intro Y hY
    Hint (hidden := true) "Prueba a reescribir la definición de entorno
    donde puedas"
    rw [def_entorno] at hY ⊢
    Hint (hidden := true) "Como `{hY}` te asegura que existen ciertos
    abiertos, puedes elegir uno de ellos (y sus correspondientes
    propiedades) con `choose`."
    choose U hUab hfxU hUY using hY
    Hint (hidden := true) "¿Qué abierto puedes usar para demostrar
    que existe uno como quieres?"
    use f ⁻¹' U
    Hint (hidden := true) "Separa el objetivo en subobjetivos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que `{h}` implica el objetivo, así
      que puedes aplicarlo."
      apply h
      Hint (hidden := true) "Ahora el objetivo es exactamente una de tus hipótesis."
      exact hUab
    Hint (hidden := true) "Separa el objetivo en subobjteivos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puede ser útil simplificar la expresión con `simp`."
      simp only [mem_preimage]
      Hint (hidden := true) "Ahora el objetivo es exactamente una de tus hipótesis."
      exact hfxU
    · Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
      lo normal es tomar un elemento arbitrario del primero (con `intro`)."
      intro y hY
      Hint (hidden := true) "Puede ser útil simplificar la expresión."
      simp
      Hint (hidden := true) "Ahora puedes aplicar `{hUY}`."
      apply hUY
      Hint (hidden := true) "Observa que `{hY}` dice exactamente lo que pide el objetivo."
      exact hY
  · Hint (hidden := true) "Puedes asumir el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes tomar un elemento arbitrario con `intro`."
    intro U hU
    Hint (hidden := true) "Como para poder usar `{h}` necesitamos un punto,
    hay que expresar el ser abierto en términos de puntos. ¿Recuerdas qué
    teorema decía algo así?"
    Hint (hidden := true) "`rw [abierto_sii_entorno]`"
    rw [abierto_sii_entorno]
    Hint (hidden := true) "Ahora ya puedes tomar un punto arbitrario con `intro`."
    intro x hx
    Hint (hidden := true) "Puedes obtener una nueva hipótesis particularizando
    `{h}` a `{x}`."
    Hint (hidden := true) "`have h2 := {h} {x}`"
    have h2 := h x
    Hint (hidden := true) "Puede ser útil reescribir la definición de continuidad
    en un punto en `{h2}`."
    rw [def_continua_en] at h2
    Hint (hidden := true) "Observa que `{h2}` implica el objetivo. Aplícala
    (con `apply`) para que el objetivo pase a ser demostrar las condiciones de `{h2}`."
    apply h2
    Hint (hidden := true) "Puede ser útil reescribir la definición de entorno."
    rw [def_entorno]
    Hint (hidden := true) "¿Qué abierto puedes usar para demostrar que existe uno?"
    use U
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Observa que hay una hipótesis que dice exactamente lo que quieres.
      (Puedes probar a simplificar las hipótesis si no lo ves claro)."
      exact hx
    · Hint (hidden := true) "Este contenido es trivial."
      trivial

end topo
