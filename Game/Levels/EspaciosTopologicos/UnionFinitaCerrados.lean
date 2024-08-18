import Game.Levels.EspaciosTopologicos.UnionCerrados
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Finite

open espacio_topologico Set


World "EspaciosTopologicos"
Level 6
Title "La unión de una familia finita de cerrados es cerrado."

Introduction "Ahora vamos a generalizar el resultado anterior
a una cantidad finita de cerrados.

Hay dos posibles formas de afrontar este nivel: una es repetir el
argumento de inducción usado para la intersección finita de abiertos.

El otro es aplicar directamente `interseccion_finita_abiertos`.
Para poder hacerlo, hay que conseguir traducir la unión finita de cerrados
a una intersección finita de abiertos. Si usas este enfoque, te será
util usar el lema `Set.Finite.image`, que dice que la imagen de un conjunto
finite por una aplicación es finita.

También puede ser útil el resultado `Set.compl_sUnion`, que permite reescribir
el complementario de una unión como una intersección de los complementarios.
"

/--
Si `S` es un subconjunto finito de `X`, y tenemos una aplicación `f : X → Y`,
`Finite.image f S` nos dice que `f '' S` es finito.
-/
TheoremDoc Set.Finite.image as "Set.Finite.image" in "Utilidades"

/--
Si `F` es una familia de conjuntos, `compl_sUnion F` dice que el complementario
de la unión de `F` es igual a la intersección de los complementarios de los elementos de `F`.
-/
TheoremDoc Set.compl_sUnion as "Set.compl_sUnion" in "Utilidades"

variable {X : Type} [espacio_topologico X]

/--
Dada una familia finita de cerrados `F`, `⋃₀ F ∈ cerrados`.
-/
TheoremDoc union_finita_cerrados as "union_finita_cerrados" in "Espacios Topológicos"

NewTheorem Set.compl_sUnion Set.Finite.image

/--
Dada una familia finita de cerrados `F`, `⋃₀ F ∈ cerrados`.
-/
Statement union_finita_cerrados (F : Set (Set X)) (hF : Set.Finite F) (hC : F ⊆ cerrados) :
    ⋃₀ F ∈ cerrados := by
  Branch
    induction F , hF using Finite.dinduction_on
    · Hint (hidden := true) "Se puede simplificar la expresión."
      simp only [sUnion_empty]
      Hint (hidden := true) "Hay un resultado que dice exactamente lo que queremos."
      apply cerrado_vacio
    · Hint (hidden := true) "Se puede simplificar la expresión."
      simp only [sUnion_insert]
      Hint (hidden := true) "¿Qué podemos aplicar para ver que la unión de dos cerrados es un cerrado?"
      apply union_cerrados
      · Hint (hidden := true) "Sólo podemos aplicar una hipótesis para ver que `{a}` es un cerrado."
        apply hC
        Hint (hidden := true) "¿Cual de los dos casos es el que se cumple?"
        left
        Hint (hidden := true) "El resultado es cierto por definición."
        rfl
      · Hint (hidden := true) "Observa que una hipótesis implica exactamente lo que queremos."
        apply a_2
        Hint (hidden := true) "Usa la forma usual de ver que un conjunto está contenido en otro."
        intro C hCC
        Hint (hidden := true) "Sólo se puede aplicar una hipótesis."
        apply hC
        Hint (hidden := true) "¿Cual de las dos opciones es la que se cumple?"
        right
        exact hCC
  Hint (hidden := true) "Debes decidir cual de los dos posibles enfoques quieres usar: inducción o reescribir el enunciado."
  rw [def_cerrado]
  Hint (hidden := true) "Hay un resultado que permite reescribir el complementario de una unión como la intersección
  de los complementarios."
  rw [compl_sUnion]
  Hint (hidden := true) "Se puede aplicar un resultado que nos dice que,
  en ciertas condiciones, la intersección de una familia es un abierto."
  apply interseccion_finita_abiertos
  · Hint (hidden := true) "El lema `Finite.image` nos dice que la imagen
    de una familia finita es finita."
    apply Finite.image
    Hint (hidden := true) "Tenemos una hipótesis que dice exactamente lo que queremos."
    exact hF
  · Hint (hidden := true) "Puedes hacer lo habitual para ver que un conjunto está
    contenido en otro."
    intro U hU
    Hint (hidden := true) "`{hU}` nos dice que hay un cierto `C ∈ F` tal que `Cᶜ = U`. Prueba a elegirlo."
    choose C hCC hCU using hU
    Hint (hidden := true) "Ahora puedes usar `{hCU}` para reescribir el objetivo (cuidado con el sentido de la igualdad)."
    rw [← hCU]
    Hint (hidden := true) "Puedes reescribir el objetivo (de nuevo, cuidado con el orden)."
    rw [← def_cerrado]
    Hint (hidden := true) "Hay una hipótesis que se puede aplicar para ver que algo es un cerrado."
    apply hC
    exact hCC
