import Game.Levels.EspaciosMetricos.ComposicionContinuas

open Set


World "EspaciosTopologicos"
Level 1
Title "Intersección finita de abiertos."

Introduction "En este nivel vamos a introducir la definición de espacio
topológico, que imita algunas propiedades de los espacios métricos.

Un espacio topológico es un conjunto ambiente $X$ junto con una familia
de subconjuntos $\\mathcal{T}$ (llamados **abiertos** )
que cumple las siguientes propiedades:

1. El conjunto vacío y el conjunto total $X$ son abiertos.
2. Dada una familia cualquiera de conjuntos abiertos, su unión es un conjunto abierto.
3. Dados dos conjuntos abiertos, su intersección es un conjunto abierto.

Veamos ahora que la tercera condición se puede generalizar a la intersección
de una cantidad finita de conjuntos abiertos.
"

class espacio_topologico (X : Type) where
  abiertos : Set (Set X)
  abierto_vacio : ∅ ∈ abiertos
  abierto_total : univ ∈ abiertos
  union_abiertos (F : Set (Set X)) : F ⊆ abiertos → ⋃₀ F ∈ abiertos
  interseccion_abiertos (A B : Set X) (hA : A ∈ abiertos) (hB : B ∈ abiertos) : A ∩ B ∈ abiertos

open espacio_topologico


TheoremTab "Espacios Topológicos"

/--
Un espacio topológico es un conjunto ambiente `X` junto con una familia
de subconjuntos (llamada `abiertos`) que satisface `abierto_vacio`,
`abierto_total`, `union_abiertos` e `interseccion_abiertos`.
-/
DefinitionDoc espacio_topologico as "espacio_topologico"

/--
En un espacio topológico `X`, se tiene `∅ ∈ abiertos`.
-/
DefinitionDoc espacio_topologico.abierto_vacio as "abierto_vacio"

/--
En un espacio topológico `X`, se tiene `univ ∈ abiertos`.
-/
DefinitionDoc espacio_topologico.abierto_total as "abierto_total"

/--
En un espacio topológico `X`, dada una familia `F : Set (Set X)` tal que
`F ⊆ abiertos`, se tiene `⋃₀ F ∈ abiertos`.
-/
DefinitionDoc espacio_topologico.union_abiertos as "union_abiertos"

/--
En un espacio topológico `X`, dados dos conjuntos `U V` tales
que `U ∈ abiertos` y `V ∈ abiertos`, se tiene `U ∩ V ∈ abiertos`.
-/
DefinitionDoc espacio_topologico.interseccion_abiertos as "interseccion_abiertos"

NewDefinition espacio_topologico espacio_topologico.abierto_vacio espacio_topologico.abierto_total espacio_topologico.union_abiertos espacio_topologico.interseccion_abiertos

/--
Sea `X` un espacio topológico, y `F` una familia finita de conjuntos abiertos,
entonces `⋂₀ F` es un abierto.
-/
TheoremDoc interseccion_finita_abiertos as "interseccion_finita_abiertos" in "Espacios Topológicos"

/--
Sea `X` un espacio topológico, y `F` una familia finita de conjuntos abiertos,
entonces `⋂₀ F` es un abierto.
-/
Statement interseccion_finita_abiertos {X : Type} [espacio_topologico X] (F : Set (Set X)) (hFfin : Set.Finite F) (hFab : F ⊆ abiertos) :
    ⋂₀ F ∈ abiertos := by
  Hint (hidden := true) "Recuerda que en el mundo anterior hiciste una prueba similar usando inducción."
  induction F, hFfin using Set.Finite.dinduction_on
  · Hint (hidden := true) "Prueba a simplificar la expresión."
    simp only [sInter_empty]
    Hint (hidden := true) "Por definición, hay una propiedad que asegura el objetivo."
    exact abierto_total
  · Hint (hidden := true) "Prueba a simplificar el resultado."
    simp only [sInter_insert]
    Hint (hidden := true) "Hay un axioma que se puede aplicar para asegurar que la intersección
     de dos conjuntos es un abierto."
    apply interseccion_abiertos
    · Hint (hidden := true) "Observa que se puede aplicar una de las hipótesis."
      apply hFab
      Hint (hidden := true) "Recuerda que el objetivo dice que debe darse una de dos opciones.
      ¿Cual se da? ¿La primera o la segunda?"
      left
      Hint (hidden := true) "El resultado es ahora trivial."
      rfl
    · Hint (hidden := true) "Observa que una de las hipótesis de inducción implica el objetivo."
      apply a_2
      Hint (hidden := true) "Una forma de ver que un conjunto está contenido en otro es tomar un
      elemento del primero y ver que debe estar en el segundo."
      intro U hU
      Hint (hidden := true) "¿Qué hipótesis se puede aplicar para garantizar que un cierto conjunto
      es abierto?"
      apply hFab
      Hint (hidden := true) "Recuerda que el objetivo dice que debe darse una de dos opciones.
      ¿Cual se da? ¿La primera o la segunda?"
      right
      Hint (hidden := true) "Ahora el objetivo es exactamente una de las hipótesis."
      exact hU
