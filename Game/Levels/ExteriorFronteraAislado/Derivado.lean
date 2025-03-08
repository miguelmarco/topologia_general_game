import Game.Levels.ExteriorFronteraAislado.Aislado
World "ExteriorFronteraAislado"
Level 12
Title "Puntos aislados y derivado."

Introduction "Los puntos aislados de un conjunto `A` son
aquellos `x` para los que hay un abierto `U` tal que `U ∩ A = {x}`.


El derivado de un conjunto `A` son los puntos `x` tales que para todo
abierto `U` conteniendo a `x` , `( U \\ {x}) ∩ A ≠ ∅`."

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)



def derivado := {x : X | ∀ U ∈ abiertos,  x ∈ U →  ∃ y, y ≠ x ∧  y ∈ U ∩ A }


/--
El derivado de un conjunto `A` son los puntos `x` tales que para todo
abierto `U` conteniendo a `x` , `( U \ {x}) ∩ A ≠ ∅`
-/
DefinitionDoc derivado as "derivado"

theorem def_derivado:  derivado A =  {x : X | ∀ U ∈ abiertos, x ∈ U →  ∃ y , y ≠ x ∧  y ∈ U ∩ A } := by
  rfl

/--
`def_derivado A` dice que `derivado A =  {x : X | ∀ U ∈ abiertos,  x ∈ U →   ∃ y , y ≠ x ∧  y ∈ U ∩ A }`
-/
TheoremDoc topo.def_derivado as "def_derivado" in "lemas-definición"


NewTheorem topo.def_derivado

/--
Dado un conjunto `A`
`clausura_union_derivado_aislado` dice que `clausura A = derivado A ∪ aislados A` .
-/
TheoremDoc topo.clausura_union_derivado_aislado as "clausura_union_derivado_aislado" in "Exterior/Frontera/Aislado"

Statement clausura_union_derivado_aislado  : clausura A = derivado A ∪ aislados A := by
  Hint (hidden := true) "Para demostrar que dos conjuntos son iguales,
  lo natural es usar el principio de extensionalidad (con `ext`):
  tomar un elemento arbitrario y ver que está en uno de los conjuntos
  si y solo si está en el otro."
  ext x
  Hint (hidden := true) "Divide el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reescribir la caracterización
    de los elementos de la clausura en `{h}`."
    rw [caracterizacion_clausura] at h
    Hint (hidden := true) "Aquí habrá que razonar por casos: si `{x}`
    es un punto aislado de `{A}`, tendremos el objetivo, y si no lo es,
    podremos usar el lema que vimos en el nivel anterior.

    Separa la demostración, en el caso de que `{x}` sea punto interior de `{A}`
    y el caso en el que no, con `by_cases hcaso : {x} ∈ aislados {A}`."
    by_cases hcas : x ∈ aislados A
    · Hint (hidden := true) "En este caso, ¿`{x}` estará en el conjunto
      de la izquierda o en el de la derecha?"
      right
      exact hcas
    · Hint (hidden := true) "¿`{x}` está en el conjunto e la izquierda
      o en el de la derecha?"
      left
      Hint (hidden := true) "Puede ser útil reescribir la definición de derivado."
      rw [def_derivado]
      Hint (hidden := true) "También será útil reescribir `{hcas}` usando
      el teorema del nivel anterior (`no_aislado_sii`)."
      rw [no_aislado_sii] at hcas
      Hint (hidden := true) "Ahora `{hcas}` nos asegura
      que estamos en una de dos posibilidades. Separa la demostración en
      esos dos casos con `cases'`."
      cases' hcas with hcas1 hcas2
      · Hint (hidden := true) "Si te fijas, el objetivo afirma que
        algo debe cumplirse para todo abierto que contenga a `{x}`,
        toma uno arbitrario con `intro`."
        intro U hU hxU
        Hint (hidden := true) "Podemos obtener una nueva hipótesis (con
        `have`) si aplicamos `{h}` a `{U}`, `{hU}` y `{hxU}`."
        have h2 := h U hU hxU
        Hint (hidden := true) "Ahora `{h2}` nos asegura que existen unos
        puntos con ciertas propiedades. Puedes elegir uno con `choose`."
        choose y hyU hyA using h2
        Hint (hidden := true) "¿Qué punto puedes usar para demostrar que
        existe uno como te piden?"
        use y
        Hint (hidden := true) "Ahora hay que separar el objetivo en dos
        con `fconstructor`."
        fconstructor
        · Hint (hidden := true) "Para demostrar que algo no es cierto,
          lo habitual es suponer que lo es (con `intro`) y llegar
          a una contradicción."
          intro hyx
          Hint (hidden := true) "La contradicción vendrá por `{hcas1}`,
          puedes aplicarlo."
          apply hcas1
          Hint (hidden := true) "Ahora sólo tienes que usar `{hyx}`
          para reescribir."
          rw [hyx] at hyA
          exact hyA
        Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
        fconstructor
        · exact hyU
        · exact hyA
      · Hint (hidden := true) "Observa que el objetivo dice exactamente
        lo mismo que `{hcas2}`."
        exact hcas2
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "`{h}` nos asegura que `{x}` está en uno
    de dos conjuntos. Podemos tratar cada caso por separado con `cases'`."
    cases' h with h h
    · Hint (hidden := true) "Puede ser útil reescribir la definición de derivado."
      rw [def_derivado] at h
      Hint (hidden := true) "Puedes expresar el objetivo de otra forma gracias
      a la caracterización de los puntos de la clausura."
      rw [caracterizacion_clausura]
      Hint (hidden := true) "Puedes tomar un abierto arbitrario con `intro`."
      intro U hU hxU
      Hint (hidden := true) "Se puede obtener una nueva hipótesis (con `have`)
      aplicando `{h}` a `{U}`, `{hU}` y `{hxU}`."
      have h2 := h U hU hxU
      Hint (hidden := true) "Ahora `{h2}` asegura que existen puntos
      con ciertas propiedades. Elige uno con `choose`."
      choose y hyx hyAU using h2
      Hint (hidden := true) "¿Qué punto puedes usar?"
      use y
    · Hint (hidden := true) "Reescribe la definición de puntos
      aislados en `{h}`."
      rw [def_aislados] at h
      Hint (hidden := true) "Fíjate en que `{h}` te asegura
      que existe un cierto abierto. Elígelo con `choose`."
      choose U hU hUAx using h
      Hint (hidden := true) "Recuerda que la clausura de un conjunto siempre
      contiene al conjunto. "
      apply clausura_contiene
      Hint (hidden := true) "Puedes simplificar la expresión de `{hUAx}`."
      simp only [unipuntual_sii, mem_inter_iff, and_imp] at hUAx
      Hint (hidden := true) "Puedes separar `{hUAx}` en dos afirmaciones con `choose`
      o `cases'`."
      choose hxUA hyx using hUAx
      Hint (hidden := true) "Puedes obtener dos afirmaciones a partir
      de `{hxUA}` con `choose` o `cases'`."
      choose hxU hxA using hxUA
      exact hxA


end topo
