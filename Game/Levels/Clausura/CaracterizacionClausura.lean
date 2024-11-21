import Game.Levels.Continuidad.ContinuaAbiertaBaseEntorno

World "Clausura"
Level 1
Title "Clausura"

Introduction "La clausura de un conjunto es la intersección de todos
los cerrados que lo contienen.

Veamos qué cumplen los puntos de la clausura.

Para esta demostración necesitaremos una nueva táctica, que permite
hacer *demostraciones por contradicción*: la táctica `by_contra`.

Si tienes como objetivo una afirmación (por ejemplo `P`), la táctica
`by_contra hn` introducirá una nuebva hipótesis `hn : ¬ P` negando
el objetivo, y el nuevo objetivo será `False`. Es decir, habrá que demostrar
una contradicción, suponiendo que el objetivo es falso.
"

/--
Si tienes como objetivo una afirmación (por ejemplo `P`), la táctica
`by_contra hn` introducirá una nuebva hipótesis `hn : ¬ P` negando
el objetivo, y el nuevo objetivo será `False`. Es decir, habrá que demostrar
una contradicción, suponiendo que el objetivo es falso.
-/
TacticDoc by_contra

NewTactic by_contra

TheoremTab "Clausura"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X]

def clausura (A : Set X) := ⋂₀ { C ∈ cerrados | A ⊆ C}

/--
Si $A$ es un subconjunto de un espacio topológico, la *clausura*
de $A$ es la intersección de los cerrados que contienen a $A$.
-/
DefinitionDoc clausura as "clausura"


/--
Si `A` es un conjunto en un espacio topológico, `def_clausura A` dice
que `clausura A = ⋂₀ { C ∈ cerrados | A ⊆ C}`.
-/
TheoremDoc topo.def_clausura as "def_clausura" in "lemas-definición"

theorem def_clausura (A : Set X) : clausura A = ⋂₀ { C ∈ cerrados | A ⊆ C} := by rfl

NewTheorem topo.def_clausura

NewDefinition clausura

/--
Un punto `x` está en la clausura de `A` si y sólo si todo
abierto que lo contenga, interseca a `A`.
-/
TheoremDoc topo.caracterizacion_clausura as "caracterizacion_clausura" in "Clausura"

Statement caracterizacion_clausura (A : Set X) (x : X) : x ∈ clausura A ↔ ∀ U ∈ abiertos, x ∈ U → ∃ y, y ∈ U ∩ A := by
  Hint (hidden := true) "Puedes separar el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente, y un abierto arbitrario con `intro`."
    intro h
    intro U hU hxU
    Hint "Ahora es el momento de usar la demostración por contradicción.
    Teclea `by_contra hn`, y verás como te aparece una nueva hipótesis `hn` negando el objetivo,
    y el objetivo pasará a ser `False` (es decir, habrá que ver una contradicción)."
    by_contra hn
    Hint "Puedes simplificar la hipótesis que da la contradicción con `simp at {hn}`."
    simp only [mem_inter_iff, not_exists, not_and] at hn
    Hint (hidden := true) "Puedes reescribir la definición de clausura en `{h}`."
    rw [def_clausura] at h
    Hint "En este punto, la contradicción vendrá porque podemos demostrar que `{x} ∈ {U}ᶜ`.
    Inicia ese subobjetivo con `have hxUc : {x} ∈ {U}ᶜ`."
    have haux2 : x ∈ Uᶜ
    · Hint (hidden := true) "Observa que la razón por la que podemos
      demostrar esto es gracias a `{h}`, así que puedes aplicarla con `apply`."
      apply h
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Reescribe la definición de cerrado."
        rw [def_cerrado]
        Hint (hidden := true) "Simplifica el objetivo con `simp`."
        simp
        exact hU
      · Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
        introduce un elemento arbitrario con `intro` (y asegurate de no elegir un
        nombre que ya esté en uso)."
        intro y hy
        Hint  "La forma de demostrar que un elemento **no** está en un conjunto,
        es suponer que sí lo está (con `intro`) y llegar a una contradicción."
        intro hyU
        Hint (hidden := true) "Observa que la contradicción vendrá por el hecho
        de particularizar `{hn}` a `{y}` y `{hyU}`."
        have hyA := hn y hyU
        Hint "Ahora está claro que la contradicción viene de `{hyA}`y `{hy}`.

        Puedes, o bien aplicar la negación (`apply {hyA}`), o directamente dar la
        contradicción con `exact {hyA} {hy}`."
        exact hyA hy
    Hint  "Ahora que sabemos `{haux2}`, tenemos una contradicción con `{hxU}`.

    Puedes demostrar la contradicción con `apply `{haux2}`."
    apply haux2
    exact hxU
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes reescribir la definición de clausura."
    rw [def_clausura]
    Hint  "De nuevo, podemos usar demostración por contradicción. Teclea
    `by_contra hn`; y así introducirás una hipótesis consistente en la negación
    del objetivo, y el nuevo objetivo será demostrar una contradicción."
    by_contra hn
    Hint  "Simplifica la expresión `{hn}` con `simp at `{hn}`."
    simp only [mem_sInter, mem_setOf_eq, and_imp, not_forall, exists_prop, exists_and_left] at hn
    Hint (hidden := true) "`{hn}` te asegura que existen cerrados
    con ciertas propiedades. Puedes elegir uno con `choose`."
    choose C hC hAC hxC using hn
    Hint (hidden := true) "Observa que puedes particularizar `{h}`
    para `{C}`ᶜ, usando `have`."
    have h2 := h Cᶜ hC hxC
    Hint (hidden := true) "`{h2}` te dice que existen puntos con ciertas
    propiedades, elige uno con `choose`."
    choose y hyC hyA using h2
    Hint "Ahora ya tienes prácticamente la contradicción, como `{hyC}`
    te dice que `{y}` no está en `{C}`, podemos dar una contradicción
    probando que `{y} ∈ {C}`. Teclea `apply {hyC}` para que el objetivo pase a ser ese."
    apply hyC
    apply hAC
    exact hyA

end topo
