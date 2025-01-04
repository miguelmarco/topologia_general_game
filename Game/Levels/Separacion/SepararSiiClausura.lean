import  Game.Levels.Numerabilidad.ContinuaLimite

World "Separacion"
Level 1
Title "Separar conjuntos"

Introduction "Decimos que dos conjuntos $A, B$ *se pueden separar*
si existen dos abiertos $U, V$ tales que $A ⊆ U$, $B ⊆ V$ y $U ∩ V = ∅$.

Esto lo denotamos en Lean como `puede_separar A B`. El teorema
`def_puede_separar` dice exactamente eso.

Veamos ahora una caracterización de este hecho en términos de clausuras.
"

namespace topo

open topo Set espacio_topologico

variable {X : Type} [espacio_topologico X]

TheoremTab "Separación"

/--
Dados dos conjuntos `A` y `B`, decimos que `puede_separar A B` si
existen dos abiertos disjuntos que los contienen.
-/
DefinitionDoc puede_separar as "puede_separar"

def puede_separar (A B : Set X) := ∃ (U V : Set X), U ∈ abiertos ∧ V ∈ abiertos ∧ A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅


/--
Dados dos conjuntos `A` y `B`, `def_puede_separar A B` dice que
`puede_separar A B ↔ ∃ (U V), U ∈ abiertos ∧ V ∈ abiertos ∧ A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅`
-/
TheoremDoc topo.def_puede_separar as "def_puede_separar" in "Separación"


theorem def_puede_separar (A B : Set X) : puede_separar A B ↔ ∃ (U V : Set X), U ∈ abiertos ∧ V ∈ abiertos ∧ A ⊆ U ∧ B ⊆ V ∧ U ∩ V = ∅  := by
  rfl

NewTheorem topo.def_puede_separar

NewDefinition puede_separar

/--
Dados dos conjuntos `A` y `B`, `puede_separar_sii_abierto_clausura A B` dice
que `puede_separar A B ↔ ∃ U ∈ abiertos, (A ⊆ U ∧ clausura U ∩ B = ∅)`
-/
TheoremDoc topo.puede_separar_sii_abierto_clausura as "puede_separar_sii_abierto_clausura" in "Separación"

Statement puede_separar_sii_abierto_clausura (A B : Set X) : puede_separar A B ↔ ∃ U ∈ abiertos, (A ⊆ U ∧ (clausura U) ∩ B = ∅) := by
  Hint (hidden := true) "Divide el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint ( hidden := true ) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puede ser útil reescribir la definición de poder separar
    conjuntos en `{h}`."
    rw [def_puede_separar] at h
    Hint (hidden := true) "Gracias a `{h}`, sabemos que existen abiertos con ciertas
    propiedades. Puedes elegirlos con `choose`."
    choose U V hU hV hAU hBV hUV using h
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    use U
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hAU
    Hint (hidden := true) "Para ver la igualdad de conjuntos, usa el principio
    de extensionalidad (`ext`)."
    ext x
    Hint (hidden := true) "Puede ser útil simplificar la expresión."
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro hxcU hB
    Hint (hidden := true) "Reescribe la caracterización de la clausura en `{hxcU}`."
    rw [caracterizacion_clausura] at hxcU
    Hint (hidden := true) "Camos a necesitar ver que `{x} ∈ {V}`, así
    que tendremos que establecer un nuevo objetivo con `have`."
    have hxV : x ∈ V
    · Hint (hidden := true) "Puedes aplicar `{hBV}`."
      apply hBV
      exact hB
    Hint (hidden := true) "Ahora puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hxcU}` a `{V}`, `{hV}` y `{hxV}`."
    have haux := hxcU V hV hxV
    Hint (hidden := true) "Gracias a `{haux}` sabes que existen puntos con ciertas
    propiedades. Elige uno con `choose`."
    choose y hyV hyU using haux
    Hint (hidden := true) "Ahora tendremos que ver que `{x} ∈ {U} ∩ {V}`. Crea
    un nuevo objetivo con `have`."
    have hyUV : y ∈ U ∩ V
    · Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      exact hyU
      exact hyV
    Hint (hidden := true) "Puedes usar `{hUV}` para reescribir `{hyUV}`."
    rw [hUV] at hyUV
    Hint (hidden := true) "Ahora `{hyUV}` te da exactamente la contradicción."
    exact hyUV
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Gracias a `{h}` sabes que existen abiertos con
    ciertas propiedades. Eligelos con `choose`."
    choose U hU hAU hUcB using h
    Hint (hidden := true) "Puede ser útil reescribir la definición de poder
    separar."
    rw [def_puede_separar]
    Hint (hidden := true) "¿Cual puede ser el primer abierto que puedes usar?"
    use U
    Hint (hidden := true) "¿Y el segundo abierto cual puede ser? Recuerda que `clausura {U}`
    es un cerrado."
    Hint (hidden := true) "`use (clausura {U})ᶜ`"
    use (clausura U)ᶜ
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Que el complementario de un conjunto sea abierto
      puede reescribirse como que ese conjunto es cerrado."
      rw [← def_cerrado]
      Hint (hidden := true) "Se puede aplicar un teorema que dice que
      la clausura de un conjunto siempre es un cerrado."
      apply clausura_cerrado
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · exact hAU
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Toma un elemento arbitrario de `{B}` con `intro`."
      intro y hy
      Hint (hidden := true) "Para ver que `{y}` está en el complementario de
      un conjunto, podemos suponer que está en el conjunto (con `intro`) y
      llegar a una contradicción."
      intro hyB
      Hint (hidden := true) "Ahora podemos usar lo que sabemos para ver que
      `{y} ∈ clausura {U} ∩ {B}`. Crea un nuevo objetivo con `have`."
      have aux : y ∈ clausura U ∩ B
      · Hint (hidden := true) "Con lo que ya sabemos, esto es trivial."
        trivial
      Hint (hidden := true) "Ahora podemos usar `{hUcB}` para reescribir `{aux}`."
      rw [hUcB] at aux
      Hint (hidden := true) "Y la contradicción que buscábamos nos la da exactamente `{aux}`."
      exact aux
    Hint (hidden := true) "Para ver la igualdad de conjuntos, hay que usar
    el principio de extensionalidad (con `ext`)."
    ext x
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Introduce el antecedente con `intro`."
      intro hx
      Hint (hidden := true) "Puedes separar `{hx}` en dos hipótesis con `choose`
      o `cases'`."
      choose hxU hxcB using hx
      Hint (hidden := true) "Puedes simplificar el objetivo."
      simp only [mem_empty_iff_false]
      Hint (hidden := true) "Observa que `{hxcB}` nos dice que `{x}` *no*
      está en un conjunto, así que podemos aplicarlo para obtener la
      contradicción que buscamos."
      apply hxcB
      Hint (hidden := true) "Podemos aplicar el resultado que nos dice
      que la clausura de un conjunto contiene al conjunto."
      apply clausura_contiene
      exact hxU
    · Hint (hidden := true) "Introduce el antecedente con `intro`."
      intro hx
      Hint (hidden := true) "Como una de las hipótesis es  falsa por definición,
      la demostración es trivial."
      trivial








end topo
