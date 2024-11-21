import Game.Levels.Clausura.ClausuraInterseccion


World "Clausura"
Level 12
Title "Densidad."

Introduction "
Un conjunto se dice **denso** si su clausura es el total. Veamos
una caracterización de la densidad.
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)

def denso := clausura A = univ

/--
Si `X` es un espacio topológico, un subconjunto `A` se dice **denso** si
`clausura A = X`.
-/
DefinitionDoc denso as "denso"

NewDefinition denso

theorem def_denso : denso A ↔ clausura A = univ := by
  rfl

/--
TheoremDoc
-/
TheoremDoc topo.def_denso as "def_denso" in "lemas_definición"

NewTheorem topo.def_denso

/--
Si `X` es un espacio topológico, y `A` es un subconjunto de `X`,
`denso A ↔ ∀ U ∈ abiertos, (∃ x, x ∈ U) → ∃ y, y ∈ U ∩ A`.
-/
TheoremDoc topo.caracterizacion_denso as "caracterizacion_denso" in "Clausura"

Statement caracterizacion_denso : denso A ↔ ∀ U ∈ abiertos, (∃ x, x ∈ U) → ∃ y, y ∈ (U ∩ A) := by
  Hint (hidden := true) "Puedes separar el objetivo en dos usando `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Puedes introducir el antecedente, y los objetos
    arbitrarios necesarios, con `intro`."
    intro h
    intro U hU hxU
    Hint (hidden := true) "Como `{hxU}` garantiza que existen elementos
    en `{U}`, podemos elegir uno con `choose`."
    choose x hxU using hxU
    Hint (hidden := true) "Nos gustaría poder usar el hecho de que
    `{x}` tiene que estar en la clausura de `{A}`, así que podemos
    enunciar esa hipótesis con `have` y pasar a demostrarla."
    have hxA : x ∈ clausura A
    · Hint (hidden := true) "Puede ser útil reescribir la definición de densidad
      en `{h}`."
      rw [def_denso] at h
      Hint (hidden := true) "Ahora podemos usar `{h}` para reescribir el objetivo."
      rw [h]
      Hint (hidden := true) "Esto es trivial."
      trivial
    Hint (hidden := true) "Ahora podemos usar la caracterización de
    los puntos en la clausura para reescribir `{hxA}`."
    rw [caracterizacion_clausura] at hxA
    Hint (hidden := true) "Observa que ` {hxA}` implica el objetivo (si podemos
    demostrar sus condiciones), así que puedes aplicarlo."
    apply hxA
    exact hU
    exact hxU
  · Hint (hidden := true) "Puedes introducr el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Para demostrar la igualdad de dos conjuntos,
    lo habitual es usar el principio de extensionalidad (`ext`)."
    ext x
    Hint (hidden := true) "Puedes dividir el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
      intro hx
      Hint (hidden := true) "Esto es trivial."
      trivial
    · Hint (hidden := true) "Puedes introducir el antecedente con `intro`."
      intro hx
      Hint (hidden := true) "Puede ser útil reescribir el objetivo usando
      la caracterización de estar en la clausura."
      rw [caracterizacion_clausura]
      Hint (hidden := true) "Puedes introducir un abierto y un punto arbitrarios
      con `intro`."
      intro U hU hxU
      Hint (hidden := true) "Observa que `{h}` implica el objetivo. Así que
      puedes aplicarlo."
      apply h
      exact hU
      use x

end topo
