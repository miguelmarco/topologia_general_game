import Game.Levels.Clausura.ClausuraIdempotente


World "Clausura"
Level 9
Title "Clausura de una unión."

Introduction "
La clausura una unión es la unión de las clausuras
"

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A B: Set X)


/--
Dados dos conjuntos  `A` y `B`, `clausura (A ∪ B) = clausura A ∪ clausura B`
-/
TheoremDoc topo.clausura_union as "clausura_union" in "Clausura"

Statement clausura_union : clausura (A ∪ B) = clausura A ∪ clausura B := by
  Hint (hidden := true) "Para demostrar la igualdad de dos conjuntos
  mediante el principio de extensionalidad, toma un elemento con `ext`."
  ext x
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antedecente con `intro`."
    intro h
    Hint "Recuerda que vimos que un cerrado que contenga
    a un conjunto, debe contener al conjunto, así que podemos aplicar
    ese resultado y bastará probar que el conjunto del objetivo es un
    cerrado que contiene a `{A} ∪ {B}`.

    **¡Atención!** para aplicar `clausura_contenida_cerrado` tendrás
    que decir además para que conjunto lo estás usando, ya que el objetivo
    no es suficiente para determinarlo. Así que tendrás que usar
    `apply clausura_contenida_cerrado ({A} ∪ {B})`."
    apply clausura_contenida_cerrado (A ∪ B)
    · Hint (hidden := true) "Hay un resultado que dice que la unión de
      cerrados es cerrado. Puedes aplicarlo."
      apply union_cerrados
      · Hint (hidden := true) "Sabemos que la clausura de un conjunto siempre
        es un cerrado. Aplica el teorema que lo asegura."
        apply clausura_cerrado
      · apply clausura_cerrado
    · Hint (hidden := true) "Como hay que ver un contenido, toma un elemento
      arbitrario con `intro`."
      intro y hy
      Hint (hidden := true) "Como `{hy}` nos dice que `{x}` está
      en `{A}` o en `{B}`, tendremos que distinguir cada uno de esos casos.

      Usa `cases'` para separar el objetivo en dos dependiendo de en cual
      de los dos casos estemos."
      cases' hy with hy hy
      · Hint (hidden := true) "Hay de determinar si demostramos que
        `{x} ∈ clausura {A}` o que `{x} ∈ clausura {B}`. Recuerda que las
        tácticas para esto eran `left` y `right`."
        left
        Hint (hidden := true) "Podemos aplicar el resultado que nos dice
        que la clausura de un conjunto contiene al conjunto."
        apply clausura_contiene
        exact hy
      · right
        apply clausura_contiene
        exact hy
    exact h
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "`{h}` nos dice que `{x}` está en  `clausura {A}`
    o en `clausura {B}`. Puedes usar `cases'` para tratar cada uno de estos casos
    por separado."
    cases' h with h h
    · Hint (hidden := true) "Sabemos que, si un conjunto está contenido en otro,
      sus clausuras también lo cumplen. Puedes aplicar ese resultado,
      pero como sólo mirando al objetivo no se puede deducir a qué
      subconjunto de `{A} ∪ {B}` te refieres, hay que especificarlo."
      Hint (hidden := true) "`apply clausura_subconjunto {A}`."
      apply clausura_subconjunto A
      · intro y hy
        left
        exact hy
      exact h
    · apply clausura_subconjunto B
      · intro y hy
        right
        exact hy
      exact h

end topo
