import Game.Levels.Clausura.ClausuraSubconjunto
open espacio_topologico Set Function

World "Clausura"
Level 7
Title "Caracterización de cerrados en términos de clausuras."

Introduction "
Un conjunto es cerrado si y sólo si es igual a su clausura.
"

variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Con conjunto `A`, es cerrado si y sólo si `A = clausura A`
-/
TheoremDoc caracterizacion_cerrado_clausura as "caracterizacion_cerrado_clausura" in "Clausura"

Statement caracterizacion_cerrado_clausura : A ∈ cerrados ↔ A = clausura A := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Para ver la igualdad de dos conjuntos,
    usa el principio de extensionalidad con `ext`."
    ext y
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes aplicar directamente un resultado previo."
      apply clausura_contiene
    · Hint (hidden := true) "Introduce el antecedente con `intro`."
      intro hy
      Hint (hidden := true) "Puede ser útil reescribir la definición de clausura en `{hy}`."
      rw [def_clausura] at hy
      Hint (hidden := true) "Observa que `{hy}` te asegura que `{y}` está
      en cualquier conjunto que cumpla ciertas propiedades. Puedes
      aplicarlo, y solo quedará demostrar que `{A}` cumple esas propiedades."
      apply hy
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · exact h
      · trivial
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes usar `{h}` para reescribir el objetivo."
    rw [h]
    Hint (hidden := true) "Un resultado previo te asegura justo lo que quieres."
    apply clausura_cerrado
