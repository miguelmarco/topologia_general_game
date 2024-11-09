import Game.Levels.Clausura.ClausuraCerrado
open espacio_topologico Set Function

World "Clausura"
Level 4
Title "La clausura de un conjunto está contenida en cualquier cerrado
que contenga al conjunto."

Introduction "Otro resultado fácil: si un cerrado contiene a un conjunto,
también contiene a su clausura.
"

variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Si un cerrado `C` contiene a un conjunto `A`, también contiene
a su clausura.
-/
TheoremDoc clausura_contenida_cerrado as "clausura_contenida_cerrado" in "Clausura"

Statement clausura_contenida_cerrado (C : Set X) (hC : C ∈ cerrados ) (hA : A ⊆ C) : clausura A ⊆ C := by
  Hint (hidden := true) "Para ver que un conjunto está contenido en otro,
  toma un elementi arbitrario con `intro`."
  intro y hy
  Hint (hidden := true) "Puede ser útil reescribir la definición de clausura
  en `{hy}`."
  rw [def_clausura] at hy
  Hint (hidden := true) "Observa que `{hy}` afirma que `{y}` está
  en todos los cerrados que contienen a `{A}`, así que puedes
  aplicarlo y sólo quedará demostrar que `{C}` cumple esas propiedades."
  apply hy
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · exact hC
  · exact hA
