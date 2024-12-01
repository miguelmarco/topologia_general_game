import Game.Levels.ExteriorFronteraAislado.FronteraInterClausuraCompl
World "ExteriorFronteraAislado"
Level 10
Title "Frontera."

Introduction "La clausura de un conjunto es la unión de su interior y su frontera.

Para esta demostración nos será útil razonar por casos."

namespace topo
open topo espacio_topologico Set
variable {X : Type} [espacio_topologico X] (A : Set X)


/--
Dado un conjunto `A`  en un espacio topológico,
`clausura_union_inter_frontera A` dice que `clausura A =  interior A ∪ frontera A`.
-/
TheoremDoc topo.clausura_union_inter_frontera as "clausura_union_inter_frontera" in "Exterior/Frontera/Aislado"


Statement clausura_union_inter_frontera : clausura A =  interior A ∪ frontera A := by
  Hint (hidden := true) "Prueba a reescribir la frontera como intersección
  de clausuras."
  rw [frontera_inter_clausura_compl]
  Hint (hidden := true) "La clausura del complementario se puede
  reescribir como el complementario del interior."
  rw [← complementario_interior]
  Hint (hidden := true) "Ahora podemos tomar un punto arbitrario
  y ver que está en un conjunto si y solo si está en el otro."
  ext x
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Ahora es cuando será útil razonar por casos.

    Usa la táctica `by_cases` para separar el objetivo en dos: uno suponiendo
    que `{x} ∈ interior {A}`, otro asumiendo lo contrario."
    by_cases hx : x ∈ interior A
    · Hint (hidden := true) "En este caso, ¿en cual de las dos partes de la
      unión está `{x}`? ¿La opción de la izquierda o la de la derecha?"
      left
      exact hx
    · Hint (hidden := true) "Ahora `{x}` estará en la otra opción."
      right
      Hint (hidden := true) "Separa el objetivo con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Esto es exactamente lo que dice `{hx}`."
        exact hx
      · exact h
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes separar `{h}` en dos con `cases'` o `choose`."
    cases' h with h h
    · Hint (hidden := true) "Puedes aplicar el teorema que dice que un conjunto
      está contenido en su clausura."
      apply clausura_contiene
      Hint (hidden := true) "Ahora puedes aplicar que el interior de un conjunto
      está contenido en el conjunto."
      apply interior_contenido
      exact h
    · Hint (hidden := true) "Puedes separar `{h}` en dos casos con `cases'` o `choose`."
      cases' h with h1 h2
      exact h2


end topo
