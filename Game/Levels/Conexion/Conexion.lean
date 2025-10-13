import Game.Levels.Compacidad.CocienteCompacto

World "Conexión"
Level 1
Title "Conexión en términos de cerrados"

namespace topo
open topo Set espacio_topologico

variable (X : Type) [espacio_topologico X]

def conexo  := ¬ ∃ (A B : Set X), A ∈ abiertos ∧ B ∈ abiertos ∧
    A ≠ ∅ ∧ B  ≠ ∅ ∧ A ∩ B = ∅ ∧ A ∪ B = univ

/--
Un espacio topológico $X$ se dice *conexo* si
no se puede poner como unión de dos abiertos propios disjuntos.
-/
DefinitionDoc topo.conexo as "conexo"

/--
Un espacio $X$ es conexo si y solo si '¬ ∃ (A B : Set X), A ∈ abiertos ∧ B ∈ abiertos ∧
    A ≠ ∅ ∧ B  ≠ ∅ ∧ A ∩ B = ∅ ∧ A ∪ B = univ'
-/
TheoremDoc topo.def_conexo as "def_conexo" in "lemas-definición"


theorem def_conexo : conexo X ↔ ¬ ∃ (A B : Set X), A ∈ abiertos ∧ B ∈ abiertos ∧
    A ≠ ∅ ∧ B  ≠ ∅ ∧ A ∩ B = ∅ ∧ A ∪ B = univ := by rfl


/--
Un espacio es conexo si y solo si no es unión de dos cerrados disjuntos no vacíos.
-/
TheoremDoc topo.caracterizacion_conexo_cerrados as "caracterizacion_conexo_cerrados" in "Conexión"

Statement caracterizacion_conexo_cerrados : conexo X ↔ ¬ ∃ (A B : Set X), A ∈ cerrados ∧ B ∈ cerrados ∧
    A ≠ ∅ ∧ B  ≠ ∅ ∧ A ∩ B = ∅ ∧ A ∪ B = univ := by
  Hint (hidden := true) "Para separar una doble implicación en dos implicaciones,
  puedes usar `fconstructor`"
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Supón que se cumple lo que queremos negar
    (con `intro`) para llegar a una contradicción."
    intro hn
    Hint (hidden := true) "Puedes usar `{hn}` para elegir dos cerrados
    y sus propiedades."
    choose A B hAc hBc hA0 hB0 hAB0 hAB using hn
    Hint (hidden := true) "Puedes reescribir la definición de conexo en `{h}`."
    rw [def_conexo] at h
    Hint (hidden := true) "Como quieres llegar a una contradicción, puedes aplicar
    `{h}`, y así te bastará con ver que existen esos dos abiertos."
    apply h
    Hint (hidden := true) "¿Qué abierto puedes usar?"
    Hint (hidden := true) "Usa `{A}ᶜ`."
    use (Aᶜ )
    Hint (hidden := true) "Puedes usar `{B}ᶜ`."
    use Bᶜ
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Esto es exactamente lo que dice `{hAc}`."
      exact hAc
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Esto es exactamente lo que dice `{hBc}`.g"
      exact hBc
    Hint (hidden := true) "Separa el objetivo en varios con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Para demostrar que algo no es cierto (en este caso,
      una igualdad), la forma natural es suponer que es cierto (con `intro`)
      y llegar a una contradicción."
      intro hAt
      Hint (hidden := true) "`{hAt}` se puede simplificar."
      simp only [compl_empty_iff] at hAt
      Hint (hidden := true) "Puedes usar `{hAt}` para reescribit `{hAB0}`."
      rw [hAt] at hAB0
      Hint (hidden := true) "`{hAB0}` se puede simplificar."
      simp at hAB0
      Hint (hidden := true) "Ahora ya tienes una contradicción clara entre
      `{hB0}` y `{hAB0}`."
      tauto
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "De nuevo, para demostrar una negación, introduce
      la afirmación correspondiente (con `intro`) y pasa a demostrar una contradicción."
      intro hBt
      Hint (hidden := true) "`{hBt}` se puede simplificar."
      simp at hBt
      Hint (hidden := true) "Puedes usar `{hBt}` para reescribir `{hAB0}`."
      rw [hBt] at hAB0
      Hint (hidden := true) "Simplifica `{hAB0}`."
      simp only [inter_univ] at hAB0
      trivial
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes usar `compl_union` para reescribir el objetivo."
      rw [← compl_union]
      Hint (hidden := true) "Puedes reescribir el objetivo con `{hAB}`."
      rw [hAB]
      Hint (hidden := true) "Basta con simplificar."
      simp only [compl_univ]
    Hint (hidden := true) "Puedes reescribir el objetivo con `compl_inter`."
    rw [← compl_inter]
    Hint (hidden := true) "Puedes reescribir el objetivo con `{hAB0}`."
    rw [hAB0]
    Hint (hidden := true) "Basta con simplificar."
    simp only [compl_empty]
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes reescribir la definición de conexo."
    rw [def_conexo]
    Hint (hidden := true) "Como quieres demostrar una negación, asume la
    afirmación con `intro` y pasa a demostrar una contradicción."
    intro hcon
    Hint (hidden := true) "Como `{h}` es una negación, puedes aplicarla,
    y bastará demostrar lo que es negado en `{h}`."
    apply h
    Hint (hidden := true) "Gracias a `{hcon}`, puedes elegir
    dos abiertos y sus propiedades."
    choose A B hAb hBab hAo hBo hABo hAB using hcon
    Hint (hidden := true) "¿Qué cerrado puedes usar?"
    Hint (hidden := true) "Usa `{A}ᶜ`."
    use Aᶜ
    Hint (hidden := true) "¿Qué otro cerrado puedes usar?"
    use Bᶜ
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes reescribir usando la definición de cerrado."
      rw [def_cerrado]
      Hint (hidden := true) "Puede ser útil simplificar."
      simp only [compl_involutive, Function.Involutive.comp_self, cancela_inver]
      exact hAb
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes reescribir usando la definición de cerrado."
      rw [def_cerrado]
      Hint (hidden := true) "Simplifica."
      simp only [compl_involutive, Function.Involutive.comp_self, cancela_inver]
      exact hBab
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Simplifica,"
      simp only [ne_eq, compl_empty_iff]
      Hint (hidden := true) "Asume lo que quieres negar con `intro`,
      y pasa a demostrar una contradicción."
      intro hAu
      Hint (hidden := true) "Puedes usar `{hAu}` para reescribir `{hABo}`."
      rw [hAu] at hABo
      Hint (hidden := true) "Simplifica `{hABo}`."
      simp only [univ_inter] at hABo
      Hint (hidden := true) "Como `{hBo}` es una negación, puedes aplicarla,
      así que bastará demostrar lo que se niega en `{hBo}` para ver que
      hay contradicción."
      apply hBo
      exact hABo
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Simplifica el objetivo."
      simp only [ne_eq, compl_empty_iff]
      intro hAu
      rw [hAu] at hABo
      simp only [inter_univ] at hABo
      apply hAo
      exact hABo
    Hint (hidden := true) "Separa el objetivo con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Puedes usar `compl_union` para reescribir el objetivo."
      rw [← compl_union]
      Hint (hidden := true) "Puedes reescribir el objetivo gracias a `{hAB}`."
      rw [hAB]
      Hint (hidden := true) "Simplifica."
      simp only [compl_univ]
    · rw [← compl_inter]
      rw [hABo]
      simp only [compl_empty]




end topo
