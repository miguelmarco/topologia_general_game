import Game.Levels.Numerabilidad.Truncadas

World "Limites"
Level 4
Title "Sucesiones asintóticas."

Introduction "
Dos sucesiones `s₁` y `s₂` se dicen *asintóticas* si tienen una
subsucesión truncada común `s'`.

Veamos que sucesiones asintóticas tienen los mismos límites.
"


namespace topo
open topo espacio_topologico Set Function Nat
variable {X : Type} [espacio_topologico X]

def asintotica (s₁ : ℕ → X) (s₂ : ℕ → X) := ∃ s, (truncada s₁ s ∧ truncada s₂ s)

/--
Dadas dos sucesiones `s₁` y `s₂`, son *asintóticas* si
existe una subsucesión truncada común `s`.
-/
DefinitionDoc asintotica as "asintotica"

theorem def_asintotica (s₁ : ℕ → X) (s₂ : ℕ → X) : asintotica s₁ s₂ ↔  ∃ s, (truncada s₁ s ∧ truncada s₂ s) := by
  rfl

/--
Dadas dos sucesiones `s₁` y `s₂`, `def_asintotica s₁ s₂` dice que
`asintotica s₁ s₂ ↔ ∃ s, (truncada s₁ s ∧ truncada s₂ s)`.
-/
TheoremDoc topo.def_asintotica as "def_asintotica" in "Limites"

NewTheorem topo.def_asintotica

/--
Si `s₁` y `s₂` son sucesiones asintóticas, un punto es límite de `s₁` si y solo si
es límite de `s₂`.
-/
TheoremDoc topo.limite_asintotica as "limite_asintotica" in "Limites"

Statement limite_asintotica (s1 s2 : ℕ → X) (h : asintotica s1 s2) (x : X) :
    limite s1 x ↔ limite s2 x := by
  Hint (hidden := true) "Empecemos reescribiendo la definición de ser asintóticas
  en `{h}`."
  rw [def_asintotica] at h
  Hint (hidden := true) "Gracias a `{h}`, sabemos que existen sucesiones
  con ciertas propiedades, elige una con `choose`."
  choose s hs1 hs2 using h
  Hint (hidden := true) "Tenemos un teorema que nos dice algo sobre límites
  de sucesiones truncadas. Podemos aplicarlo a `{hs1}` para obtener una
  nueva hipóteis (con `have`)."
  Hint (hidden := true ) "Teclea `have haux1 := limite truncada `{hs1}`."
  have haux1 := limite_truncada hs1
  Hint (hidden := true ) "Y podemos hacer lo mismo con `{hs2}`."
  have haux2 := limite_truncada hs2
  Hint (hidden := true ) "Y ahora solo falta reescribir el objetivo usando
  `{haux1}`  y `{haux2}`."
  rw [← haux1,haux2]



end topo
