import Game.Levels.Numerabilidad.AglomeracionCortadas

World "Limites"
Level 10
Title "Primer axioma de numerabilidad."

Introduction "
Un espacio es separable si existe un denso contable.

Un espacio topológico `X` cumple el *primer axioma de numerabilidad* (`IAN`)
si cada punto tiene una base contable de entornos.


Un conjunto `S : Set X` se dice *contable* si, o bien es vacío, o bien hay una función `f : ℕ → X`
tal que `S = { f n | n : ℕ }`.

Se puede demostrar que, si un espacio es *IAN*, se pueden elegir
las bases de entornos de cada punto de manera que sean encajadas. Es lo
que dice el teorema `caracterizacion_IAN`.

En este límite veremos una de las razones por las que la propiedad
de ser primero numerable es relevante: nos da una caracterización
para los puntos que están en la clausura de un conjunto,
en términos de límites de sucesiones.
"



def contable {X : Type} (S : Set X) := S = ∅ ∨ ∃ (f : ℕ → X) , S = { f n | n : ℕ}

theorem def_contable {X : Type} (S : Set X) : contable S ↔    S = ∅ ∨  ∃ (f : ℕ → X) , S = { f n | n : ℕ} := by
  rfl




namespace topo
open topo espacio_topologico Set Function Nat

def separable (X : Type) [espacio_topologico X] := ∃ (D : Set X), (denso D ∧ contable D)

def IAN (X : Type) [espacio_topologico X] := ∀ (x : X), ∃ B,  base_de_entornos x B ∧ contable B


/--
Un espacio topológico `X` es separable si existe un subconjunto `D`
denso y contable.
-/
DefinitionDoc separable as "separable"

/--
Un espacio topológico `X` cumple el *primer axioma de numerabilidad* (`IAN`)
si cada punto tiene una base contable de entornos.
-/
DefinitionDoc IAN as "IAN"

NewDefinition separable IAN

theorem def_separable (X : Type) [espacio_topologico X]: separable X ↔ ∃ (D : Set X), denso D ∧ contable D := by
  rfl

TheoremTab "Numerabilidad"

/--
Si `X`  es un espacio topológico, `def_separable X`  dice que
`separable X ↔ ∃ D , denso D ∧ contable D`.
-/
TheoremDoc topo.def_separable as "def_separable" in "Numerabilidad"

theorem def_IAN (X : Type) [espacio_topologico X]: IAN X ↔ ∀ (x : X), ∃ B,  base_de_entornos x B ∧ contable B := by
  rfl

/--
Si `X` es un espacio_topológico, `def_IAN X` dice que
` IAN X ↔ ∀ (x : X), ∃ B, base_de_entornos x B ∧ contable B`.
-/
TheoremDoc topo.def_IAN as "def_IAN" in "Numerabilidad"



theorem IAN_base_entornos_encajadas {X : Type} [espacio_topologico X] (hX : IAN X) (x : X) :
    ∃ (g : ℕ → Set X), (base_de_entornos x { (g n) | n : ℕ }) ∧ (∀ (n : ℕ), g (n + 1) ⊆ g n ) := by
  choose B hBbas hBcont using hX
  have hbas := hBbas x
  have hcont := hBcont x
  choose hbas hbas2 using hbas
  cases' hcont with hempty hcont
  · have haux := entornos_N1 x
    choose N hN using haux
    have hbasN := hbas2 N hN
    choose B1 hB1 hB2 using hbasN
    rw [hempty] at hB1
    trivial
  · choose f hf using hcont
    let g : ℕ → Set X
    · intro n
      induction n
      · exact f 0
      · exact f (n_1 + 1) ∩ n_ih
    use g
    fconstructor
    · fconstructor
      · intro N hN
        choose n hn using hN
        rw [←hn]
        clear hn
        induction n
        · apply hbas
          simp [g]
          rw [hf]
          use 0
        · apply entornos_N3
          · apply hbas
            rw [hf]
            use n_1 + 1
          · apply n_ih
      · intro N hN
        have hbas3 := hbas2 N hN
        choose B1 hB1 hB2 using hbas3
        rw [hf] at hB1
        choose n hn using hB1
        use g n
        fconstructor
        · use n
        · intro z hz
          apply hB2
          rw [← hn]
          induction n
          · exact hz
          · exact hz.1
    · intro n
      simp only [rec_add_one, inter_subset_right, g]


/--
Dado un espacio topológico `X`, `caracterizacion_IAN` dice que
`X` es `IAN` si y solo si para todo punto
existe una base contable de entornos encajados. Es decir:
`IAN X ↔ ∀ x, ∃ (g : ℕ → Set X), base_de_entornos x { (g n) | n : ℕ } ∧ (∀ (n m: ℕ), n ≤ m → g m  ⊆ g n )`
-/
TheoremDoc topo.caracterizacion_IAN as "caracterizacion_IAN" in "Limites"

theorem caracterizacion_IAN {X : Type} [espacio_topologico X]  :
    IAN X ↔ ∀ x, ∃ (g : ℕ → Set X), (base_de_entornos x { (g n) | n : ℕ }) ∧ (∀ (n m: ℕ), n ≤ m → g m  ⊆ g n ) := by
  fconstructor
  · intro hX x
    have haux := IAN_base_entornos_encajadas hX x
    choose g hg1 hg2 using haux
    use g
    fconstructor
    · exact hg1
    · intro n m hnm
      have haux : ∃ l, m = n + l
      · use m - n
        simp only [ge_iff_le, hnm, add_tsub_cancel_of_le]
      choose l hl using haux
      rw [hl]
      clear hl
      clear hnm
      induction l
      · simp only [zero_eq, add_zero]
        trivial
      · intro y hy
        apply n_ih
        apply hg2
        exact hy
  · intro h x
    specialize h x
    choose g hg1 hg2 using h
    use { g n | n : ℕ  }
    fconstructor
    · exact hg1
    · right
      use g


NewTheorem topo.def_separable topo.def_IAN topo.caracterizacion_IAN

/--
Si `X` es un espacio topológico , y se cumple la hipótesis `h : IAN X`, `A` es un subconjunto de `X`,
y `x` un punto, `clausura_sucesion h A x` dice que `x ∈ clausura A ↔ ∃ s : ℕ → X, (∀ n, s n ∈ A ) ∧ limite x s`.
-/
TheoremDoc topo.clausura_sucesion as "clausura_sucesion" in "Limites"





Statement clausura_sucesion {X : Type} [espacio_topologico X] (h : IAN X) (A : Set X) (x : X) :
    x ∈ clausura A ↔ ∃ s : ℕ → X, (∀ n, s n ∈ A) ∧ limite s x := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro hx
    Hint (hidden := true) "Puede ser útil reescribir la caracterización de los puntos en la clausura."
    rw [caracterizacion_clausura] at hx
    Hint (hidden := true) "También puede ser útil reescribir `{h}` usando la caracterización de los espacios `IAN`."
    rw [caracterizacion_IAN] at h
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    particularizando `{h}` a `{x}`."
    have h2 := h x
    Hint (hidden := true) "Gracias a `{h2}` sabemos que existe alguna
    función con ciertas propiedades. Elígela con `choose`."
    choose g hgbas hgenc using h2
    Hint (hidden := true) "Puedes reescribir la definición de
    base de entornos en `{hgbas}`."
    rw [def_base_de_entornos] at hgbas
    Hint (hidden := true) "Puedes separar `{hgbas}` en dos hipótesis
    con `cases'` o `choose`."
    choose hB1 hB2 using hgbas
    Hint "Ahora tenemos que construir una sucesión. Para ello, necesitamos
    un punto en `g (n) ∩ A` para cada `n`. Así que necesitamos
    demostrar que esos puntos existen.

    Crea un nuevo objetivo para demostrar esa existencia:
    `have haux : ∀ n, ∃ y, y ∈ {g} n ∩ {A}`
    "
    have haux : ∀ n, ∃ y, y  ∈ g n ∩ A
    · Hint (hidden := true) "Toma un número arbitrario con `intro`."
      intro n
      Hint "Ahora necesitamos ver que `{g} {n}` es entorno de `{x}`.

      Crea otro objetivo con `have`."
      have hBn : entorno x (g n)
      · Hint (hidden := true) "Puedes aplicar `{hB1}`."
        apply hB1
        Hint (hidden := true) "¿Qué número puedes usar?"
        use n
      Hint (hidden := true) "Gracias a `{hBn}`, sabemos que existe
      un abierto intermedio, elígelo con `choose`."
      choose U hUab hxU hUB using hBn
      Hint (hidden := true) "Ahora puedes obtener (con `have`)
      una nueva hipótesis aplicando `{hx}` a `{U}`, `{hUab}` y `{hxU}`."
      have hx2 := hx U hUab hxU
      Hint (hidden := true) "Gracias a `{hx2}`, sabemos que existen
      puntos en `{U} ∩ {A}`, elige uno con `choose`."
      choose y hyU hyA using hx2
      Hint (hidden := true) "Y ese es el punto que podemos usar."
      use y
      Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
      fconstructor
      · Hint (hidden := true) "Puedes aplicar `{hUB}`."
        apply hUB
        exact hyU
      · exact hyA
    Hint "Ahora, sabiendo que para cada número natural
    existen puntos en cierto conjunto, podemos tomar una función que
    elija uno de ellos:

    `choose s hsn hsA using `{haux}`.
    "
    choose s hsn hsA using haux
    Hint (hidden := true) "Y `{s}` es la sucesión que tenemos que usar."
    use s
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · exact hsA
    · Hint (hidden := true) "Como queremos ver que para cada abierto
      que contenga a  `{x}` hay un punto de la sucesión, toma
      uno arbitrario con `intro`."
      intro U hU hxU
      Hint (hidden := true) "Necesitaremos ver que `{U}` es entorno
      de `{x}`. Afortunadamente, tenemos un teorema que nos dice
      que un conjunto es abierto si y solo si es entorno de todos sus puntos."
      rw [abierto_sii_entorno] at hU
      Hint (hidden := true) "Ahora podemos obtener una nueva hipótesis
      (con `have`) aplicando `{hU}` a `{x}` y `{hxU}`."
      have h2 := hU x hxU
      Hint (hidden := true) "Y de nuevo, podemos obtener una nueva hipótesis
      aplicando `{hB2}` a `{U}` y `{h2}`."
      have hBU := hB2 U h2
      Hint (hidden := true) "`{hBU}` nos dice que existen ciertos
      conjuntos, elije uno con `choose`."
      choose B hB hBU using hBU
      Hint (hidden := true) "`{hB}` asegura que existe algún número
      natural con ciertas propiedades. Elige uno con `choose`."
      choose n hBn using hB
      Hint (hidden := true) "Ya tenemos un natural que podemos usar."
      use n
      Hint (hidden := true) "Toma un número arbitrario mayor o igual a
      `{n}` con `intro`."
      intro n1 hn1
      Hint (hidden := true) "Puedes aplicar `{hBU}`."
      apply hBU
      Hint (hidden := true) "Aprovecha `{hBn}` para reescribir el objetivo."
      rw [← hBn]
      Hint (hidden := true) "Puedes obtener una nueva hipótesis particularizando
      `{hgenc}` a `{n} y `{n1}` (y `{hn1}`)."
      have hgencn := hgenc n n1 hn1
      Hint (hidden := true) "Ahora puedes aplicar `hgencn`."
      apply hgencn
      Hint (hidden := true) "Puedes aplicar `{hsn}`."
      apply hsn
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Puedes elegir una sucesión usando `{h}`."
    choose s hs1 hs2 using h
    Hint (hidden := true) "Recuerda que hay un teorema que asegura
    algo parecido, pero con aglomeraciones en vez de límites. Prueba
    a aplicarlo."
    apply aglomeracion_clausura hs1
    Hint (hidden := true) "Recuerda que un resultado
    relaciona puntos de aglomeración, y límites
    de subsucesiones. Aplicalo (usando `{s}` como subsucesión
    de la propia `{s}`.)"
    apply aglomeracion_subsucesion s s
    · Hint (hidden := true) "Para ver que `{s}` es subsucesión
      de sí misma, necesitas dar una aplicación de `ℕ` en `ℕ`.

      En concreto la aplicación identidad (llamada `id`) sirve."
      use id
      Hint (hidden := true) "Debería bastar simplificar la expresión
      para que sea trivial."
      simp only [id_eq, imp_self, forall_const, comp_id, and_self]
    · exact hs2



end topo
