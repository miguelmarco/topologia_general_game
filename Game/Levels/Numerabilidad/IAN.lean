import Game.Levels.ExteriorFronteraAislado.Derivado

World "Numerabilidad"
Level 1
Title "Primer axioma de numerabilidad."

Introduction "
Un espacio es separable si existe un denso numerable.

Un espacio topológico `X` cumple el *primer axioma de numerabilidad* (`IAN`)
si cada punto tiene una base contable de entornos.

En esta demostración necesitaremos dos nuevas tácticas:

La táctica `clear` permite limpiar hipótesis del estado
de la demostración. Esto puede ser útil para mantener
el estado limpio de hipótesis que ya no se van a usar,
pero también puede servir para evitar que algunas hipótesis
se intenten generalizar en demostraciones por inducción.

La táctica `let` permite definir un objeto para ser usado
dentro de una demostración.

`let a := expr` define un objeto llamado `a`, definido como el contenido de
la expresión `expr`.

`let a : tipo`  define un objeto llamado `a` de tipo `tipo`, y crea un nuevo
objetivo en el que debe definirse. Esto es especialmente útil
si se quiere definir una función.
"

namespace topo
open topo espacio_topologico Set Function Nat

def separable (X : Type) [espacio_topologico X] := ∃ f : ℕ  → X,  denso { f n | n : ℕ}

def IAN (X : Type) [espacio_topologico X] := ∀ (x : X), ∃ f : ℕ → Set X,  base_de_entornos x {f n | n : ℕ}
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

theorem def_separable (X : Type) [espacio_topologico X]: separable X ↔∃ f : ℕ  → X,  denso { f n | n : ℕ} := by
  rfl

TheoremTab "Numerabilidad"

/--
Si `X`  es un espacio topológico, `def_separable X`  dice que
`separable X ↔ ∃ D : Set X, denso D ∧ Countable D`.
-/
TheoremDoc topo.def_separable as "def_separable" in "Numerabilidad"

theorem def_IAN (X : Type) [espacio_topologico X]: IAN X ↔ ∀ (x : X), ∃ f : ℕ → Set X,  base_de_entornos x {f n | n : ℕ} := by
  rfl

/--
Si `X` es un espacio_topológico, `def_IAN X` dice que
` IAN X ↔ ∀ (x : X), ∃ B, base_de_entornos x B ∧ Countable B`.
-/
TheoremDoc topo.def_IAN as "def_IAN" in "Numerabilidad"



/--
La táctica `let` permite definir un objeto para ser usado
dentro de una demostración.

`let a := expr` define un objeto llamado `a`, definido como el contenido de
la expresión `expr`.

`let a : tipo`  define un objeto llamado `a` de tipo `tipo`, y crea un nuevo
objetivo en el que debe definirse. Esto es especialmente útil
si se quiere definir una función.
-/
TacticDoc «let»

/--
La táctica `clear` permite limpiar hipótesis del estado
de la demostración. Esto puede ser útil para mantener
el estado limpio de hipótesis que ya no se van a usar,
pero también puede servir para evitar que algunas hipótesis
se intenten generalizar en demostraciones por inducción.
-/
TacticDoc clear

NewTactic «let» clear

theorem caracterizacion_IAN (X : Type) [espacio_topologico X] : IAN X ↔ ∀ (x : X), ∃ (Bx : Set (Set X)), (base_de_entornos x Bx ∧ Set.Countable Bx) := by
  fconstructor
  · intro h x
    specialize h x
    choose f hf using h
    use {(f n) | n  : ℕ }
    fconstructor
    · exact hf
    · rw [@countable_iff_exists_subset_range]
      use f
      intro U hU
      choose n hn using hU
      use n
  · intro h
    intro x
    specialize h x
    choose Bx hBx hcont using h
    choose hBx1 hBx2 using hBx
    rw [@countable_iff_exists_subset_range] at hcont
    choose f hf using hcont
    fconstructor
    intro n
    by_cases hcas : f n ∈ Bx
    · exact f n
    · exact univ
    fconstructor
    · intro B hB
      choose n hn using hB
      by_cases hcas : f n ∈ Bx
      · simp only [hcas, ↓reduceDite] at hn
        rw [← hn]
        apply hBx1
        exact hcas
      · simp only [hcas, ↓reduceDite] at hn
        use univ
        fconstructor
        · exact abierto_total
        · simp only [mem_univ, univ_subset_iff, true_and,← hn]
    · intro N hxN
      specialize hBx2 N hxN
      choose B hB hBN using hBx2
      have h2 := hf hB
      choose n hn using h2
      use B
      fconstructor
      · use n
        rw [← hn]
        simp only [dite_eq_ite, ite_eq_left_iff]
        rw [hn]
        simp only [hB, not_true_eq_false, IsEmpty.forall_iff]
      exact hBN

/--
`caracterizacion_IAN` dice que un espacio es `IAN` si y solo si
 `∀ x , ∃ Bx, (base_de_entornos x Bx ∧ Set.Countable Bx)`.
-/
TheoremDoc topo.caracterizacion_IAN as "caracterizacion_IAN" in "Numerabilidad"

NewTheorem topo.def_separable topo.def_IAN


/--
En un espacio `IAN`, cada punto admite una base de entornos contable y encajada
(es decir, que cada elemento, está contenido en el anterior).
-/
TheoremDoc topo.IAN_base_entornos_encajadas as "IAN_base_entornos_encajadas" in "Numerabilidad"


Statement IAN_base_entornos_encajadas (X : Type) [espacio_topologico X] (hX : IAN X) (x : X) :
    ∃ (g : ℕ → Set X), (base_de_entornos x { (g n) | n : ℕ }) ∧ (∀ (n : ℕ), g (n + 1) ⊆ g n ) := by
  Hint (hidden := true) "Puede ser útil reescribir la definición de `IAN` en `{hX}`."
  rw [def_IAN] at hX
  Hint (hidden := true) "Podemos obtener una nueva hipótesis (con `have`)
  aplicando `{hX}` a `{x}`."
  have h := hX x
  Hint (hidden := true) "`{h}` nos asegura que existe alguna función con
  ciertas propiedades. Elige una con `choose`."
  choose f hBx hB using h
  Hint  "Aquí vamos a necesitar definir una función `g` que tome
  valores en los naturales, y devuelva conjuntos de `{X}`. Podemos
  hacer esto gracias a la táctica `let` que nos permite
  definir objetos auxiliares en medio de una demostración.
  Teclea `let g : ℕ → Set X` (el símbolo `ℕ` se puede obtener tecleando
  `\\N`.)"
  let g : ℕ → Set X
  Hint  "Ahora tenemos que definir la función. Como tenemos que decir
  qué valor asignar a cada natural, tomemos un natural arbitrario con `intro n`."
  · intro n
    Hint "Ahora vamos a construir los valores que tomará `g` por inducción.
    Teclea `induction' n with m S`.

    - `n` es el valor sobre el que haremos la inducción.
    - `m` será el valor que usaremos en el paso de inducción: suponiendo
      que conocemos el valor para `m`, daremos el valor para `m + 1`
    - `S` será el conjunto obtenido para `n = m`, y lo usaremos para definir el
      valor para `n = m + 1`."
    induction' n with m S
    · Hint "Aquí vamos a definir el valor de `g` para `n = 0`. Teclea `use {f} 0`
      (es decir, `g 0` va a ser `{f} 0`)."
      use f 0
    · Hint "Ahora, suponiendo que `g m = S`, tenemos que definir `g (m + 1)`.
      Como queremos que `g` sea decreciente, vamos a intersecar `S` con el siguiente
      conjunto de `{f}`. Teclea `use S ∩ ({f} (m + 1))`."
      use S ∩ (f (m + 1))
  Hint "Pues ya hemos definido la función que queriamos, ahora podemos usarla."
  use g
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Será útil reescribir la definición de base de entornos."
    rw [def_base_de_entornos]
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · Hint (hidden := true) "Como hay que demostrar que algo se cumple para todo
      elemento de una familia, toma uno arbitrario con `intro`."
      intro U hU
      Hint (hidden := true) "Gracias a `{hU}`, puedes elegir un número
      natural `n` tal que `{g} n = {U}`. Eligelo con `choose`."
      choose n hn using hU
      Hint (hidden := true) "Puedes usar `{hn}` para reescribir el objetivo
      (de derecha a izquierda)."
      rw [← hn]
      Hint "El siguiente paso lo demostraremos por inducción
      sobre `{n}`; pero como `{hn}` afirma cosas sobre `{n}`,
      el demostrados intentará usarlo en el paso de inducción, y eso
      nos dificultará el trabajo. Así que será mejor olvidarnos por el momento
      de `{hn}`.

      Teclea `clear {hn}`."
      clear hn
      Hint "Ahora ya podemos hacer la demostración por inducción sobre `{n}`.

      Teclea `induction' {n} with n hnU`."
      induction' n with n hnU
      · Hint (hidden := true) "Para la demostración del caso base, podemos
        aplicar `{hBx}`."
        apply hBx
        Hint "Si simplificamos la definición de `{g}`,
        debería ser evidente que `{g} 0 = {f} 0`. Teclea `simp [{g}]`."
        simp only [zero_eq, rec_zero, mem_setOf_eq, exists_apply_eq_apply, g]
      · Hint  "Recuerda que `g ({n} + 1)` está definida
        como una intersección, así que podemos aplicar el resultado
        que nos asegura que la intersección de entornos es entorno."
        apply entornos_N3
        · Hint "Aunque la expresión del objetivo puede ser confusa, porque
          `{g}` está escrito con su definición expandida, realmente dice lo mismo
          que la hipótesis de inducción."
          Hint (hidden := true) "Teclea `exact {hnU}.`"
          exact hnU
        · Hint (hidden := true) "Observa que queremos ver que `{f} ({n} + 1)`
          es entorno de `{x}`. `{hBx}` nos asegura que ciertos conjuntos lo son,
          así que podemos probar a aplicarlo."
          apply hBx
          Hint (hidden := true) "Hay que demostrar que existe un natural, tal que
          al aplicarle `{f}` obtenemos `{f} ({n} + 1)`, ¿cual puedes usar?"
          use n + 1
    · Hint (hidden := true) "Como hay que ver algo para todo entorno de `{x}`,
      toma uno arbitrario con `intro`."
      intro N hN
      Hint (hidden := true) "Como ahora tenemos un entorno de `{x}`, podemos
      obtener una nueva hipótesis aplicándole `{hB}` (con `have`)."
      have hBx22 := hB N hN
      Hint (hidden := true) "Ahora, gracias a `{hBx22}` sabemos que existe
      un cierto elemento de la familia contenido en `{N}`, elige uno (y
      lo que podemos afirmar sobre él) con `choose`."
      choose B1 hB1 hB11 using hBx22
      Hint (hidden := true) "`{hB1}` nos asegura que existe al menos
      un natural con ciertas propiedades. Elige uno con `choose`."
      choose n hn using hB1
      Hint (hidden := true) "Puede ser útil simplificar la expresión del objetivo."
      simp only [mem_setOf_eq, exists_exists_eq_and]
      Hint (hidden := true) "¿Qué número natural podemos usar?"
      use n
      Hint (hidden := true) "Toma un elemento de `{g} {n}` arbitrario
      con `intro`."
      intro y hy
      Hint (hidden := true) "Como `{hB11}` nos asegura que ciertos
      puntos están en `{N}`, podemos probar a aplicarlo."
      apply hB11
      Hint (hidden := true) "Usa `{hn}` para reescribir el objetivo."
      rw [← hn]
      Hint "Esto habrá que demostrarlo por inducción. Teclea `induction' {n} with m hm`."
      induction' n with m hm
      · Hint (hidden := true) "Observa que, por como hemos definido
        `{g}`, `{g} 0 = {f} 0`, así que el objetivo es exactamente `{hy}`."
        exact hy
      · Hint (hidden := true) "Obserba que `{hy}` nos dice que `{y}`
        está en la intersección de dos conjuntos. Puedes separar esa afirmación
        en dos con `choose` o `cases'`."
        choose hm1 hm2 using hy
        Hint (hidden := true) "Ahora el objetivo es exactemente `{hm2}`."
        exact hm2
  · Hint (hidden := true) "Toma un natural arbitrario con `intro`."
    intro n
    Hint (hidden := true) "Simplificando la expresión de `{g}`
    debería ser suficiente para demostrar el objetivo.
    Teclea `simp [g]`."
    simp only [Nat.rec_add_one, inter_subset_left, g]

end topo
