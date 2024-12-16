import Game.Levels.Numerabilidad.Aglomeracion

World "Numerabilidad"
Level 4
Title "Subsucesiones truncadas."

Introduction "
Dada una sucesión `s`, una subsucesión `s'` es *truncada* si existe un `n₀`
tal que `s' n = s (n + n₀)`.

Veamos que los límites de una subsucesión truncada coinciden con los de la
sucesión inicial.

En este nivel necesitaremos ver algunos hechos que involucran cálculos
aritméticos con números naturales, que no siempre se pueden hacer con `linarith`
(ya que, por ejemplo, la resta en los números naturales no está
definida igual que en los enteros o los reales). Para estos casos, podemos usar
la táctica `omega`, que puede verse como una versión de `linarith` especializada
en los números naturales (en particular, puede gestionar la resta de naturales,
y algunas propiedades de divisibilidad).
"

/--
La táctica `omega` puede demostrar automáticamente algunas afirmaciones
sobre números naturales (en particular, és útil para demostrar afirmaciones
que involucran restas y divisibilidad).
-/
TacticDoc omega

NewTactic omega

namespace topo
open topo espacio_topologico Set Function Nat
variable {X : Type} [espacio_topologico X]

def truncada (s : ℕ → X) (s' : ℕ → X) := ∃ n0, ∀ n, s' n = s (n + n0)

/--
Dadas dos sucesiones `s` y `s'`, decimos que `s'` es una sucesión truncada
de `s` si existe un `n₀` tal que `s' n = s (n + n₀)`.
-/
DefinitionDoc truncada as "truncada"

theorem def_truncada (s : ℕ → X) (s' : ℕ → X) : truncada s s' ↔ ∃ n0, ∀ n, s' n = s (n + n0) := by
  rfl

/--
Dadas dos sucesiones `s` y `s'`, `def_truncada s s'` dice que
`truncada s s' ↔ ∃ n0, ∀ n, s' n = s (n + n0)`.
-/
TheoremDoc topo.def_truncada as "def_truncada" in "Numerabilidad"

NewTheorem topo.def_truncada

/--
Si `s'` es una sucesión truncada de `s`, un punto es límite de `s'` si y solo si
es límite de `s`.
-/
TheoremDoc topo.limite_truncada as "limite_truncada" in "Numerabilidad"

Statement limite_truncada {s s' : ℕ → X} (h : truncada s s') (x : X) :
    limite s' x ↔ limite s x := by
  Hint (hidden := true) "Puede ser útil reescribir la definición de truncada en `{h}`."
  rw [def_truncada] at h
  Hint (hidden := true) "Como `{h}` asegura que existen números naturales
  con ciertas propiedades, puedes elegir uno con `choose`."
  choose n0 hn0 using h
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Introduce el antecedente como una hipótesis, con
    `intro`."
    intro hx
    Hint (hidden := true) "Puedes reescribir la definición de límite en el objetivo
    y en `{hx}`."
    rw [def_limite] at hx ⊢
    Hint (hidden := true) "Puedes tomar un abierto arbitrario con `intro`."
    intro U hU hxU
    Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
    aplicando `{hx}` a `{U}`, `{hU}` y `{hxU}`."
    have h2 := hx U hU hxU
    Hint (hidden := true) "Ahora `{h2}` nos asegura que existen ciertos números
    naturales. Elige con uno con `choose`."
    choose n1 hn1 using h2
    Hint (hidden := true) "¿Qué número podemos usar?"
    use n1 + n0
    Hint (hidden := true) "Toma un número arbitrario con `intro`."
    intro n hn
    Hint (hidden := true) "Para poder usar `{hn1}`, necesitamos ver
    que `{n} - {n0} ≥ {n1}`. Creemos un nuevo objetivo para ello:

    teclea `have haux : {n} - {n0} ≥ {n1}"
    have haux : n - n0 ≥ n1
    · Hint "Este tipo de afirmaciones que involucran la resta de naturales,
      se pueden demostrar con `omega`."
      omega
    Hint (hidden := true) "Ahora podemos obtener (con `have`) una nueva
    hipótesis aplicando `{hn1}` a `({n} - {n0})` y `{haux}`."
    have hn2 := hn1 (n - n0) haux
    Hint (hidden := true) "Puedes usar `{hn0}` para reescribir `{hn2}`."
    rw [hn0] at hn2
    Hint "Aunque parezca claro que `{n} - {n0} + {n0} = {n}`,
    demostrarlo no es tan fácil (porque, por ejemplo, si `{n}` fuera más pequeño
    que `{n0}`, no está claro cómo gestionar la resta). Para ello, vamos a crear
    un nuevo objetivo (con `have`) para demostrar exactamente esta afirmación."
    Hint (hidden := true) "Teclea `have haux2 : {n} - {n0} + {n0} = {n}`."
    have haux2 : n - n0 + n0 = n
    · Hint "Este es el tipo de afirmaciomes que se pueden demostrar con
      `omega`."
      omega
    Hint (hidden := true) "Ahora ya podemos usar `{haux2}` para reescribir `{hn2}`."
    rw [haux2] at hn2
    exact hn2
  · Hint (hidden := true) "Introduce el antecedente con `intro`."
    intro h
    Hint (hidden := true) "Reescribe la definición de límite en `{h}` y el
    objetivo."
    rw [def_limite] at h ⊢
    Hint (hidden := true) "Toma un abierto arbitrario con `intro`."
    intro U hU hxU
    Hint (hidden := true) "Puedes obtener (con `have`) una nueva hipótesis,
    aplicando `{h}` a `{U}`, `{hU}` y `{hxU}`."
    have h2 := h U hU hxU
    Hint (hidden := true) "Gracias a `{h2}` sabes que existen números naturales
    con ciertas propiedades, elige uno con `choose`."
    choose n1 hn1 using h2
    Hint (hidden := true) "¿Qué número puedes usar?"
    use n1
    Hint (hidden := true) "Toma un natural arbitrario con `intro`."
    intro n hn
    Hint (hidden := true) "Puedes usar `{hn0}` para reescribir el objetivo."
    rw [hn0]
    Hint (hidden := true) "Se puede aplicar `{hn1}`."
    apply hn1
    Hint (hidden := true) "Esta tipo de afirmaciones se pueden demostrar tanto
    con `omega` como `linarith`."
    omega


end topo
