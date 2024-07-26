import Game.Levels.EspaciosMetricos.ContinuidadEntornos

variable {X : Type} {Y : Type} [espacio_metrico X] [espacio_metrico Y]
open espacio_metrico

World "EspaciosMetricos"
Level 12
Title "Caracterización de continuidad mediante abiertos."

Introduction "En este nivel vamos a ver una caracterización de la continuidad de una
función entre espacios métricos, en términos de abiertos.

Para ello, usaremos los resultados `caracterizacion_d_continua_en_entornos`
y `caracterizacion_d_continua_en_bola` de los niveles anteriores.

En este nivel usaremos la *preimagen* de un conjunto por una aplicación: dada una aplicación
$ f : X \\to Y$, y un conjunto $U \\subseteq Y$, $f ^\\{-1\\}(U)$ es el conjunto de los
elementos de $X$ cuya imagen está en $U$. Este conjunto se denota en lean como $f ⁻¹' U$.
Para obtener el símbolo `⁻¹` teclea `\\-1`.

El lema `def_preimagen` caracteriza los puntos que están en la preimagen de un conjunto.
"

lemma def_preimagen {X Y: Type} (f : X → Y) (U : Set Y) (x : X) : x ∈ f ⁻¹' U ↔ f x ∈ U := by
  rfl

/--
Dada una aplicación `f : X → Y`, un conjunto `U` de `Y`, y un elemento `x` de `X`,
`def_preimagen f U x`  nos dice que `x ∈ f ⁻¹' U ↔ f x ∈ U`
-/
TheoremDoc def_preimagen as "def_preimagen" in "lemas-definición"

NewTheorem def_preimagen

/--
Una función entre espacios métricos es continua si y solo si la preimagen de cualquier
abierto métrico es abierto métrico.
-/
TheoremDoc caracterizacion_d_continua_abiertos as "caracterizacion_d_continua_abiertos" in "Espacios Métricos"

/--
Una función entre espacios métricos es continua si y solo si la preimagen de cualquier
abierto métrico es abierto métrico.
-/
Statement caracterizacion_d_continua_abiertos (f : X → Y) :
    d_continua f ↔ ∀ (V : Set Y), abierto_metrico V → abierto_metrico ( f ⁻¹' V) := by
  fconstructor
  · intro h V hV
    intro x hx
    have h2 := h x
    rw [caracterizacion_d_continua_en_entornos] at h2
    have h3 := hV (f x) hx
    have h4 := h2 V h3
    choose U hU hUV using h4
    choose r hr0 hr using hU
    use r
    fconstructor
    · exact hr0
    · intro y hy
      apply hUV
      use y
      fconstructor
      · apply hr
        exact hy
      · trivial

  · intro h
    intro x
    rw [caracterizacion_d_continua_en_bola]
    intro r hr0
    have h2 := h (bola (f x) r) (bola_abierta (f x) r hr0)
    have hx : f x ∈ bola (f x) r
    · have h0 := d1 (f x)
      rw [def_bola]
      linarith
    have h3 := h2 x hx
    choose d hd0 hd using h3
    use d
    fconstructor
    · exact hd0
    · intro y hy
      choose x1 hx1 hx1y using hy
      have hyb := hd  hx1
      rw [def_preimagen] at hyb
      rw [hx1y] at hyb
      exact hyb
