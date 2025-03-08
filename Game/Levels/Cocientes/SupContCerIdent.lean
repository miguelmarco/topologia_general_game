import Game.Levels.Cocientes.SupContAbIdent

World "Cocientes"
Level 14
Title "Identificaciones como aplicaciones cerradas."

Introduction "
Veamos ahora que una aplicación suprayectiva, continua y cerrada, es una identificación.
"

namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]


/--
Una aplicación suprayectiva, continua y cerrada es una identificación.
-/
TheoremDoc topo.sup_cont_cerrada_ident as "sup_cont_cerrada_ident" in "Cocientes"

Statement sup_cont_cerrada_ident (f : X → Y) (hsup : Surjective f) (hcont : continua f) (hcer : cerrada f) :
    identificacion f := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · exact hsup
  · Hint (hidden := true) "Toma un conjunto arbitrario con `intro`."
    intro U
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · apply hcont
    · Hint (hidden := true) "Introdugce el antecedente como hipótesis
      con `intro`."
      intro hfU
      Hint (hidden := true) "Vamos e tener que usar que usar un cerrado en `X`,
      para ello, tenemos que demostrar que `({f} ⁻¹' {U})ᶜ` es cerrado.
      Crea una nueva hipótesis diciendo eso (con `have`) y pasemos a demostrarla."
      have hUcer : (f ⁻¹' U)ᶜ ∈ cerrados
      · Hint (hidden := true) "Reescribe la definición de cerrado."
        rw [def_cerrado]
        Hint (hidden := true) "Simplifica el objetivo."
        simp only [compl_involutive, Involutive.comp_self, cancela_inver]
        exact hfU
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
      aplicando `{hcer}` a `({f} ⁻¹' {U})ᶜ` y `{hUcer}`."
      have haux := hcer  (f ⁻¹' U)ᶜ  hUcer
      Hint (hidden := true) "Ahora tendremos que demostrar que `{f} '' ({f} ⁻¹' {U})ᶜ = {U}ᶜ`.
      Crea una nueva hipótesis diciendo esto (con `have`) y pasemos a demostrarla."
      have haux2 : f '' (f ⁻¹' U)ᶜ = Uᶜ
      · Hint (hidden := true) "Para ver la igualdad de conjuntos, tomemos un elemento
        arbitrario con `ext`, y veamos que pertenece a un conjunto si y solo si pertenece al otro."
        ext y
        Hint (hidden := true) "Separa el objetivo con `fconstructor`."
        fconstructor
        · Hint (hidden := true) "Introduce el antecedente con `intro`."
          intro hy
          Hint (hidden := true) "Como `{y}` está en la imagen de un conjunto,
          puedes elegir un elemento de ese conjunto cuya imagen sea `{y}` con
          `choose`."
          choose x hx1 hx2 using hy
          Hint (hidden := true) "Simplifica la expresión en `{hx1}`."
          simp only [mem_compl_iff, mem_preimage] at hx1
          Hint (hidden := true) "Puedes rescribir `{hx1}` usando `{hx2}`."
          rw [hx2] at hx1
          Hint (hidden := true) "El objetivo es exactamente `{hx1}`."
          exact hx1
        · Hint (hidden := true) "Introduce el antecedente con `intro`."
          intro hy
          Hint (hidden := true) "Puedes obtener una nueva hipótesis aplicando
          `{hsup}` a `{y}`."
          have haux2 := hsup y
          Hint (hidden := true) "Puedes elegir una preimagen de `{y}` (con `choose`)
          gracias a `{haux2}`."
          choose x hx using haux2
          Hint (hidden := true) "Para ver que `{y}` está en la preimagen
          de un conjunto, tienes que dar un elemento cuya imagen sea `{y}`.
          ¿Cual puedes usar?"
          use x
          Hint (hidden := true) "Separa el objetivo con `fconstructor`."
          fconstructor
          · Hint (hidden := true) "Simplifica el objetivo."
            simp only [mem_compl_iff, mem_preimage]
            Hint (hidden := true) "Prueba a usar `{hx}` para reescribir el objetivo."
            rw [hx]
            Hint (hidden := true) "El objetivo es exactamente `{hx}`."
            exact hy
          · exact hx
      Hint (hidden := true) "Ahora puedes reescribir `{haux}` usando `{haux2}`."
      rw [haux2] at haux
      Hint (hidden := true) "Prueba a reescrivir la definición de cerrado en
      `{haux}`."
      rw [def_cerrado] at haux
      Hint (hidden := true) "Simplifica `{haux}`."
      simp only [compl_involutive, Involutive.comp_self, cancela_inver] at haux
      exact haux


end topo
