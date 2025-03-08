import Game.Levels.Cocientes.ComposicionSiiIdentificacion

World "Cocientes"
Level 13
Title "Identificaciones como aplicaciones abiertas."

Introduction "
Veamos ahora que una aplicación suprayectiva, continua y abierta, es una identificación.
"

namespace topo
open topo espacio_topologico Set Function

variable {X: Type} [espacio_topologico X]

variable {Y : Type} [espacio_topologico Y]

/--
Una aplicación suprayectiva, continua y abierta es una identificación.
-/
TheoremDoc topo.sup_cont_abierta_ident as "sup_cont_abierta_ident" in "Cocientes"

Statement sup_cont_abierta_ident (f : X → Y) (hsup : Surjective f) (hcont : continua f) (hab : abierta f) :
    identificacion f := by
  Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
  fconstructor
  · exact hsup
  · Hint (hidden := true) "Toma un conjunto arbitrario con `intro`."
    intro U
    Hint (hidden := true) "Separa el objetivo en dos con `fconstructor`."
    fconstructor
    · apply hcont
    · Hint (hidden := true) "Introduce el antecedente como hipótesis
      con `intro`."
      intro hfU
      Hint (hidden := true) "Puedes obtener una nueva hipótesis (con `have`)
      aplicando `{hab}` a `({f} ⁻¹' {U})` y `{hfU}`."
      have haux := hab  (f ⁻¹' U) hfU
      Hint (hidden := true) "Gracias a que `{f}` es suprayectiva, se puede
      simplificar `{haux}`. Para ello, teclea `simp [{hsup}] at {haux}`."
      simp only [hsup, image_preimage_eq] at haux
      exact haux

end topo
