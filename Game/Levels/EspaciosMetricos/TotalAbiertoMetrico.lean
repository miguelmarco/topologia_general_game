import Game.Levels.EspaciosMetricos.VacioAbiertoMetrico

variable {X : Type} [espacio_metrico X]
open espacio_metrico Set

World "EspaciosMetricos"
Level 5

Title "El conjunto total es un abierto métrico"

Introduction "Ahora veremos otro ejemplo simple de un conjunto que es un abierto métrico:
el conjunto formado por todos los puntos del espacio métrico (llamado *conjunto total*
o *conjunto universal*).

En este nivel introducimos la táctica `trivial`, que se usa para demostrar afirmaciones que
son ciertas por definición.
"



/--
El conjunto total es un abierto métrico.
-/
TheoremDoc total_abierto_metrico as "total_abierto_metrico" in "Espacios Métricos"

/--
La táctica `trivial` demuestra enunciados que son ciertos por definición.
-/
TacticDoc trivial

NewTactic trivial


/--
El conjunto total es un abierto métrico.
-/
Statement total_abierto_metrico : abierto_metrico (univ : Set X) := by
  Hint (hidden := true) "Si no sabes como empezar, puedes desarrollar la definición de abierto métrico."
  rw [def_abierto_metrico]
  Hint (hidden := true) "Como hay que demostrar algo para todo `x`, puedes tomar uno arbitrario."
  intro x
  Hint (hidden := true) "Puedes introducir el antecedente como nueva hipótesis con `intro h`."
  intro h
  Hint (hidden := true) "Desarrolla la definición de entorno métrico."
  rw [def_entorno_metrico]
  Hint "Como hay que demostrar que existe un cierto `r > 0`, habrá que dar uno, para ello puedes usar
  la táctica `use`.

  ¿Se te ocurre qué `r` puedes usar? "
  Hint (hidden := true) "Como cualquier bola va a estar contenida en el total, puedes usar cualquier
  número real positivo. El primero que viene a la mente es `1`. Así que puedes usar `use 1`."
  use 1
  Hint (hidden := true) "Ahora tu objetivo es demostrar dos afirmaciones. Las puedes separar en dos
  con `fconstructor`."
  fconstructor
  · Hint (hidden := true) "Recuerda que la táctica `linarith` puede demostrar (des)igualdades
    mediante aritmética lineal."
    linarith
  · Hint (hidden := true) "La forma natural de demostrar que un conjunto está contenido en otro, debes tomar un
    elemento arbitrario del primero y demostrr que está en el segundo. Usa `intro y`."
    intro y
    Hint (hidden := true) "Puedes introducir el antecedente como hipótesis con `intro hy`."
    intro hy
    Hint "Que un elemento de `X` está en el conjunto universal, es cierto por definición."
    Hint (hidden := true) "Usa `trivial`."
    trivial
