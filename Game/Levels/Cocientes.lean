import Game.Levels.Cocientes.CocienteT1
Title "Cocientes"

Introduction "
En este mundo veremos cómo dotar de estructura de
espacio topológico al cociente de un espacio topológico por una relación
de equivalencia.

Para ello, necesitamos algunas nociones cocientes de conjuntos.

En este contexto, típicamente `X` será un espacio topológico, y `R`
una relación de equivalencia definida en `X`. Esto se denotará como `R : Equiv X`.

El conjunto cociente se denota como `X /' R' (notar que usamos un apóstrofe
para distinguir de la operación de división). Dado un elemento `x` de `X`,
su clase de equivalencia se denota como `⟦x⟧` (los símbolos `⟦`y `⟧`
se obtienen tecleando `\\[[` y `\\]]`). La aplicación `π : X → (X /' R)`
es la que envia cada `x` a `⟦x⟧`. El teorema `def_pi` establece esta
definición.

El hecho de que dos elementos de `x` estén relacionados por la relación
se denota `x ≈ y` (el símbolo `≈` se obtiene tecleando `\\approx`). El teorema
`def_clase_equiv` dice que `⟦x⟧ = ⟦y⟧ ↔ x ≈ y`.

Cada clase de equivalencia de `X /' R` tiene un representante. El teorema
`existe_representante` afirma esto mismo.

El conjunto cociente `X /' R` tiene una estructura de espacio topológico,
donde un conjunto `S` es de abierto si  `{x | ⟦x⟧ ∈ S}` es un abierto. El
teorema `def_abierto_cociente` establece este hecho.
"
