/- Este tercer y último módulo trata las bases de teoría de grupos.
  Así como construimos un poco de la teoría de los numeros 
  naturales a base de los axiomas de peano, construiremos
  la teoría de grupos a base de los axiomas de un grupo. -/

-- Otra vez usamos nuestros propios nombres porque Lean ya conoce los grupos.
--namespace smf22

/-
Para definir un grupo vamos a usar definiciones que ya existen en Lean.
Específicamente, vamos a usar las propiedades:

 - `has_mul G`, que quiere decir que `G` tiene una multplicación, es decir
   una operación `* : G → G → G` (léase también como `G × G → G`)
 - `has_one G`, que quiere decir que `G` tiene una unidad, es decir un 
   elemento `1 : G` (léase también como `1 ∈ G`)
 - `has_inv G`, que quieren decir que tiene una operación de inversa, es
   decir `⁻¹ : G → G`.

Cabe mencionar que no sabemos más de estas funciones/estos elementos que
su existencia: no tenemos propiedades como la asociatividad de la 
multiplicación (magma) o la relación con la unidad (monoide).
-/

class grupo (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_asoc : ∀ (a b c : G), a * b * c = a * (b * c))
(unidad_mul : ∀ (a : G), 1 * a = a)
(mul_inv_izq : ∀ (a : G), a⁻¹ * a = 1)

/-
La definición de `grupo` quiere entonces decir que tenemos estas tres definiciones,
la multiplicación, unidad e inversa, y que estas cumplen las propiedades:
 - assocatividad   de la multiplicación: `mul_assoc`
 - `1` es unidad por la izquierda: `unidad_mul`
 - la multiplicación con el inverso por la izquierda da la unidad: `mul_inv_izq` 

Tal vez le parecerá un poco extraña esta definición, generalmente tenemos
propiedades que parecen ser más fuertes (multiplicación por ambos lados).

Sin embargo, como vamos a demostrar aquí, estas propiedades alcanzan.
Entonces en Lean definimos un grupo con estas propiedades (aparentemente)
más débiles para hacer más fácil el demostrar que alguna estructura es un grupo.

Ahora vamos a demostrar que estos axiomas implican (y por tanto son equivalentes)
a la versión de ambos lados que conocemos. Es decir, vamos a demostar:

- `mul_unidad (a : G) : a * 1 = a`
- `mul_der_inv (a : G) : a * a⁻¹ = 1`

-/
namespace grupo
-- Vamos a declarar primero una variable `G` que sea un grupo. Lo hacemos así:
variables {G : Type} [grupo G]

/- Para demostrar las versiones "derechas" de los axiomas, primero tenemos
que demostrar otras propiedades útiles que son consecuencia de los axiomas,
como la siguiente: -/
lemma mul_izq_cancel (a b c : G) : a * b = a * c → b = c := 
begin
 intros Habac,
 calc b = 1 * b         : by rw unidad_mul
    ... = (a⁻¹ * a) * b : by rw mul_inv_izq
    ... = a⁻¹ * (a * b) : by sorry -- siga con `rw` + el axioma indicado
    ... = a⁻¹ * (a * c) : by sorry
    ... = (a⁻¹ * a) * c : by sorry
    ... = 1 * c         : by sorry
    ... = c             : by sorry,
end 

/- Aquí vemos una nueva tátctica, `calc`, que nos sirve para calcular
una serie de equaciones, demostrando en cada paso que axioma usamos. 

Demostramos otro lemma ligeramente técnico: que podemos multiplicar
por la izquierda con `x` y cancelar un producto de `a` con `a⁻¹`.
Este lo hacemos directamente con `rw`, para ver la comparación con
el `calc` arriba:  -/

lemma mul_eq_de_eq_inv_mul {a x y : G} : x = a⁻¹ * y →
 a * x = y :=
begin
  intro h,
  apply mul_izq_cancel a⁻¹,  --dexemos decire
  rw h,
  rw ← (mul_asoc (a⁻¹) a  _), -- usamos `_` para que Lean infiera el argumento
  rw (mul_inv_izq a ),
  rw unidad_mul,
end

-- Declaramos un par de variables para no estar escribiendolas cada vez:
-- Sean `a,b,c,x,y` "elementos" del grupo `G`.
variables (a b c x y : G)

/- Ahora vamos a demostrar los axiomas de grupo que faltan: -/

@[simp] theorem mul_one : a * 1 = a :=
begin
  apply mul_eq_de_eq_inv_mul, -- que pasó aquí?
  rw mul_inv_izq,
end

/- Esta demostracion es similar, hagámosla como ejercicio: -/
@[simp] theorem mul_der_inv : a * a⁻¹ = 1 :=
begin
  sorry
end

/- Vamos a discutir esta palabra clave aquí, `@[simp]`: 

## El simplificador de Lean

Un humano ve `a * a⁻¹` en teoría de grupos e inmedatamente lo reemplaza por `1`.
Ahora vamos a "entrenar" una IA simple, llamada `simp`, para que haga lo mismo.
El simplificador de Lean, `simp`, es lo que se llama un sistema de 
reescritura de términos. Esto quiere decir que cuando le enseñamos varios 
teoremas con la forma `A = B` o `P ↔ Q` (al marcarlos con el atributo  `@[simp]`)
y le damos un objetivo complicado, como 
`ejemplo : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1`
entonces `simp` va a tratar de usar la táctica `rw` lo mas que pueda, usando
los lemmas que se le han enseñado, intendando simplificar el objetivo.
Si lo logra resolver completamente, pues excelente! Si no, pero sentimos que
lo debería poder haber hecho, entonces debemos marcar más lemmas con `@[simp]`.
`simp` sólo debe ser usado para cerrar objetivos completamente. Ahora vamos a
entrenar al simplificador para resolver el ejemplo de arriba (de hecho, lo vamos
a entrenar para que reduzca un elemento arbitrario de un grupo libre a una forma
normal única, para que pueda resolver igualdades que son verdaderas de todos los
grupos, como el ejemplo arriba).

## Nota importante
El simplificador de Lean hace una serie de reescrituras, cada una reemplaza algo
con algo mas. Pero el simplificador siempre va a reescribir de izquierda a derecha!
Si le decimos que `A = B` es un lemma `simp`, entonces va a reemplazar las `A`s 
con `B`s, pero nunca va a reemplazar `B`s con `A`s. Si marcamos una demostración
de `A = B` con `@[simp]` y también marcamos una demostración de `B = A` con simp,
entonces el simplificador se va a trabar en un bucle infinito cuando encuentre un
`A`! En ese sentido, no debemos pensar en igualdad como algo simétrico aquí.
Porque el simplificador trabaja de izquierda a derecha, una regla práctica (a ojo
de buen cubero) es que si `A = B` es un lemma de `simp`, entonces `B`
probablemente debería ser más simple que `A`! No es coincidencia que en los
teoremas siguientes
`@[simp] theorem mul_unidad (a : G) : a * 1 = a`
`@[simp] theorem mul_inv_der (a : G) : a * a⁻¹ = 1`
el lado derecho es más simple que el izquierdo. Sería un desastre
el marcar `a = a * 1` con la viñeta de `@[simp]` -- puede ver por que?
Entrenemos al simplificador de Lean! Vamos a mostrarle los axiomas de
un grupo ahora. Ya los definimos, así que tenemos que marcarlos retrospectivamente
con el atributo  `@[simp]`.
-/

attribute [simp] unidad_mul mul_inv_izq mul_asoc

/-
Ahora le vamos a mostrar al simplifcador los siguientes lemmas:
`inv_mul_cancel_izq : a⁻¹ * (a * b) = b`
`mul_inv_cancel_izq : a * (a⁻¹ * b) = b`
`inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹`
`unidad_inv : (1 : G)⁻¹ = 1`
`inv_inv : (a⁻¹)⁻¹ = a`
Note que en cada caso, el lado derecho es más simple que el izquierdo.
Trate de usar al sipmlificador en sus demostraciones. Vamos a resolver
la primera juntos:
-/

@[simp] lemma inv_mul_cancel_izq : a⁻¹ * (a * b) = b :=
begin
  rw ← mul_asoc, -- el simplificador no va a hacer esto (en esta dirección)
                  -- así que lo hacemos manualmente
  simp, -- el simplificador lo toma desde aquí, 
        -- reescribiendo `a⁻¹ * a` a `1` y luego `1 * b` a `b`
end

@[simp] lemma mul_inv_cancel_izq : a * (a⁻¹ * b) = b :=
begin
  sorry
end

@[simp] lemma inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  sorry
end

@[simp] lemma unidad_inv : (1 : G)⁻¹ = 1 :=
begin
  sorry
end

@[simp] lemma inv_inv : a ⁻¹ ⁻¹ = a :=
begin
  sorry
end

/-
La razón por la que escogimos estos cinco lemas en particular es que
los sistemas de reescritura de términos los entendemos bien en
la ciencia de la computación. En especial, existe un algoritmo llamado 
el algoritmo de Knuth-Bedix, al cual, si le damos los tres axiomas de
grupo que usamos, produce lo que se llama un "sistema de reescritura
de términos confluente y Noetheriano", que transforma cualquier término
en una forma normal única. El sistema entonces produce precisamente
los lemmas de `simp` que hemos demostrado anteriormente. Vea:
https://en.wikipedia.org/wiki/Word_problem_(mathematics)#Example:_A_term_rewriting_system_to_decide_the_word_problem_in_the_free_group
(en inglés) para más información. No vamos a hablar del algoritmo de
Knuth-Bendix por que realmente trata de ciencias de la computación,
pero al parecer, si se le aplicamos a anillos polinomiales entonces
obtenemos el algoritmo de Buchberger para computar bases de Gröbner.
-/

-- Ahora intentemos nuestro ejemplo:
example : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp 

-- El simplificador lo resuelve!

-- Intente con sus propias identidades. `simp` las resolverá todas!
/- Probos lo que hemos aprendido con una demostración más de un Lemma
 un poco mas interesante -/
@[simp] theorem inv_inj_iff {a b : G}: a⁻¹ = b⁻¹ ↔ a = b :=
begin
  sorry
end   

end grupo
