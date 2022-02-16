/- El segundo módulo de este minicurso trata de los 
números naturales. Es decir, ahora vamos a tratar con
objetos matemáticos más concretos, no sólo con proposiciones
lógicas -/

/- Empezamos definiendo a los números naturales. Existen varias
formas de definir los números naturales, en Lean y en este 
minicurso usaremos los axiomas de Peano. -/

/- En esta hoja vamos a importar unas definiciones de Mathlib.
Estas no las vamos a ocupar hasta al final, pero las incluímos
al principio porque Lean requiere que todas las importaciones 
ocurran al principio de la hoja. -/
import algebra.big_operators.intervals

/- Definimos nuestro propio espacio de nombres para trabajar 
con nuestras propias definiciones: -/
namespace smf22

/- Ahora definimos un número natural según los axiomas de Peano: -/
inductive natural
| cero : natural -- El número cero (`0`) en un número natural
| suc (n : natural) : natural -- Si `n` es un número natural, 
                              -- su sucesor también.

/- Hemos definido la estructura de forma inductiva: tenemos un caso base, 
cero, que dice que `cero` es un numero natural, y luego tenemos el caso 
inductivo, `suc` (de sucesor), que dice que si `n` es un número natural,
también su sucesor es un número natural.  El sucesor de un número 
natural `n` es `n + 1`.

Lean tiene una forma generalizada de inducción ya incluída. Al decir
`inductive` para definir un objecto matemático, Lean entiende dos cosas:
 - La definición no es circular, es inductiva
 - Lean genera un principio de inducción para estos objetos.

Peano originalmente tenía mucho otros axiomas, como
que todo natural es igual a sí mismo, ` ∀ x : natural, x = x`.
Estos axiomas ya los tenemos por la base lógica en Lean y no hace
falta repetirlos para definir los números naturales.
 -/

 /- Podemos definir el número 1, por ejemplo: -/
def uno := natural.suc natural.cero

/- Lean ocupa un punto `.` para acceder a los nombres definidos.
Cómo vamos a estar trabajando con los números naturales, es muy
tedioso tener que escribir `natural.suc` cada vez; en vez, 
le decimos a Lean que "abra las definiciones, para que no tengamos
que escribir `natural` cada vez.  "-/
open natural

/- y podemos definir dos -/
def dos := suc (suc cero)

/- Demostramos que 1 + 1 = 2. -/
example : suc uno = dos := 
begin
  refl -- por definición
end

/- Por el momento no hemos definido la suma, interpretamos al 
sucesor como `+ 1`, pero no está realmente definido. Es más, 
es al revez: definimos la suma usando al sucesor. -/

def suma : natural → natural → natural
| a  cero     := a
| a  (suc b) := suc (suma a b)


#check suma uno uno

/- Con esta definición, para escribir la suma de dos números
`a` y `b`, tendríamos que escribir `suma a b`. Esto se puede 
volver tedioso rápidamente. Afortunadamente, Lean nos permite definir
nuestra propia notación para evitar esta confusion y tedio.
-/

infix ` + `:60 := suma 

/- Lean dice `infix` porque el símbolo `+` va entre sus argumentos,
no como sufijo o prefixo. El 60 es la "precedencia" del operador, 
sirve para desambiguar expresiones como 2 ⬝ 3 + 5, que podrían 
significar (2 ⬝ 3) + 5 ó 2 ⬝ (3 + 5). Por convención, lo 
interpretamos como la primera opción, pero a Lean hay que 
enseñarle esta convención también! -/

#check uno + uno -- ahora podemos escribirlo así

/- Regresamos a nuestro "teorema": 1 + 1 = 2 -/
theorem uno_mas_uno : uno + uno = dos :=
begin
  unfold uno, -- cual es la definición de uno?
  unfold dos, -- cual es la definición de dos?
  unfold suma, -- cual es la definición de la suma?
end

theorem uno_mas_uno' : uno + uno = dos :=
begin
  refl, -- Sigue siendo verdadero por definición
end

-- Vamos a trabajar con un par de variables (numeros naturales)
variables (l m n : natural)

/- Igual, por definición, n + 0 = n. 
Cuando es un solo paso, podemos decir `by` en vez de
usar `begin` y `end`.  -/
theorem suma_cero : n + cero = n := by refl 
 
/- Ahora que pasa con lo opuesto (`cero + n = n`)?
Esto no funciona por definición.  Cual es la diferencia entre estos dos? 
De hecho, la única forma de demostrarlo es por inducción!
-/
theorem cero_suma : cero + n = n :=
begin
 induction n with n hi,
 -- caso base (cero)
 {
   refl,
 },
 {
   unfold suma, --definición de suma
   rw hi, --hipótesis de inducción
 }
end

/- Muy similar al caso con cero, como hemos visto,
 `suc n` es `n + 1`, por definición. Que pasa con `1 + n`? -/
theorem n_mas_uno : suc n = n + uno := by refl

/- Un pequeño ejercicio: -/
theorem uno_mas_n : uno + n = suc n := 
begin
  sorry,
end

/- un ejericico un poco más interesante: -/
theorem suma_asociativa : (l + m) + n = l + (m + n)  :=
begin 
 sorry,
end

/- Que tal si hacemos el caso más general, n + m = m + n? -/
theorem suma_conmutativa : n + m = m + n := 
begin
  induction n with n hi,
  {
    rw cero_suma,
    rw suma_cero,
  },
  {
    rw ← uno_mas_n,
    rw ← (suma_asociativa m uno n),
    rw ← n_mas_uno,
    rw ← uno_mas_n,
    rw suma_asociativa,
    rw suma_asociativa,
    rw hi,
  }
end

/- Este lemma claramente es consecuencia de la distributividad
y asociatividad de la suma, sin embargo resulta ser útil tenerlo
 aparte. -/
lemma suma_izq_conm : n + (m + l) = m + (n + l) :=
begin
  induction n with n hi,
  {
    rw cero_suma,
    rw cero_suma,
  },
  {
    rw ← suma_asociativa,
    rw suma_asociativa,
    rw suma_conmutativa,
    rw suma_asociativa,
    rw (suma_conmutativa (suc n) l),
  }
end
/- En este último caso tuvimos que decirle a Lean que 
numeros usar para aplicar la conmutatividad, lo cual podemos hacer
dandole los argumentos explicitamente y poniendo todo en parentesis,
 como hicimos aquí. -/

/- Vemos como podemos empezar a construir la teoría de los números 
naturales en base a los axiomas de Peano. Vamos al siguiente paso:
como definiríamos la multiplicación? -/

def mul : natural → natural → natural
| m cero := cero
| m (suc n) := mul m n + m

/- definimos la multipliciación. Podemos usar ambos, `⬝` ó `*`. -/
infix ` * `:70 := mul 
infix ` ⬝ `:70 := mul 

-- a la derecha otra vez es por definición
theorem mul_cero : n * cero = cero := by refl

/- para la demostración por la izquierda necesitamos 
ahora saber algo de la suma también! -/
theorem cero_mul : cero * n = cero := 
begin
 induction n,
 refl,
 unfold mul,
 rw suma_cero,
 exact n_ih,
end

/- El siguiente objetivo aquí será demostrar la asociatividad y
 comutatividad de la muliplicación, así como la ley distributiva.
 Esto lleva mucho tiempo.  -/

lemma suc_mul : (suc n) * m = (n * m) + m :=
begin
  induction m with m hi,
  refl,
  unfold mul,
  rw hi,
  rw n_mas_uno,
  rw suma_asociativa,
  rw (suma_conmutativa (n + uno) m),
  rw suma_asociativa,
  rw (uno_mas_n m),
  rw suma_asociativa,
end

-- La otra dirección es trivial por definición!
lemma mul_suc : n * suc m = n * m + n := by refl

/- Con esto podemos demostrar las leyes distributivas
   para relacional la suma y la multiplicación:
-/
theorem distrib_izq : n * (m + l) = n * m + n * l :=
begin
induction n with n hi,
{
  simp [cero_mul], -- que pasa si en vez hacemos rw cero_mul?
  refl,
},
{
  simp [suc_mul],
  rw hi,
  simp [suma_asociativa, suma_conmutativa, suma_izq_conm],
}
end

theorem distrib_der : (n + m) * l = n * l + m * l :=
begin 
  induction l with l hi,
  refl,
  {
  simp [mul_suc, hi],
  simp [suma_asociativa, suma_conmutativa, suma_izq_conm],
  }
end

theorem mul_asociativa  : (n * m) * l = n * (m * l) :=
begin
  induction l with l hi,
  refl,
  simp [mul_suc, distrib_izq, hi],
end

/- La tarea: demuestre que la multiplicaicón es conmutativa! -/
theorem mul_conmutativa : n * m = m * n :=
begin
  sorry,
end

/- Hasta aquí hemos ido construyendo la teoría de los números naturales
paso a paso. Sin embargo, Lean ya la conoce, por supuesto! Vamos a cerrar
nuestro espacio de nombres extra y ver como funciona esto -/
end smf22

infix ` + `:60 := nat.add 

#check nat
/- Para demostrar un poco como Lean puede ser mas poderoso, 
demostraremos una propiedad de los numeros pares usando
un poco mas de automatización -/
theorem producto_par : ∀ m n : ℕ, even n → even (m * n) :=
begin
  intros m n hpar,
  unfold even at hpar, -- cual es la definición de par?
  /- En la hoja de lógica no vimos cuantificadores, pero no es muy 
  complejo. Si tenemos la existencia de un objeto con una propiedad,
  podemos separarla igual que en los otros casos usando `cases`: -/
  cases hpar with k hk, 
  use (m * k), -- demostramos la existencia explicitamente
  rw hk,
  ring, -- lean tiene tacticas mas poderosas, como `ring`
end