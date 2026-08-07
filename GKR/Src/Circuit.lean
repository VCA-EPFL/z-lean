import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fin.Tuple.Basic

/--
A gate in a layered circuit

k is the width of the layer below (layer below has 2 ^ k gates)
-/
inductive Gate (k : ℕ ) where
  | add : Fin (2 ^ k ) → Fin (2 ^ k ) → Gate k
  | mul : Fin (2 ^ k ) → Fin (2 ^ k)  → Gate k
  deriving Repr

/--
The whole circuit where 2 ^ k is the number of nodes in each layer

d is the depth of the circuit
-/
structure Circuit (k : ℕ ) (d : ℕ) where
  gate : Fin d → Fin (2 ^ k) → Gate k

/-
Peel the layer of a circuit
-/
def Circuit.tail
 {k : ℕ }
 {d : ℕ}
 (c : Circuit k (d + 1)) : Circuit k d where
  gate := fun i z => c.gate i.succ z -- i.succ takes in Fin n and returns Fin n + 1

/--
Evaluate one layer of an arithmetic circuit
-/
def evalLayer
 {k : ℕ}
 {F : Type}[Field F]
 (thisLayer : Fin (2 ^ k) → Gate k)
 (lowerLayer : Fin (2 ^ k) -> F)
 : Fin (2 ^ k) → F :=
 fun z =>
  match thisLayer z with
  | Gate.add a b => lowerLayer a + lowerLayer b
  | Gate.mul a b => lowerLayer a * lowerLayer b

/--
Evaluate the whole arithmetic circuit
-/
def evalCircuit
  {k : ℕ }
  {d : ℕ }
  {F : Type} [Field F]
  (c : Circuit k d)
  (input : Fin (2 ^ k) → F)
  : Fin (2 ^ k) → F :=
  match d , c with
  | 0, _ => input
  | (_ + 1), c => evalLayer (c.gate 0) (evalCircuit c.tail input)

/--
get a value at every layer
-/
def layerValues
  { k : ℕ }
  { d : ℕ }
  {F : Type}[Field F]
  (c : Circuit k d)
  (input : Fin (2 ^ k) → F)
  : (Fin (d + 1)) → (Fin (2 ^ k)) → F :=
  match d, c with
  | 0, _ => fun _ => input
  | _ + 1, c =>
    let below := layerValues c.tail input
    Fin.cons (evalLayer (c.gate 0) (below 0)) below

/--
add predicate
at level l, we have a gate z and at level l + 1 we have gates x and y
we return wether z is an add gate
-/
def addPred
  {k d : ℕ}
  (F : Type)[Field F]
  (c : Circuit k d)
  (l : Fin (d))
  (z x y : Fin (2 ^ k)) : F :=
  match c.gate l z with
  | Gate.add a b => if a = x ∧ b = y then 1 else 0
  | Gate.mul _ _ => 0

/--
mul predicate
at level l, we have a gate z and at level l + 1 we have gates x and y
we return wether z is a mul gate
-/
def mulPred
  {k d : ℕ}
  (F : Type)[Field F]
  (c : Circuit k d)
  (l : Fin (d))
  (z x y : Fin (2 ^ k)) : F :=
  match c.gate l z with
  | Gate.mul a b => if a = x ∧ b = y then 1 else 0
  | Gate.add _ _ => 0
