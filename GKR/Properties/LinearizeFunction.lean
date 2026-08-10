import GKR.Src.Circuit
import GKR.Src.LinearizeFunction


namespace CPoly.CMvPolynomial

/--
Just a little helper for the proof below
-/
def toPoint {k : ℕ} {F : Type} [Field F] (w : Index k) : Fin k → F :=
  fun i => if w i then 1 else 0

/--
A helper for function_linerization_agrees
-/
lemma eval_sum_eq_sum_eval
{k : ℕ}
{F : Type}[Field F][BEq F][LawfulBEq F]
(g : Index k → CMvPolynomial k F)
(inputs : Fin k → F)
: (∑ s, g s).eval inputs = ∑s, ((g s).eval inputs) := by
induction (Finset.univ : Finset (Index k)) using Finset.cons_induction with
| empty =>
  simp only [Finset.sum_empty, CPoly.eval_zero]
| cons a ta ha ih =>
  simp only [Finset.sum_cons, eval_add, ih]


lemma eval_prod_eq_prod_eval
{k : ℕ}
{F : Type}[Field F][BEq F][LawfulBEq F]
(g : Fin k → CMvPolynomial k F)
(inputs : Fin k → F)
: (∏ s, g s ).eval inputs = ∏ s , ((g s).eval inputs):= by
induction (Finset.univ : Finset (Fin k)) using Finset.cons_induction with
| empty =>
  simp only [Finset.prod_empty, eval_one]
| cons a ta ha ih =>
    rw [Finset.prod_cons, Finset.prod_cons, eval_mul]
    simp only [ih]


lemma eval_X
{k : ℕ}
{F : Type} [Field F] [BEq F] [LawfulBEq F]
(vals : Fin k → F) (i : Fin k) : eval vals (X i) = vals i := by
 simp only [eval_equiv, fromCMvPolynomial_X]
 apply MvPolynomial.eval_X

/--
TODO: rewrite this in a more simple manner
-/
lemma eval_chi
{k : ℕ}
(s : Fin k)
(m : Index k)
(x : Index k)
(F : Type)[Field F][BEq F][LawfulBEq F]
: eval (toPoint m) (chi s x F) = if x s = m s then 1 else 0 := by
unfold chi
cases hx : x s with
| true =>
  cases hs : m s with
  | true =>
    simp only [if_true]
    unfold toPoint
    simp only [eval_X, hs, if_true]
  | false =>
    simp only [if_true, Bool.true_eq_false, if_false, eval_X]
    unfold toPoint
    simp only [ hs, Bool.false_eq_true, if_false]
| false =>
  cases hs : m s with
  | true =>
    simp only [Bool.false_eq_true, if_false]
    unfold toPoint
    simp only [eval_sub, eval_one, eval_X, hs, if_true]
    field
  | false =>
    simp only [if_true, Bool.false_eq_true, if_false, eval_sub, eval_one, eval_X]
    unfold toPoint
    simp only [hs, Bool.false_eq_true, if_false]
    field


theorem function_linearization_agrees
{k : ℕ}
{F: Type}[Field F][BEq F] [LawfulBEq F]
(f : Index k → F) : ∀ m, f m = (linearizeFunction f).eval (toPoint m) := by
  intro m
  unfold linearizeFunction
  rw [eval_linearizeAll_boolean]
  . rw [ eval_sum_eq_sum_eval]
    simp only [eval_mul]
    simp only [eval_prod_eq_prod_eval]
    simp only [eval_chi]
    simp only [eval_C, Finset.prod_boole]
    simp only [Finset.mem_univ, forall_const , ← funext_iff]
    rw [Finset.sum_eq_single m]
    . simp only [if_true, mul_one]
    . intro _ _ bh
      simp only [bh, if_false, mul_zero]
    . intro h
      absurd h (Finset.mem_univ m)
      simp
  . intro i
    unfold toPoint
    cases m i with
    | true => simp
    | false => simp

/--
Our function is actually multilinear
We get this directly from Linearize.lean
-/
theorem degreeOf_linearizeFunction_le_one
    {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (f : Index k → F) (i : Fin k) :
    (linearizeFunction f).degreeOf i ≤ 1 := by
  unfold linearizeFunction
  exact degreeOf_linearizeAll_le_one _ i

end CPoly.CMvPolynomial
