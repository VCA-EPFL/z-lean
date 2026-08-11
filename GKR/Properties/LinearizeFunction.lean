import GKR.Src.Circuit
import GKR.Src.LinearizeFunction
import GKR.Src.Linearize

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

/--
A helper lemma used for the proof of the below thing
-/
lemma toPoint_cons {n : ℕ} {F : Type} [Field F] (b : Bool) (x : Index n) :
    toPoint (F := F) (Fin.cons b x) = Fin.cons (if b then 1 else 0) (toPoint x) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [toPoint]
  | succ j => simp [toPoint]

/--
We need this for proving that our multilinear extension is unique
-/
theorem multilinear_eq_zero_on_hypercube_is_zero_polynomial
{k : ℕ}
{F : Type} [Field F] [BEq F] [LawfulBEq F]
(p : CMvPolynomial k F)
(hdeg : ∀ i, p.degreeOf i ≤ 1)
(h : ∀ x : Index k, eval (toPoint x ) p = 0)
: p = 0 := by
induction k with
| zero =>
  have h0 := h (fun i => i.elim0)
  -- bridge between CompPoly's polynomial and mathlibs polynomial
  rw [CPoly.eval_equiv] at h0
  apply CPoly.fromCMvPolynomial_injective
  rw [map_zero]
  obtain ⟨c, hc⟩ :=
  (MvPolynomial.isEmptyRingEquiv F (Fin 0)).symm.surjective (fromCMvPolynomial p)
  rw [← hc] at h0 ⊢
  rw [MvPolynomial.isEmptyRingEquiv_symm_apply] at h0 ⊢
  rw [MvPolynomial.eval_C] at h0
  rw [h0]
  simp
-- TODO: get rid of the code duplication here
| succ n ih =>
  have slice0 : specialize0 p 0 = 0 := by
    apply ih
    . intro i
      apply le_trans  (degreeOf_specialize0_succ_le p 0 i)
      exact hdeg i.succ
    . intro x
      rw [eval_specialize0]
      have hx := h (Fin.cons false x)
      rw [toPoint_cons] at hx
      simpa using hx
  have slice1  : specialize0 p 1 = 0 := by
    apply ih
    . intro i
      apply le_trans  (degreeOf_specialize0_succ_le p 1 i)
      exact hdeg i.succ
    . intro x
      rw [eval_specialize0]
      have hx := h (Fin.cons true x)
      rw [toPoint_cons] at hx
      simpa using hx
  have hrec : linearize0 p = p := linearize0_eq_self_of_degreeOf_le_one p (hdeg 0)
  rw [← hrec]
  unfold linearize0
  rw [slice0, slice1]
  simp

/--
Bridge from CMv's polynomial to the mathlibs one
-/
lemma degreeOf_sub_le_max
{k : ℕ}
{F : Type} [Field F] [BEq F] [LawfulBEq F]
(p q : CMvPolynomial k F) (i : Fin k) :
degreeOf i (p - q) ≤ max (degreeOf i p) (degreeOf i q) := by
rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := p - q)) i,
congrFun (CPoly.degreeOf_equiv (S := F) (p := p)) i,
congrFun (CPoly.degreeOf_equiv (S := F) (p := q)) i]
rw [show fromCMvPolynomial (p - q)
      = fromCMvPolynomial p - fromCMvPolynomial q from map_sub _ _]
exact MvPolynomial.degreeOf_sub_le _ _ _

/--
Subtraction of two multilinear polynomials yields a multilinear polynomial
-/
theorem sub_multilinear_eq_multilinear
{k : ℕ}
{F : Type} [Field F] [BEq F] [LawfulBEq F]
(p : CMvPolynomial k F)
(q : CMvPolynomial k F)
(pdeg : ∀ i, p.degreeOf i ≤ 1)
(qdeg : ∀ i, q.degreeOf i ≤ 1)
: (∀ i, (p - q).degreeOf i ≤ 1) := by
intro i
have step1 : (p - q).degreeOf i ≤ max (p.degreeOf i) (q.degreeOf i) :=
  degreeOf_sub_le_max p q i
have step2 : max (p.degreeOf i) (q.degreeOf i) ≤ 1 :=
  max_le (pdeg i) (qdeg i)
exact le_trans step1 step2

theorem multilienear_extension_unique
{k : ℕ}
{F : Type} [Field F] [BEq F] [LawfulBEq F]
(p : CMvPolynomial k F)
(f : Index k → F)
(hdeg : ∀ i, p.degreeOf i ≤ 1)
(h : ∀ x : Index k, eval (toPoint x ) p = eval (toPoint x) (linearizeFunction f))
: (p = linearizeFunction f) := by
  rw [← sub_eq_zero]
  apply multilinear_eq_zero_on_hypercube_is_zero_polynomial
  . apply sub_multilinear_eq_multilinear
    intro i
    . apply hdeg
    . exact degreeOf_linearizeFunction_le_one f
  . simp only [eval_sub]
    simp only [h]
    intro X
    field


end CPoly.CMvPolynomial
