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
  rw [eval_sum_eq_sum_eval]
  simp only [eval_mul]
  simp only [eval_prod_eq_prod_eval]
  simp only [eval_chi]
  simp only [eval_C, Finset.prod_boole]
  simp only [Finset.mem_univ, forall_const, ← funext_iff]
  rw [Finset.sum_eq_single m]
  · simp only [if_true, mul_one]
  · intro _ _ bh
    simp only [bh, if_false, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ m) h


/--
Just a bridge between CompPoly's polynomaial and mathlibs
-/
lemma degreeOf_C_eq {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (c : F) (i : Fin k) :
    degreeOf i (C c : CMvPolynomial k F) = 0 := by
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := (C c : CMvPolynomial k F))) i,
      CMvPolynomial.fromCMvPolynomial_C]
  exact MvPolynomial.degreeOf_C _ _

/--
Also a bridge between comppoly and mathlib
-/
lemma degreeOf_mul_le' {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (p q : CMvPolynomial k F) (i : Fin k) :
    degreeOf i (p * q) ≤ degreeOf i p + degreeOf i q := by
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := p * q)) i,
      congrFun (CPoly.degreeOf_equiv (S := F) (p := p)) i,
      congrFun (CPoly.degreeOf_equiv (S := F) (p := q)) i]
  rw [show fromCMvPolynomial (p * q)
        = fromCMvPolynomial p * fromCMvPolynomial q from map_mul _ _]
  exact MvPolynomial.degreeOf_mul_le _ _ _


/--
convert degree of product to sum of degrees, with bridges to mathlib
-/
lemma degreeOf_prod_le' {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {ι : Type} (s : Finset ι) (g : ι → CMvPolynomial k F) (i : Fin k) :
    degreeOf i (∏ j ∈ s, g j) ≤ ∑ j ∈ s, degreeOf i (g j) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    have h1 : degreeOf i (1 : CMvPolynomial k F) = 0 := by
      rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := (1 : CMvPolynomial k F))) i,
          CPoly.map_one]
      simp
    simp [h1]
  | cons a t ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact le_trans (degreeOf_mul_le' _ _ i) (Nat.add_le_add_left ih _)

/--
Degree over a sum is a maximum degree of individual terms
-/
lemma degreeOf_sum_le' {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {ι : Type} (s : Finset ι) (g : ι → CMvPolynomial k F) (i : Fin k) :
    degreeOf i (∑ j ∈ s, g j) ≤ s.sup (fun j => degreeOf i (g j)) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
    have h0 : degreeOf i (0 : CMvPolynomial k F) = 0 := by
      rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := (0 : CMvPolynomial k F))) i,
          CPoly.map_zero]
      simp
    simp [h0]
  | cons a t ha ih =>
    rw [Finset.sum_cons, Finset.sup_cons]
    refine le_trans ?_ (max_le_max (le_refl _) ih)
    rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := g a + ∑ j ∈ t, g j)) i,
        congrFun (CPoly.degreeOf_equiv (S := F) (p := g a)) i,
        congrFun (CPoly.degreeOf_equiv (S := F) (p := ∑ j ∈ t, g j)) i]
    rw [show fromCMvPolynomial (g a + ∑ j ∈ t, g j)
          = fromCMvPolynomial (g a) + fromCMvPolynomial (∑ j ∈ t, g j) from map_add _ _]
    exact MvPolynomial.degreeOf_add_le _ _ _

/--
Also a bridge
-/
lemma degreeOf_X_le {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (i j : Fin k) :
    degreeOf i (X j : CMvPolynomial k F) ≤ if j = i then 1 else 0 := by
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := (X j : CMvPolynomial k F))) i,
      CMvPolynomial.fromCMvPolynomial_X, MvPolynomial.degreeOf_X]
  by_cases h : j = i
  · simp [h]
  · simp [h, Ne.symm h]

/--
Degree of chi
-/
lemma degreeOf_chi_le {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (i j : Fin k) (w : Index k) :
    degreeOf i (chi j w F) ≤ if j = i then 1 else 0 := by
  unfold chi
  cases hw : w j
  · refine le_trans (degreeOf_sub_le_max 1 (X j) i) ?_
    have h1 : degreeOf i (1 : CMvPolynomial k F) = 0 := by
      rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := (1 : CMvPolynomial k F))) i,
          CPoly.map_one]
      simp
    simp only [h1]
    exact max_le (by positivity) (degreeOf_X_le i j)
  · simpa using degreeOf_X_le i j

/--
Degree of chi is a product of some stuff
-/
lemma degreeOf_chi_prod_le {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (i : Fin k) (w : Index k) :
    degreeOf i (∏ j, chi j w F) ≤ 1 := by
  refine le_trans (degreeOf_prod_le' _ _ i) ?_
  refine le_trans (Finset.sum_le_sum (fun j _ => degreeOf_chi_le i j w)) ?_
  simp


/--
One of the capstone lemmas in this file
Proves that our multilinear extension is actually multilinear
-/
theorem degreeOf_linearizeFunction_le_one {k : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
    (f : Index k → F) (i : Fin k) :
    (linearizeFunction f).degreeOf i ≤ 1 := by
  unfold linearizeFunction
  refine le_trans (degreeOf_sum_le' _ _ i) ?_
  refine Finset.sup_le (fun w _ => ?_)
  refine le_trans (degreeOf_mul_le' _ _ i) ?_
  rw [degreeOf_C_eq]
  simpa using degreeOf_chi_prod_le i w

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

theorem multilinear_extension_unique
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
