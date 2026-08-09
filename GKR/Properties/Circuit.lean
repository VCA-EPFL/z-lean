import GKR.Src.Circuit
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi


/--
TODO: get rid of code duplication here (how?)
-/
theorem eval_layer_eq_sum
  {k d : ℕ}
  (F : Type)[Field F]
  (c : Circuit k d)
  (l : Fin (d))
  (W : Index k → F)
  : ∀ z : Index k , evalLayer (c.gate l) W z =
   ∑ x, ∑ y ,( (addPred F c l z x y) * (W x + W y) + (mulPred F c l z x y) * (W x * W y)) := by
  intro z
  cases h: c.gate l z with
  | add a b =>
    simp only [evalLayer, addPred, mulPred ,h, zero_mul, add_zero]
    rw [Finset.sum_eq_single a]
    . rw [Finset.sum_eq_single b]
      . simp only [and_self, if_true, one_mul]
      . intro _ _ hx
        simp only [true_and , Ne.symm hx, if_false, zero_mul]
      . intro hb
        exact absurd (Finset.mem_univ b) hb
    . intro bb _ hx
      simp only [Ne.symm hx, false_and, if_false, zero_mul, Finset.sum_const_zero]
    . intro ha
      exact absurd (Finset.mem_univ a) ha
  | mul a b =>
    simp only [evalLayer, addPred, mulPred, h, zero_mul, zero_add]
    rw [Finset.sum_eq_single a]
    . rw [Finset.sum_eq_single b]
      . simp only [true_and, if_true, one_mul]
      . intro _ _ hx
        simp only [true_and, Ne.symm hx, if_false, zero_mul]
      . intro hb
        exact absurd (Finset.mem_univ b) hb
    . intro bb _ hx
      simp only [Ne.symm hx, false_and, if_false, zero_mul, Finset.sum_const_zero]
    . intro ha
      exact absurd (Finset.mem_univ a) ha

/-
Helper for layer_values_eq_sum
-/
theorem layer_values_eq_eval_layer
  {k d : ℕ}
  (F: Type)[Field F]
  (c : Circuit k d)
  (l : Fin d)
  (input : Index k → F)
  : ∀ z : Index k, layerValues c input l.castSucc z
    = evalLayer (c.gate l) (layerValues c input l.succ) z := by
  intro z
  induction d  with
  | zero =>
    apply Fin.elim0 l
  | succ n ih =>
    simp only [layerValues]
    cases l using Fin.cases with
    | zero =>
      rw [Fin.castSucc_zero]
      rw [Fin.cons_zero]
      rw [Fin.cons_succ]
    | succ x =>
      rw [← Fin.succ_castSucc , Fin.cons_succ]
      rw [Fin.cons_succ] -- we can go on without this
      apply ih c.tail x




theorem layer_values_eq_sum
  {k d : ℕ}
  (F : Type)[Field F]
  (c : Circuit k d)
  (l : Fin d)
  (input : Index k → F)
  : ∀ z : Index k, layerValues c input l.castSucc z =
  ∑ x, ∑ y, (addPred F c l z x y * (layerValues c input l.succ x
  + layerValues c input l.succ y) + mulPred F c l z x y * ((layerValues c input l.succ x) *layerValues c input l.succ y))
  := by
  intro z
  rw [← eval_layer_eq_sum F c l  (layerValues c input l.succ)]
  apply layer_values_eq_eval_layer
