import GKR.Src.Circuit
import GKR.Src.LinearizeFunction

open CPoly CPoly.CMvPolynomial


def gluePoint
{k : ℕ}
{F : Type}
(a b c : Fin k → F) : Fin (k + (k + k)) → F :=
Fin.append a (Fin.append b c)

def glueIndex
{k : ℕ}
(z x y : Index k) : Index (k + (k + k)) :=
  Fin.append z (Fin.append x y)

-- we need the functions below in order to "decompose" a 3k bit index into 3 k bit ones
-- and those 3 k bit ones can then be fed into addPred, which is what we want

/-- First k-length block of a 3k bit index -/
def part₀ {k : ℕ} (w : Index (k + (k + k))) : Index k :=
  fun i => w (Fin.castAdd (k + k) i)

/-- second k-length block of a 3k bit index -/
def part₁ {k : ℕ} (w : Index (k + (k + k))) : Index k :=
  fun i => w (Fin.natAdd k (Fin.castAdd k i))

/-- The last k bits -/
def part₂ {k : ℕ} (w : Index (k + (k + k))) : Index k :=
  fun i => w (Fin.natAdd k (Fin.natAdd k i))

-- these two depend on linearizeFunction, which is noncomputable, so they need to be noncomputable as well

noncomputable def addTilde
{k d : ℕ}
(F : Type) [Field F] [BEq F] [LawfulBEq F]
(c : Circuit k d) (l : Fin d) : CMvPolynomial (k + (k + k)) F :=
  linearizeFunction (fun w => addPred F c l (part₀ w) (part₁ w) (part₂ w))

noncomputable def mulTilde
{k d : ℕ}
(F : Type) [Field F] [BEq F] [LawfulBEq F]
(c : Circuit k d) (l : Fin d) : CMvPolynomial (k + (k + k)) F :=
  linearizeFunction (fun w => mulPred F c l (part₀ w) (part₁ w) (part₂ w))

-- these three lemmas are here to make our lives easier later when we are proving stuff about this
@[simp] lemma part₀_glueIndex
{k : ℕ}
(z x y : Index k) : part₀ (glueIndex z x y) = z := by
  funext i
  simp only [part₀, glueIndex, Fin.append_left]

@[simp] lemma part₁_glueIndex {k : ℕ} (z x y : Index k) : part₁ (glueIndex z x y) = x := by
  funext i
  simp only [part₁, glueIndex, Fin.append_right, Fin.append_left]

@[simp] lemma part₂_glueIndex {k : ℕ} (z x y : Index k) : part₂ (glueIndex z x y) = y := by
  funext i
  simp only [part₂, glueIndex, Fin.append_right]

/--
A helper for layer_sum_eq_multilinear_extension
-/
@[simp] lemma glueIndex_parts {k : ℕ} (w : Index (k + (k + k))) :
    glueIndex (part₀ w) (part₁ w) (part₂ w) = w := by
  funext i
  induction i using Fin.addCases with
  | left i => simp only [glueIndex, part₀, Fin.append_left]
  | right j =>
    induction j using Fin.addCases with
    | left i => simp only [glueIndex, part₁, Fin.append_right, Fin.append_left]
    | right i => simp only [glueIndex, part₂, Fin.append_right]

/-
Also a helper for layer_sum_eq_multilinear_extension
-/
def glueEquiv {k : ℕ} : (Index k × Index k × Index k) ≃ Index (k + (k + k)) where
  toFun p := glueIndex p.1 p.2.1 p.2.2
  invFun w := (part₀ w, part₁ w, part₂ w)
  left_inv p := by simp
  right_inv w := by simp
