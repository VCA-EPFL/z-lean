import GKR.Src.Circuit
import CompPoly.Multivariate.FinSuccEquiv
import CompPoly.Multivariate.CMvPolynomialEvalLemmas
import CompPoly.Multivariate.Rename
import GKR.Src.Linearize
/-
Linearize.lean only linearizes a polynomial,
but GKR needs to linearize a function on boolean hypercube and this file provides a bridge for that
-/

namespace CPoly.CMvPolynomial

/--
xi (i) = x_i * w_i + (1 - x_i) * (1 - w_i)
-/
noncomputable def chi
{k : ℕ}
(i : Fin k)
(w : Index k)
(F : Type) [Field F]
[BEq F] [LawfulBEq F] -- needed for CMV polynomial
: CMvPolynomial k F :=
 if w i then  X i else 1 - X i

/--
Explicitly construct a multilinear polynomial agreeeing with a function over all hypercube points
Formula is the same as Lemma 3.6. from Thaler's book
noncomputable for compatibility with linearizeAll
-/
noncomputable def linearizeFunction
{F : Type} [Field F]
[BEq F] [LawfulBEq F] -- needed for CMV polynomial
{k : ℕ}
(f : Index k → F) : CMvPolynomial k F :=
linearizeAll (∑ w, C (f w)  * ∏ i, chi i w F)
-- something

end CPoly.CMvPolynomial
