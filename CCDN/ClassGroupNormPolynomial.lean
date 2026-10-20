module

public import CCDN.ClassGroupBoundedGenerators
public import CCDN.PlaneGridHeight
public import Mathlib.LinearAlgebra.Charpoly.Basic

/-! Integral norm polynomials and the two signed plane equations
needed to count square-norm generators. The norm polynomial retains the full
number-field degree even when its parameter lies in a proper subfield. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped NumberField
open NumberField Polynomial

variable (K : Type*) [Field K] [NumberField K]

def integerNormPolynomial (β : 𝓞 K) : ℤ[X] :=
  (Algebra.lmul ℤ (𝓞 K) β).charpoly

lemma integerNormPolynomial_monic (β : 𝓞 K) :
    (integerNormPolynomial K β).Monic :=
  LinearMap.charpoly_monic _

lemma integerNormPolynomial_natDegree (β : 𝓞 K) :
    (integerNormPolynomial K β).natDegree = Module.finrank ℚ K := by
  rw [integerNormPolynomial, LinearMap.charpoly_natDegree, RingOfIntegers.rank]

lemma integerNormPolynomial_eval (β : 𝓞 K) (x : ℤ) :
    (integerNormPolynomial K β).eval x =
      Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [integerNormPolynomial, LinearMap.eval_charpoly, Algebra.norm_apply,
    map_sub (Algebra.lmul ℤ (𝓞 K)), Algebra.lmul_algebraMap]
  rfl

/-- The outer coordinate is the square root of the norm; the inner
coordinate is the integral translation parameter. -/
def signedNormCurvePolynomial (β : 𝓞 K) (ε : ℤ) : MvPolynomial (Fin 2) ℤ :=
  (bivariatePolynomialEquiv ℤ).symm
    (X ^ 2 - C (C ε * integerNormPolynomial K β))

lemma signedNormCurvePolynomial_eval (β : 𝓞 K) (ε x y : ℤ) :
    MvPolynomial.eval ![y, x] (signedNormCurvePolynomial K β ε) =
      y ^ 2 - ε * Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β) := by
  rw [← bivariatePolynomialEquiv_eval _ y x]
  simp [signedNormCurvePolynomial, integerNormPolynomial_eval]

lemma square_norm_yields_signedNormCurve_point
    (β : 𝓞 K) (x : ℤ) (m : ℕ)
    (h : (Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β)).natAbs = m ^ 2) :
    MvPolynomial.eval ![(m : ℤ), x] (signedNormCurvePolynomial K β 1) = 0 ∨
      MvPolynomial.eval ![(m : ℤ), x] (signedNormCurvePolynomial K β (-1)) = 0 := by
  have ha : |Algebra.norm ℤ (algebraMap ℤ (𝓞 K) x - β)| = (m : ℤ) ^ 2 := by
    simpa only [Int.natCast_natAbs, Nat.cast_pow]
      using congrArg (Nat.cast : ℕ → ℤ) h
  rcases (abs_eq (by positivity)).mp ha with hp | hn
  · left
    rw [signedNormCurvePolynomial_eval, hp]
    ring
  · right
    rw [signedNormCurvePolynomial_eval, hn]
    ring

end
end CCDN
