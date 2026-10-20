module

public import AffineCurveCounting.HypersurfacePrimeDeterminant

/-! Choosing the prime endpoint at the dimension root of the row count
produces the exact rank power and leading constant in CCDN Proposition 3.2.6. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Finset

/-- An explicit error depending only on hypersurface dimension. -/
def hypersurfaceDeterminantError (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * (Real.log 27 + 2 * mertensError + 2 * hypersurfaceCountConstant n * primeBlockMass) +
    (n + 2 : ℝ) ^ 2 / ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (Real.log 4 + 4)

lemma hypersurface_rank_prime_endpoint (n s : ℕ) (hs : 0 < s) :
    1 ≤ (s : ℝ) ^ (1 / (n + 1 : ℝ)) := by
  apply Real.one_le_rpow
  · exact_mod_cast hs
  · positivity

lemma hypersurface_determinant_rank_identity (n s d : ℕ) (hs : 0 < s) (charge : ℝ) :
    hypersurfaceDeterminantMain n s *
        (Real.log ((s : ℝ) ^ (1 / (n + 1 : ℝ))) - 4 * Real.log d - Real.log 27 -
          2 * mertensError - charge - 2 * hypersurfaceCountConstant n * primeBlockMass) -
        ((n + 2 : ℝ) * s) * ((Real.log 4 + 4) * (s : ℝ) ^ (1 / (n + 1 : ℝ))) =
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
        (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
          (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + charge) - hypersurfaceDeterminantError n) := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have hfac : ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) ≠ 0 := by positivity
  have hp : (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) =
      (s : ℝ) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) := by
    rw [Real.rpow_add hs0, Real.rpow_one]
  rw [Real.log_rpow hs0]
  unfold hypersurfaceDeterminantMain hypersurfaceDeterminantError
  rw [hp]
  field_simp
  ring

/-- The higher-dimensional rank-cutoff form of Proposition 3.2.6 for actual
maximal minors and common-degree homogeneous evaluation columns. -/
theorem hypersurface_determinant_log_lower_at_rank {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      27 * (d : ℝ) ^ 4 < p →
      map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) f))) :
    ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + (∑ p ∈ bad, Real.log p / p)) -
          hypersurfaceDeterminantError n) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := hypersurface_determinant_log_lower_degree_four f hf hd F hF z hprim hz hrows
    (hypersurface_rank_prime_endpoint n s hs) bad hred
  rw [hypersurface_determinant_rank_identity n s d hs] at h
  exact h

end
end AffineCurveCounting
