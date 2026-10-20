module

public import AffineCurveCounting.CongruencePrimeSum
public import AffineCurveCounting.HypersurfaceDeterminantRank
public import AffineCurveCounting.SmoothHypersurfaceCongruence
import all ArithmeticHeights.BombieriVaaler

/-! Congruence-refined global hypersurface determinant bounds. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Finset

/-- The global hypersurface divisor and prescribed congruence divisors
contribute simultaneously, with their primes excluded from the global sum. -/
theorem hypersurface_determinant_log_lower_degree_four_congruence {n s N d M : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    {x : ℝ} (hx : 1 ≤ x) (bad : Finset ℕ)
    (P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℕ)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)))
    (hred : ∀ (p : ℕ) [Fact p.Prime], p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad →
      27 * (d : ℝ) ^ 4 < p →
      map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) f))) :
    hypersurfaceDeterminantMain n s *
      (Real.log x - 4 * Real.log d - Real.log 27 - 2 * mertensError -
        (∑ p ∈ bad, Real.log p / p) - 2 * hypersurfaceCountConstant n * primeBlockMass) -
      ((n + 2 : ℝ) * s) * ((Real.log 4 + 4) * x) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  classical
  let L : ℝ := 27 * (d : ℝ) ^ 4
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad).filter (fun p : ℕ => L < p)
  let D := Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))
  let mass : ℕ → ℝ := fun p => p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL : 1 ≤ L := by
    dsimp [L]
    nlinarith [one_le_pow₀ hd1 (n := 4)]
  have hp (p : ℕ) (h : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp h).1).1).2
  have hlocal (p : ℕ) (h : p ∈ S) :
      ∃ e : ℕ, hypersurfaceDeterminantMain n s / mass p - (n + 2 : ℝ) * s ≤ e ∧
        (p : ℤ) ^ e ∣ D := by
    let : Fact p.Prime := ⟨hp p h⟩
    obtain ⟨hf0, hir⟩ := hred p (mem_filter.mp h).1 (mem_filter.mp h).2
    obtain ⟨e, he, hdiv⟩ := projective_hypersurface_minorGcd_sharp f hf hd hf0 hir
      (mem_filter.mp h).2 F hF z hprim hz
    refine ⟨e, ?_, hdiv⟩
    convert he using 1
    unfold hypersurfaceDeterminantMain mass
    ring
  let e : ℕ → ℕ := fun p => if h : p ∈ S then (hlocal p h).choose else 0
  have hh := general_determinant_log_lower_cutoff_congruence hx hL
    (mul_nonneg (hypersurfaceCountConstant_nonneg n) (sq_nonneg (d : ℝ)))
    (hypersurfaceDeterminantMain_nonneg n s) (by positivity : 0 ≤ (n + 2 : ℝ) * s)
    bad P hPbad hP mass e v (D := D) (lt_of_lt_of_le (by norm_num) (Int.Matrix.one_le_minorGcd hrows))
    ?_ ?_ ?_ ?_ hcong
  · have hsqrt : (d : ℝ) ^ 2 ≤ Real.sqrt L := by
      apply Real.le_sqrt_of_sq_le
      dsimp [L]
      nlinarith [sq_nonneg ((d : ℝ) ^ 2)]
    have htail : hypersurfaceCountConstant n * (d : ℝ) ^ 2 *
        (2 * primeBlockMass / Real.sqrt L) ≤ 2 * hypersurfaceCountConstant n * primeBlockMass := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
      have h := mul_le_mul_of_nonneg_left hsqrt
        (show 0 ≤ 2 * hypersurfaceCountConstant n * primeBlockMass from
          mul_nonneg (mul_nonneg (by norm_num) (hypersurfaceCountConstant_nonneg n)) primeBlockMass_pos.le)
      nlinarith
    have hlog : Real.log L = Real.log 27 + 4 * Real.log d := by
      dsimp only [L]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    rw [hlog] at hh
    have hmul := mul_le_mul_of_nonneg_left htail (hypersurfaceDeterminantMain_nonneg n s)
    dsimp only [D] at hh
    nlinarith
  · intro p hp hcut
    have hprime := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hpos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    dsimp [mass]
    have := hypersurfaceCountConstant_nonneg n
    positivity
  · intro p _ _
    exact le_rfl
  · intro p hp hcut
    have hmem : p ∈ S := mem_filter.mpr ⟨hp, hcut⟩
    rw [show e p = (hlocal p hmem).choose from dite_eq_left hmem]
    exact (hlocal p hmem).choose_spec.1
  · intro p hp hcut
    have hmem : p ∈ S := mem_filter.mpr ⟨hp, hcut⟩
    rw [show e p = (hlocal p hmem).choose from dite_eq_left hmem]
    exact (hlocal p hmem).choose_spec.2


/-- The higher-dimensional rank-cutoff form of Proposition 3.2.6 for actual
maximal minors and common-degree homogeneous evaluation columns. -/
theorem hypersurface_determinant_log_lower_at_rank_congruence {n s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (P : Finset ℕ) (hPbad : P ⊆ bad) (hP : ∀ p ∈ P, p.Prime)
    (v : ℕ → ℕ)
    (hcong : ∀ p ∈ P, (p : ℤ) ^ v p ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)))
    (hred : ∀ (p : ℕ) [Fact p.Prime],
      p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad →
      27 * (d : ℝ) ^ 4 < p →
      map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) f))) :
    ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + (∑ p ∈ bad, Real.log p / p)) -
          hypersurfaceDeterminantError n) +
      (∑ p ∈ P, (v p : ℝ) * Real.log p) ≤
      Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := hypersurface_determinant_log_lower_degree_four_congruence f hf hd F hF z hprim hz hrows
    (hypersurface_rank_prime_endpoint n s hs) bad P hPbad hP v hcong hred
  rw [hypersurface_determinant_rank_identity n s d hs] at h
  exact h


end
end AffineCurveCounting
