module

public import CCDN.HypersurfaceHeightDeterminant
public import CCDN.HypersurfaceBadPrimeFactor
public import CCDN.ProjectiveZeroLocus
import all ArithmeticHeights.BombieriVaaler

/-! The corrected finite-family form of CCDN Proposition 3.2.6.
Each square evaluation matrix has a common homogeneous degree, but the
common degree may vary between matrices. The gcd is taken over the actual
determinants, not over additional mixed minors. All local divisors and the
bad-prime set are constructed from the equation and its primitive zeros.
The unnormalized varying-degree-within-one-matrix statement is false. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- The normalized integer gcd of the square determinants in the source
orientation: forms index rows and points index columns. -/
def homogeneousDeterminantFamilyGcd {ι : Type*} [Fintype ι] {n s : ℕ}
    (F : ι → Fin s → MvPolynomial (Fin n) ℤ) (z : Fin s → IntPoint n) : ℤ :=
  univ.gcd fun l => (Matrix.of fun i j => eval (z j) (F l i)).det

lemma homogeneousDeterminantFamilyGcd_nonneg {ι : Type*} [Fintype ι] {n s : ℕ}
    (F : ι → Fin s → MvPolynomial (Fin n) ℤ) (z : Fin s → IntPoint n) :
    0 ≤ homogeneousDeterminantFamilyGcd F z :=
  Finset.Int.finsetGcd_nonneg

lemma square_minorGcd_dvd_det {s : ℕ} (A : Matrix (Fin s) (Fin s) ℤ) :
    Int.Matrix.minorGcd A ∣ A.det := by
  classical
  let S : Set.powersetCard (Fin s) s := ⟨univ, by simp⟩
  have h := Finset.gcd_dvd (s := univ) (f := exteriorPower.plucker s A.row) (mem_univ S)
  rw [exteriorPower.plucker_fin_eq_det] at h
  exact h

/-- The ceiling of the uniform real exponent is a single prime-power
that divides every determinant in the family. No rank assumption on any
individual matrix, or nonemptiness assumption on the family, is needed. -/
theorem projective_hypersurface_familyGcd_sharp
    {ι : Type*} [Fintype ι] {n s p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : 27 * (d : ℝ) ^ 4 < p)
    (M : ι → ℕ) (F : ι → Fin s → MvPolynomial (Fin (n + 3)) ℤ)
    (hF : ∀ l j, (F l j).IsHomogeneous (M l))
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    ∃ e : ℕ,
      hypersurfaceDeterminantMain n s /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) -
          (n + 2 : ℝ) * s ≤ e ∧
      (p : ℤ) ^ e ∣ homogeneousDeterminantFamilyGcd F z := by
  classical
  let a : ℝ := hypersurfaceDeterminantMain n s /
    (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) - (n + 2 : ℝ) * s
  refine ⟨⌈a⌉₊, Nat.le_ceil a, ?_⟩
  apply Finset.dvd_gcd
  intro l _
  obtain ⟨e, he, hdiv⟩ := projective_hypersurface_minorGcd_sharp f hf hd hf0 hir hsize
    (F l) (hF l) z hprim hz
  have ha : a ≤ e := by
    convert he using 1
    dsimp only [a, hypersurfaceDeterminantMain]
    ring
  have hpow := pow_dvd_pow (p : ℤ) (Nat.ceil_le.mpr ha)
  have hdet := hpow.trans (hdiv.trans (square_minorGcd_dvd_det
    (Matrix.of fun i j => eval (z i) (F l j))))
  rw [← Matrix.det_transpose] at hdet
  exact hdet

/-- Prime aggregation for the actual finite-family gcd. This intermediate
form only exposes the good-reduction predicate; the final theorem below
constructs and discharges it. -/
theorem hypersurface_familyGcd_log_lower_degree_four
    {ι : Type*} [Fintype ι] {n s d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (M : ι → ℕ) (F : ι → Fin s → MvPolynomial (Fin (n + 3)) ℤ)
    (hF : ∀ l j, (F l j).IsHomogeneous (M l))
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (hD : homogeneousDeterminantFamilyGcd F z ≠ 0)
    {x : ℝ} (hx : 1 ≤ x) (bad : Finset ℕ)
    (hred : ∀ (p : ℕ) [Fact p.Prime], p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad →
      27 * (d : ℝ) ^ 4 < p →
      map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) f))) :
    hypersurfaceDeterminantMain n s *
      (Real.log x - 4 * Real.log d - Real.log 27 - 2 * mertensError -
        (∑ p ∈ bad, Real.log p / p) - 2 * hypersurfaceCountConstant n * primeBlockMass) -
      ((n + 2 : ℝ) * s) * ((Real.log 4 + 4) * x) ≤
        Real.log (homogeneousDeterminantFamilyGcd F z) := by
  classical
  let L : ℝ := 27 * (d : ℝ) ^ 4
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad).filter (fun p : ℕ => L < p)
  let D := homogeneousDeterminantFamilyGcd F z
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
    exact projective_hypersurface_familyGcd_sharp f hf hd hf0 hir
      (mem_filter.mp h).2 M F hF z hprim hz
  let e : ℕ → ℕ := fun p => if h : p ∈ S then (hlocal p h).choose else 0
  have hDpos : 0 < D := lt_of_le_of_ne (homogeneousDeterminantFamilyGcd_nonneg F z) hD.symm
  have hh := general_determinant_log_lower_cutoff hx hL
    (mul_nonneg (hypersurfaceCountConstant_nonneg n) (sq_nonneg (d : ℝ)))
    (hypersurfaceDeterminantMain_nonneg n s) (by positivity : 0 ≤ (n + 2 : ℝ) * s)
    bad mass e (D := D) hDpos ?_ ?_ ?_ ?_
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

/-- Corrected CCDN Proposition 3.2.6 for an arbitrary finite family.
Each matrix has one homogeneous degree, which may differ from every other
matrix's degree. The exact paper bad-prime factor and dimension-only error
are retained. Individual zero determinants, an empty row set and repeated
points are allowed; only the actual family gcd must be nonzero. -/
theorem hypersurface_determinant_family_log_lower
    {ι : Type*} [Fintype ι] {n s d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (M : ι → ℕ) (F : ι → Fin s → MvPolynomial (Fin (n + 3)) ℤ)
    (hF : ∀ l j, (F l j).IsHomogeneous (M l))
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (hD : homogeneousDeterminantFamilyGcd F z ≠ 0) :
    ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - (n + 1 : ℝ) *
          (4 * Real.log d + Real.log (hypersurfaceBadPrimeFactor f)) - hypersurfaceDeterminantError n) ≤
      Real.log (|homogeneousDeterminantFamilyGcd F z| : ℝ) := by
  classical
  have hnonneg := homogeneousDeterminantFamilyGcd_nonneg F z
  rw [abs_of_nonneg (show (0 : ℝ) ≤ homogeneousDeterminantFamilyGcd F z by exact_mod_cast hnonneg)]
  by_cases hs : 0 < s
  · have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
    have hdeg : f.totalDegree = d := hf.totalDegree hf0
    let bad := (finite_fin_hypersurface_bad_primes f hir (hdeg ▸ hd)).toFinset
    have hmem (p : ℕ) : p ∈ bad ↔ 27 * d ^ 4 < p ∧ HypersurfaceBadReduction f p := by
      simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hdeg]
    have hred (p : ℕ) [Fact p.Prime]
        (hp : p ∈ ((Ioc 0 ⌊(s : ℝ) ^ (1 / (n + 1 : ℝ))⌋₊).filter Nat.Prime) \ bad)
        (hcut : 27 * (d : ℝ) ^ 4 < p) :
        map (Int.castRingHom (ZMod p)) f ≠ 0 ∧
        Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
          (map (Int.castRingHom (ZMod p)) f)) := by
      apply hypersurface_good_reduction f p
      intro hb
      exact (mem_sdiff.mp hp).2 ((hmem p).mpr ⟨by exact_mod_cast hcut, hb⟩)
    have h := hypersurface_familyGcd_log_lower_degree_four f hf hd M F hF z hprim hz hD
      (hypersurface_rank_prime_endpoint n s hs) bad hred
    rw [hypersurface_determinant_rank_identity n s d hs] at h
    rw [hypersurfaceBadPrimeFactor_eq_exp f hir hdeg bad hmem, Real.log_exp]
    exact h
  · have hs0 : s = 0 := by omega
    have hone : (1 : ℝ) ≤ homogeneousDeterminantFamilyGcd F z := by
      exact_mod_cast (show (1 : ℤ) ≤ homogeneousDeterminantFamilyGcd F z by omega)
    simp only [hs0, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0), mul_zero, zero_mul]
    exact Real.log_nonneg hone

/-- The same corrected family bound on actual rational projective points.
Primitive integral representatives, and their vanishing equations, are
constructed rather than supplied as additional data. -/
theorem projective_hypersurface_determinant_family_log_lower
    {ι : Type*} [Fintype ι] {n s d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (M : ι → ℕ) (F : ι → Fin s → MvPolynomial (Fin (n + 3)) ℤ)
    (hF : ∀ l j, (F l j).IsHomogeneous (M l))
    (x : Fin s → ProjectivePoint (n + 2))
    (hx : ∀ i, x i ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f))
    (hD : homogeneousDeterminantFamilyGcd F (fun i => primitiveProjectiveRep (x i)) ≠ 0) :
    ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) / (n + 2 : ℝ) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) *
        (Real.log s - (n + 1 : ℝ) *
          (4 * Real.log d + Real.log (hypersurfaceBadPrimeFactor f)) - hypersurfaceDeterminantError n) ≤
      Real.log (|homogeneousDeterminantFamilyGcd F (fun i => primitiveProjectiveRep (x i))| : ℝ) := by
  apply hypersurface_determinant_family_log_lower f hf hd hir M F hF
    (fun i => primitiveProjectiveRep (x i)) (fun i => primitiveProjectiveRep_gcd (x i)) _ hD
  intro i
  exact (mem_integer_projectiveZeroLocus hf (x i)).mp (hx i)

end
end CCDN
