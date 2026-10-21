/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfaceBadPrimeFactor
public import CCDN.Height.ProjectiveZeroLocus
import all ArithmeticHeights.BombieriVaaler
public import CCDN.Determinant.HypersurfaceDeterminantRank
import CCDN.Auxiliary.HypersurfaceBadPrimeCoordinates

/-! The corrected finite-family form of CCDN Proposition 3.2.6.
Each square evaluation matrix has a common homogeneous degree, but the
common degree may vary between matrices. The gcd is taken over the
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
that divides every determinant in the family. Individual matrices may have
any rank, and the family may be empty. -/
theorem projective_hypersurface_familyGcd_dvd
    {ι : Type*} [Fintype ι] {n s p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hf0 : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) f)))
    (hsize : stepanovThreshold (d : ℝ) < p)
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
  obtain ⟨e, he, hdiv⟩ := projective_hypersurface_minorGcd_dvd f hf hd hf0 hir hsize
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

/-- Corrected CCDN Proposition 3.2.6 for an arbitrary finite family.
Each matrix has one homogeneous degree, which may differ from every other
matrix's degree. The exact paper bad-prime factor and dimension-only error
are retained. Individual zero determinants, an empty row set and repeated
points are allowed; only the family gcd must be nonzero. -/
theorem hypersurface_determinant_family_log_lower
    {ι : Type*} [Fintype ι] {n s d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (M : ι → ℕ) (F : ι → Fin s → MvPolynomial (Fin (n + 3)) ℤ)
    (hF : ∀ l j, (F l j).IsHomogeneous (M l))
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) (hD : homogeneousDeterminantFamilyGcd F z ≠ 0) :
    hypersurfaceRankLowerBound n s d (Real.log (hypersurfaceBadPrimeFactor f)) ≤
      Real.log (|homogeneousDeterminantFamilyGcd F z| : ℝ) := by
  classical
  have hnonneg := homogeneousDeterminantFamilyGcd_nonneg F z
  rw [abs_of_nonneg (show (0 : ℝ) ≤ homogeneousDeterminantFamilyGcd F z by exact_mod_cast hnonneg)]
  by_cases hs : 0 < s
  · have hdeg : f.totalDegree = d := hf.totalDegree (ne_zero_of_irreducible_map hir)
    obtain ⟨bad, hmem⟩ := exists_hypersurface_bad_prime_finset f hf hd hir
    rw [hypersurfaceBadPrimeFactor_eq_exp f hir hdeg bad hmem, Real.log_exp]
    refine hypersurface_log_lower_at_rank_of_local_divisors hs hd bad
      (lt_of_le_of_ne hnonneg (Ne.symm hD)) fun p hp hcut => ?_
    have : Fact p.Prime := ⟨(mem_filter.mp (mem_sdiff.mp hp).1).2⟩
    obtain ⟨hf0, hir⟩ := hasGoodReduction_of_not_mem hmem p (mem_sdiff.mp hp).2 hcut
    exact projective_hypersurface_familyGcd_dvd f hf hd hf0 hir hcut M F hF z hprim hz
  · have hs0 : s = 0 := by omega
    have hone : (1 : ℝ) ≤ homogeneousDeterminantFamilyGcd F z := by
      exact_mod_cast (show (1 : ℤ) ≤ homogeneousDeterminantFamilyGcd F z by omega)
    simp only [hypersurfaceRankLowerBound, hs0, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0), mul_zero, zero_mul]
    exact Real.log_nonneg hone

/-- The logarithm of the gcd of a family of evaluation determinants at rational projective
points of an absolutely irreducible hypersurface (each matrix with a common column degree) is
at least `hypersurfaceRankLowerBound` in terms of the homogeneous bad-prime factor. The points
are evaluated at their primitive integral representatives. -/
theorem projective_hypersurface_determinant_family_log_lower
    {ι : Type*} [Fintype ι] {n s d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f.IsHomogeneous d) (hd : 0 < d)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (M : ι → ℕ) (F : ι → Fin s → MvPolynomial (Fin (n + 3)) ℤ)
    (hF : ∀ l j, (F l j).IsHomogeneous (M l))
    (x : Fin s → ProjectivePoint (n + 2))
    (hx : ∀ i, x i ∈ projectiveZeroLocus (map (Int.castRingHom ℚ) f))
    (hD : homogeneousDeterminantFamilyGcd F (fun i => primitiveProjectiveRep (x i)) ≠ 0) :
    hypersurfaceRankLowerBound n s d (Real.log (hypersurfaceBadPrimeFactor f)) ≤
      Real.log (|homogeneousDeterminantFamilyGcd F (fun i => primitiveProjectiveRep (x i))| : ℝ) := by
  apply hypersurface_determinant_family_log_lower f hf hd hir M F hF
    (fun i => primitiveProjectiveRep (x i)) (fun i => primitiveProjectiveRep_gcd (x i)) _ hD
  intro i
  exact (mem_integer_projectiveZeroLocus hf (x i)).mp (hx i)

end
end CCDN
