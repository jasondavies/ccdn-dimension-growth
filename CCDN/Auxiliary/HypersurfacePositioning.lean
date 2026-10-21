/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.HypersurfaceFullOuterDegree
public import CCDN.Determinant.GenericPlaneMinor
/-! Full-degree monic positioning of an irreducible hypersurface at a
smooth point, using an invertible affine change and a nonzero scalar. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Normalize the leading scalar of the explicit affine coordinate change. -/
def normalizedHypersurfaceCoordinates {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    MvPolynomial (Option σ) K :=
  C (eval b (homogeneousComponent f.totalDegree f))⁻¹ * hypersurfaceAffineCoordinates a b hb f

lemma normalizedHypersurfaceCoordinates_monic {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C]
  apply Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [Polynomial.leadingCoeff, hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir,
    hypersurfaceAffineCoordinates_top_coefficient, ← map_mul, inv_mul_cancel₀ hdir, map_one]

lemma normalizedHypersurfaceCoordinates_natDegree {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).natDegree = f.totalDegree := by
  unfold normalizedHypersurfaceCoordinates
  rw [map_mul, optionEquivLeft_C,
    Polynomial.natDegree_C_mul_of_isUnit ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)]
  exact hypersurfaceAffineCoordinates_full_outer_degree a b hb f hdir

lemma normalizedHypersurfaceCoordinates_totalDegree_le {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K) :
    (normalizedHypersurfaceCoordinates a b hb f).totalDegree ≤ f.totalDegree := by
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_C, zero_add]
    exact hypersurfaceAffineCoordinates_totalDegree_le a b hb f)

lemma normalizedHypersurfaceCoordinates_irreducible {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hf : Irreducible f) (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0) :
    Irreducible (normalizedHypersurfaceCoordinates a b hb f) := by
  apply (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (inv_ne_zero hdir)).map C)).mpr
  exact (MulEquiv.irreducible_iff (f := hypersurfaceAffineCoordinates a b hb)).mpr hf

lemma normalizedHypersurfaceCoordinates_eval_zero {K σ : Type*} [Field K]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hz : eval a f = 0) :
    eval (0 : Option σ → K) (normalizedHypersurfaceCoordinates a b hb f) = 0 := by
  rw [normalizedHypersurfaceCoordinates, map_mul, hypersurfaceAffineCoordinates_eval_zero, hz, mul_zero]

lemma normalizedHypersurfaceCoordinates_partial_ne_zero {K σ : Type*} [Field K] [Fintype σ]
    (a b : Option σ → K) (hb : b none ≠ 0) (f : MvPolynomial (Option σ) K)
    (hdir : eval b (homogeneousComponent f.totalDegree f) ≠ 0)
    (ht : (∑ i, eval a (pderiv i f) * b i) ≠ 0) :
    eval (0 : Option σ → K) (pderiv none (normalizedHypersurfaceCoordinates a b hb f)) ≠ 0 := by
  rw [normalizedHypersurfaceCoordinates, pderiv_C_mul, map_mul, eval_C,
    hypersurfaceAffineCoordinates_partial_zero]
  exact mul_ne_zero (inv_ne_zero hdir) ht

/-- Smooth-point existence and direction avoidance discharge all positioning
hypotheses: the coordinates and the nonzero scalar are actually constructed. -/
theorem exists_monic_smooth_hypersurface_coordinates
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    {p : ℕ} [CharP K p] (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      Irreducible (normalizedHypersurfaceCoordinates a b hb f) ∧
      (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).Monic ∧
      (optionEquivLeft K σ (normalizedHypersurfaceCoordinates a b hb f)).natDegree = f.totalDegree ∧
      (normalizedHypersurfaceCoordinates a b hb f).totalDegree ≤ f.totalDegree ∧
      eval (0 : Option σ → K) (normalizedHypersurfaceCoordinates a b hb f) = 0 ∧
      eval (0 : Option σ → K) (pderiv none (normalizedHypersurfaceCoordinates a b hb f)) ≠ 0 := by
  obtain ⟨a, j, ha, hj⟩ := exists_smooth_hypersurface_point_of_degree_lt_char (p := p) f hf hpos hchar
  obtain ⟨b, hb, hdir, ht⟩ := exists_good_hypersurface_direction_with_coordinate f hf.ne_zero a j hj none
  exact ⟨a, b, hb, hdir, normalizedHypersurfaceCoordinates_irreducible a b hb f hf hdir,
    normalizedHypersurfaceCoordinates_monic a b hb f hdir,
    normalizedHypersurfaceCoordinates_natDegree a b hb f hdir,
    normalizedHypersurfaceCoordinates_totalDegree_le a b hb f,
    normalizedHypersurfaceCoordinates_eval_zero a b hb f ha,
    normalizedHypersurfaceCoordinates_partial_ne_zero a b hb f hdir ht⟩

/-- Every irreducible positive-degree hypersurface in large characteristic has
an explicitly positioned generic-plane family with a nonzero slope minor. -/
theorem exists_positioned_genericPlane_minor
    {K σ : Type*} [Field K] [IsAlgClosed K] [Fintype σ]
    {p : ℕ} [CharP K p] (f : MvPolynomial (Option σ) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : 2 * f.totalDegree ^ 2 < p) :
    ∃ (a b : Option σ → K) (hb : b none ≠ 0),
      eval b (homogeneousComponent f.totalDegree f) ≠ 0 ∧
      ∃ (rows : Fin (2 * f.totalDegree ^ 2 - 1) → ℕ × ℕ)
        (cols : Fin (2 * f.totalDegree ^ 2 - 1) → ClosedFormColumns f.totalDegree),
        Function.Injective rows ∧ Function.Injective cols ∧
        ((closedFormCoefficientMatrix f.totalDegree
          (genericPlanePolynomial (normalizedHypersurfaceCoordinates a b hb f))).submatrix rows cols).det ≠ 0 := by
  have hp : f.totalDegree < p := by nlinarith [Nat.le_mul_self f.totalDegree]
  obtain ⟨a, b, hb, hdir, hg, hm, hdeg, ht, hz, hs⟩ :=
    exists_monic_smooth_hypersurface_coordinates (p := p) f hf hpos hp
  exact ⟨a, b, hb, hdir, exists_genericPlane_minor (p := p) f.totalDegree hpos
    (normalizedHypersurfaceCoordinates a b hb f) hg hm hdeg ht hchar hz hs⟩

end
end CCDN
