/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Height.Box
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Projection.AffineLinearCountTransfer
import CCDN.Projection.AffineProjectionDegree
import CCDN.Projection.BoundedAffineBirationalProjection
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.ClosureProjectionBirational
import CCDN.Algebra.ProjectionScalarExtension
/-! The positive-dimensional affine projection in CCDN Proposition 4.3.1.
The image equation has the source degree and remains irreducible
after scalar extension. An integral normalization gives the exact factor d
in the point-count comparison. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def affineProjectionHeightConstant (n : ℕ) : ℕ :=
  (n + 1) * birationalProjectionHeightConstant n

lemma affineProjectionHeightConstant_pos (n : ℕ) : 0 < affineProjectionHeightConstant n := by
  exact Nat.mul_pos (Nat.succ_pos n) (birationalProjectionHeightConstant_pos n)

/-- A constructed bounded integer projection with exact degree, geometric
integrality, finite and birational coordinate map, and uniform count bound. -/
theorem exists_geometric_affine_projection_positive_dimension
    {L : Type*} [Field L] [Algebra ℚ L] (m n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (d : ℕ) (hd : 1 ≤ d)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin n → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight n d) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      Irreducible (map (algebraMap ℚ L) f) ∧ f.totalDegree = d ∧
      ∀ B : ℝ, 1 ≤ B → count (idealZeroLocus I) B ≤
        d * count (zeroLocus f)
          ((affineProjectionHeightConstant n : ℝ) * (d : ℝ) ^ (2 * n) * B) := by
  have hmn : m + 1 ≤ n := by
    obtain ⟨_, _, hdimle, _⟩ := filteredHilbertPolynomial_positive_multiplicity I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›)
    simpa only [hdimdeg.natDegree_eq, Fintype.card_fin] using hdimle
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  let n := m + 1 + k
  obtain ⟨b, f, hb, hN, hP, hcone, hfpos, _⟩ :=
    exists_bounded_affine_birational_projection m k I d hdimdeg
  have hfieldcone := closure_projection_generates_functionField I
    (fun i => integerLinearForm (b i)) (fun i => linearForm_isHomogeneous _) hP.birational
  have hfdeg := affine_projection_equation_degree_eq_of_closure I
    (fun i => integerLinearForm (b i)) (fun i => linearForm_isHomogeneous _)
    hcone hfieldcone d hdimdeg f hP.irreducible.ne_zero hfpos hP.ker_eq
  refine ⟨b, f, hb, hP,
    projection_equation_irreducible_map I _ f hP.irreducible.ne_zero hP.ker_eq, hfdeg, ?_⟩
  have hrel := hP.aeval_mem
  have hfiber (z : Fin (m + 2) → ℚ) (s : Finset (Fin n → ℚ))
      (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
      (hproj : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) :
      s.card ≤ d := by
    have hh := bounded_degree_normalization_fiber_card_le I 1 (by omega)
      (fun i : Fin (m + 1) => integerLinearForm (b i.succ))
      (fun i => linearForm_totalDegree_le _) hN.injective hN.integral d hdimdeg
      (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)
    simpa only [one_pow, Nat.mul_one] using hh
  let H : ℝ := birationalProjectionHeightConstant n * (d : ℝ) ^ (2 * n)
  have hH : 0 ≤ H := by positivity
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight n d := by
      exact_mod_cast hb i j
    apply hh.trans
    dsimp only [H]
    exact_mod_cast integerBirationalProjectionHeight_le n d hd
  intro B hB
  have hh := affine_integer_linear_count_transfer I b f hrel d hfiber H B hH hbH
  apply hh.trans
  apply Nat.mul_le_mul_left
  apply count_mono (Set.Subset.refl _)
  change (n : ℝ) * H * B ≤ (affineProjectionHeightConstant n : ℝ) *
    (d : ℝ) ^ (2 * n) * B
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * H * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ n) hH) (by linarith)
    _ = _ := by simp only [affineProjectionHeightConstant, Nat.cast_mul, H, mul_assoc]

end
end CCDN
