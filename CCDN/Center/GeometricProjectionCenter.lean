/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Center.HomogeneousProjectionNoBasePoint
import CCDN.Center.IndependentBirationalProjection
import CCDN.Center.IndependentProjectionRows
import CCDN.Algebra.ProjectionScalarExtension
/-! Rational projection centers of the required dimension, disjoint
from the variety over extension fields and inducing finite birational maps.
The integer map has the proved normalization height bound; the sharper
Section 5 bound on a basis of the center is treated separately. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix

private lemma integerLinearForm_aeval_extension {L : Type*} [Field L] [Algebra ℚ L]
    {n : ℕ} (b : Fin n → ℤ) (x : Fin n → L) :
    aeval x (integerLinearForm b) = ∑ j, (b j : L) * x j := by
  simp [integerLinearForm]

private theorem homogeneous_integer_projection_center_disjoint
    {L : Type*} [Field L] [Algebra ℚ L] [Infinite L] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (hI : IsHomogeneousIdeal I)
    (b : Fin m → Fin (n + 1) → ℤ)
    (hint : (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral)
    (x : Projectivization L (Fin (n + 1) → L))
    (hx : x ∈ projectiveIdealZeroLocus (I.map (map (algebraMap ℚ L)))) :
    (fun i j => (b i j : L)) *ᵥ x.rep ≠ 0 := by
  have hh := homogeneous_integral_projection_geometric_no_base_point I hI
    (fun i => integerLinearForm (b i))
    (fun i => linearForm_isHomogeneous _) hint x hx
  change (fun i => ∑ j, (b i j : L) * x.rep j) ≠ 0
  simpa only [integerLinearForm_aeval_extension] using hh

/-- A geometrically good center is constructed, including degree one. Its
vector dimension is n-m-1, and its projection has a geometrically
integral image of the same degree. -/
theorem exists_geometric_birational_projection_center
    {L : Type*} [Field L] [Algebra ℚ L] [Infinite L]
    (m n : ℕ) (hmn : m + 2 ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin (n + 1) → ℤ)
      (Λ : Submodule ℚ (Fin (n + 1) → ℚ)) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (n + 1) d) ∧
      Λ = (Matrix.mulVecLin (fun i j => (b i j : ℚ))).ker ∧
      Module.finrank ℚ Λ = n - m - 1 ∧
      Function.Surjective (Matrix.mulVec (fun i j => (b i j : ℚ))) ∧
      (∀ x : Projectivization L (Fin (n + 1) → L),
        x ∈ projectiveIdealZeroLocus (I.map (map (algebraMap ℚ L))) →
        (fun i j => (b i j : L)) *ᵥ x.rep ≠ 0) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      Irreducible (map (algebraMap ℚ L) f) ∧ f.IsHomogeneous d ∧ f.totalDegree = d := by
  obtain ⟨b, f, hb, hli, _, hP, hfhom, hfdeg⟩ :=
    exists_independent_bounded_birational_hypersurface_projection m (n + 1)
      (by omega) I hI d hdimdeg
  obtain ⟨hs, hdimker⟩ := independent_integer_rows_kernel_dimension b hli
  refine ⟨b, (Matrix.mulVecLin (fun i j => (b i j : ℚ))).ker, f,
    hb, rfl, ?_, hs, ?_, hP,
    projection_equation_irreducible_map I _ f hP.irreducible.ne_zero hP.ker_eq, hfhom, hfdeg⟩
  · omega
  · exact homogeneous_integer_projection_center_disjoint I hI b hP.integral

end
end CCDN
