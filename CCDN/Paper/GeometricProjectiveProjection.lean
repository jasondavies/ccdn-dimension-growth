/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveZeroLocus
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
import CCDN.Algebra.ProjectionScalarExtension
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.ProjectiveLinearCountTransfer

/-!
Geometric integrality in the finite birational projective
projection. This supplies the general-dimensional geometric interface of
Proposition 4.3.2, with a dimension-only polynomial height cost.

The exact degree factor in the projective projection count.
A finite birational integer projection preserves the Hilbert degree,
and every fiber is bounded by d through its integral linear normalization.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A constructed finite birational hypersurface projection has exactly the
degree factor d in its point-count comparison, with a polynomial height cost
depending only on ambient dimension. -/
theorem exists_projective_variety_projection
    (m n : ℕ) (hmn : m ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hd : 1 ≤ d)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin (n + 1) → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      f.IsHomogeneous d ∧ f.totalDegree = d ∧
      ∀ B : ℝ, projectiveCount (projectiveIdealZeroLocus I) B ≤
        d * projectiveCount (projectiveZeroLocus f)
          (((n + 1 : ℕ) * birationalProjectionHeightConstant (n + 1) : ℕ) *
            (d : ℝ) ^ (2 * (n + 1)) * B) := by
  obtain ⟨b, f, hb, hN, hP, hfhom, hfdeg⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le m (n + 1)
      (by omega) I hI d hdimdeg
  refine ⟨b, f, hP, hfhom, hfdeg, ?_⟩
  have hrel := hP.aeval_mem
  have hfiber (z : Fin (m + 2) → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
      (hproj : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) :
      s.card ≤ d := by
    have hh := bounded_degree_normalization_fiber_card_le I 1 (by omega)
      (fun i : Fin (m + 1) => integerLinearForm (b i.succ))
      (fun i => linearForm_totalDegree_le _) hN.injective hN.integral d hdimdeg
      (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)
    simpa only [one_pow, Nat.mul_one] using hh
  let H : ℝ := birationalProjectionHeightConstant (n + 1) * (d : ℝ) ^ (2 * (n + 1))
  have hH : 0 ≤ H := by positivity
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight (n + 1) d := by
      exact_mod_cast hb i j
    apply hh.trans
    dsimp only [H]
    exact_mod_cast integerBirationalProjectionHeight_le (n + 1) d hd
  intro B
  have hh := projective_integer_linear_count_transfer
    I b f (by rwa [hfdeg]) hrel d hfiber H B hH hbH
  convert hh using 1
  simp only [H, Nat.cast_mul, mul_assoc]

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The constructed finite birational integer projection preserves degree
and geometric integrality, and its point-count comparison has factor
exactly `d`. Scalar extension may be to any field where the source stays
prime, in particular to an algebraic closure. -/
theorem exists_geometrically_integral_projective_projection
    {L : Type*} [Field L] [Algebra ℚ L]
    (m n : ℕ) (hmn : m ≤ n)
    (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    [(I.map (map (algebraMap ℚ L))).IsPrime]
    (hI : IsHomogeneousIdeal I)
    (d : ℕ) (hd : 1 ≤ d)
    (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ b : Fin (m + 2) → Fin (n + 1) → ℤ,
      (projectionCoordinateMap I (fun i => integerLinearForm (b i))).IsIntegral ∧
      IntermediateField.adjoin ℚ
        (Set.range (fun i => algebraMap (MvPolynomial (Fin (n + 1)) ℚ ⧸ I)
          (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ I))
          ((Ideal.Quotient.mk I) (integerLinearForm (b i))))) = ⊤ ∧
      ∃ f : MvPolynomial (Fin (m + 2)) ℚ,
        Irreducible f ∧ Irreducible (map (algebraMap ℚ L) f) ∧
        f.IsHomogeneous d ∧ f.totalDegree = d ∧
        RingHom.ker (projectionCoordinateMap I (fun i => integerLinearForm (b i))) =
          Ideal.span {f} ∧
        ∀ B : ℝ, projectiveCount (projectiveIdealZeroLocus I) B ≤
          d * projectiveCount (projectiveZeroLocus f)
            (((n + 1 : ℕ) * birationalProjectionHeightConstant (n + 1) : ℕ) *
              (d : ℝ) ^ (2 * (n + 1)) * B) := by
  obtain ⟨b, f, hP, hfhom, hfdeg, hcount⟩ :=
    exists_projective_variety_projection m n hmn I hI d hd hdimdeg
  exact ⟨b, hP.integral, hP.birational, f, hP.irreducible,
    projection_equation_irreducible_map I _ f hP.irreducible.ne_zero hP.ker_eq,
    hfhom, hfdeg, hP.ker_eq, hcount⟩

end
end CCDN
