/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.AffineCurveDegree
public import CCDN.Projection.BoundedBirationalHypersurfaceProjection
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Algebra.ProjectionScalarExtension
import CCDN.Hilbert.PrincipalHilbertPolynomial
import CCDN.Hilbert.ProjectiveClosureHilbertPolynomial
import CCDN.Projection.AffineLinearCountTransfer
import CCDN.Projection.BoundedDegreeNormalizationFiber
import CCDN.Projection.ClosureProjectionBirational
import CCDN.Projection.HomogeneousFiniteProjectionDegree
import CCDN.Projection.LeadingCoordinateExtension
import CCDN.Projection.LinearParameterPrimitive

/-!
The positive-dimensional affine projection in CCDN Proposition 4.3.1.
The image equation has the source degree and remains irreducible
after scalar extension. An integral normalization gives the exact factor d
in the point-count comparison.

Degree preservation for an affine linear projection whose
projective-closure map is finite and birational.

A bounded finite birational affine projection constructed from a
normalization that remains finite at infinity. The degree-preservation step
is supplied separately by comparison of the projective closures.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_bounded_affine_birational_projection
    (m k : ℕ) (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime]
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ (b : Fin (m + 2) → Fin (m + 1 + k) → ℤ) (f : MvPolynomial (Fin (m + 2)) ℚ),
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + 1 + k) d) ∧
      IsNoetherNormalization I (fun i : Fin (m + 1) => integerLinearForm (b i.succ)) ∧
      IsBirationalProjection I (fun i => integerLinearForm (b i)) f ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates (fun i => integerLinearForm (b i)))).IsIntegral ∧
      0 < f.totalDegree ∧ f.totalDegree ≤ d := by
  classical
  let n := m + 1 + k
  let F := FractionRing (MvPolynomial (Fin n) ℚ ⧸ I)
  obtain ⟨a, ha, hinta, hinja, hcone⟩ :=
    exists_bounded_integer_closure_normalization m k I d hdimdeg
  let l : Fin (m + 1) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (a i)
  obtain ⟨t, ht, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I l (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  let b : Fin (m + 2) → Fin n → ℤ := Fin.cases (fun j => (t : ℤ) ^ j.val) a
  let l' : Fin (m + 2) → MvPolynomial (Fin n) ℚ := fun i => integerLinearForm (b i)
  have hfield' : IntermediateField.adjoin ℚ (Set.range (fun i =>
      algebraMap _ F ((Ideal.Quotient.mk I) (l' i)))) = ⊤ := by
    have hl : l' = Fin.cases (momentCoordinate ℚ n t) (fun i => integerLinearForm (a i)) :=
      integerLinearForm_moment_cons t a
    rwa [hl]
  obtain ⟨f, hf, hfpos, hfd, hker⟩ := exists_extended_projection_equation_degree_le
    I l' (fun i => linearForm_totalDegree_le _) hinja d hdimdeg
  have hcone' : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates l')).IsIntegral := by
    let ι : Fin (m + 2) → Fin (m + 3) := Fin.cases 0 (fun i => i.succ.succ)
    let ψcone := projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates l')
    have heqcone : ψcone.comp (rename ι) =
        projectionCoordinateMap (projectiveClosureIdeal I) (closureProjectionCoordinates l) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [ψcone, projectionCoordinateMap, closureProjectionCoordinates, ι, l', b, l]
    apply RingHom.IsIntegral.tower_top (rename ι).toRingHom ψcone.toRingHom
    change (ψcone.comp (rename ι)).IsIntegral
    rwa [heqcone]
  exact ⟨b, f, moment_cons_abs_le_integerBirationalProjectionHeight ht a ha, ⟨hinta, hinja⟩,
    ⟨⟨hfield', hf, hker⟩, projectionCoordinateMap_isIntegral_of_tail I l' hinta⟩, hcone', hfpos,
    hfd⟩

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private theorem affine_projection_equation_degree_eq_of_closure
    {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℚ)) [I.IsPrime]
    (a : Fin (m + 2) → MvPolynomial (Fin n) ℚ)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap (projectiveClosureIdeal I)
      (closureProjectionCoordinates a)).IsIntegral)
    (hfield : IntermediateField.adjoin ℚ
      (Set.range (fun i => algebraMap
        (MvPolynomial (Fin (n + 1)) ℚ ⧸ projectiveClosureIdeal I)
        (FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ projectiveClosureIdeal I))
        ((Ideal.Quotient.mk (projectiveClosureIdeal I))
          (closureProjectionCoordinates a i)))) = ⊤)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (f : MvPolynomial (Fin (m + 2)) ℚ) (hf : f ≠ 0) (hfpos : 0 < f.totalDegree)
    (hker : RingHom.ker (projectionCoordinateMap I a) = Ideal.span {f}) :
    f.totalDegree = d := by
  let J := RingHom.ker (projectionCoordinateMap I a)
  have : J.IsPrime := RingHom.ker_isPrime _
  have hJ : HasProjectiveDimensionDegree J m f.totalDegree := by
    rw [show J = Ideal.span {f} from hker]
    exact principal_filteredHilbertPolynomial_degree_leadingCoeff f hf hfpos
  have hsource := (projectiveClosureIdeal_hilbertPolynomial_parameters
    I (m + 1) d hdimdeg).leadingCoeff_eq
  have htarget := (projectiveClosureIdeal_hilbertPolynomial_parameters
    J (m + 1) f.totalDegree hJ).leadingCoeff_eq
  have heq := homogeneous_finite_birational_projection_leadingCoeff_eq
    (F := FractionRing (MvPolynomial (Fin (n + 1)) ℚ ⧸ projectiveClosureIdeal I))
    (projectiveClosureIdeal I) (projectiveClosureIdeal_homogeneous I)
    (closureProjectionCoordinates a) (closureProjectionCoordinates_homogeneous a ha)
    hint hfield
  rw [← projectiveClosureIdeal_projection_kernel I a ha, hsource, htarget] at heq
  exact_mod_cast (div_left_inj' (by positivity : ((m + 1 + 1).factorial : ℚ) ≠ 0)).mp heq

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

/-- The constant `(n + 1) * birationalProjectionHeightConstant n` scaling the height in the
point-count comparison for the affine projection in `n` variables. -/
def affineProjectionHeightConstant (n : ℕ) : ℕ :=
  (n + 1) * birationalProjectionHeightConstant n

/-- The affine projection height constant is positive. -/
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
