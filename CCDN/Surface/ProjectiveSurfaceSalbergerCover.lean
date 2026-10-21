/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveClosureIdeal
public import CCDN.Projection.ProjectivePlaneProjection
public import CCDN.Surface.GeometricCurveCover
import CCDN.Algebra.HomogeneousChartIrreducible
import CCDN.Algebra.IdealScalarDescent
import CCDN.Algebra.PrimitiveNormalization
import CCDN.Algebra.ProjectiveClosureDegree
import CCDN.Surface.SalbergerCover

/-!
Salberger's surface cover on the standard projective affine chart.
Every returned curve is a homogeneous geometrically prime ideal;
its degree is the projective Hilbert degree, proved by closure.

Clearing rational coefficients preserves the exact geometric Salberger
cover and all of its uniform constants.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem rational_surface_salberger_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : CoordinatePolynomial 3),
      AbsolutelyIrreducibleRat f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
        (∀ I ∈ S, IsGeometricSurfaceCurve f I (δ I) ∧ δ I ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus f \ (⋃ I ∈ S, idealZeroLocus I)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  obtain ⟨C,c,hC,hc,hcover⟩ := surface_salberger_cover d hd
  refine ⟨C,c,hC,hc,?_⟩
  intro f habs hfd B hB
  have hf0 : f ≠ 0 := by intro hz; exact habs.ne_zero (by rw [hz,map_zero])
  obtain ⟨g,a,_,ha,he⟩ := exists_primitive_integer_model f hf0
  have hgdeg : g.totalDegree = d := (rational_scalar_model_degree ha hf0 he).trans hfd
  have haK : algebraMap ℚ (AlgebraicClosure ℚ) a ≠ 0 :=
    by simpa only [map_zero] using (algebraMap ℚ (AlgebraicClosure ℚ)).injective.ne ha
  have heK : map (Int.castRingHom (AlgebraicClosure ℚ)) g =
      MvPolynomial.C (algebraMap ℚ (AlgebraicClosure ℚ) a) *
        map (algebraMap ℚ (AlgebraicClosure ℚ)) f := by
    have hh := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ))) he
    have hφ : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AlgebraicClosure ℚ) := by ext; simp
    simpa only [map_map,map_mul,map_C,hφ] using hh
  have hgabs : AbsolutelyIrreducible g := by
    rw [AbsolutelyIrreducible, heK]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr haK).map MvPolynomial.C)).mpr habs
  obtain ⟨S,δ,hS,hcard,hcount⟩ := hcover g hgabs hgdeg B hB
  refine ⟨S,δ,?_,hcard,?_⟩
  · intro I hI
    obtain ⟨hp,hh,hg,hgeo,hpos,hdeg,hδ⟩ := hS I hI
    refine ⟨⟨⟨hp,hh,?_,hdeg⟩,hgeo,hpos⟩,hδ⟩
    rw [he] at hg
    have hh' := I.mul_mem_left (MvPolynomial.C a⁻¹) hg
    simpa only [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, map_one, one_mul] using hh'
  · rw [he,smoothSurfaceLocus_C_mul a ha] at hcount
    exact hcount

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private lemma projectiveClosure_union_chart {n : ℕ}
    (S : Finset (Ideal (CoordinatePolynomial n))) :
    affineProjectivePoint ⁻¹' (⋃ J ∈ S.image projectiveClosureIdeal,
      projectiveIdealZeroLocus J) = ⋃ I ∈ S, idealZeroLocus I := by
  classical
  ext a
  constructor
  · intro ha
    obtain ⟨J,hJ,haJ⟩ := Set.mem_iUnion₂.mp ha
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact Set.mem_iUnion₂.mpr ⟨I,hI,(projectiveClosureIdeal_chart_point I a).mp haJ⟩
  · intro ha
    obtain ⟨I,hI,haI⟩ := Set.mem_iUnion₂.mp ha
    exact Set.mem_iUnion₂.mpr ⟨projectiveClosureIdeal I,Finset.mem_image.mpr ⟨I,hI,rfl⟩,
      (projectiveClosureIdeal_chart_point I a).mpr haI⟩

/-- The paper's projective surface and projective curves, with the
integer-point count taken in x₀=1. Constants are chosen before the equation
and the box, and the hyperplane x₀=0 is required to intersect properly. -/
theorem projective_surface_salberger_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (F : CoordinatePolynomial 4), F.IsHomogeneous d →
      AbsolutelyIrreducibleRat F →
      (¬ X 0 ∣ F) → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 4)))
        (δ : Ideal (CoordinatePolynomial 4) → ℕ),
        (∀ J ∈ S, J.IsPrime ∧
          IsHomogeneousIdeal J ∧
          (J.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime ∧
          F ∈ J ∧ X 0 ∉ J ∧ 0 < δ J ∧ HasProjectiveCurveDegree J (δ J) ∧ δ J ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus (affineChart 3 F) \
          affineProjectivePoint ⁻¹' (⋃ J ∈ S, projectiveIdealZeroLocus J)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  classical
  obtain ⟨C,c,hC,hc,hcover⟩ := rational_surface_salberger_cover d hd
  refine ⟨C,c,hC,hc,?_⟩
  intro F hhom habs hX B hB
  have hXK : ¬ X 0 ∣ map (algebraMap ℚ (AlgebraicClosure ℚ)) F := by
    intro hh
    apply hX
    have hmem : map (algebraMap ℚ (AlgebraicClosure ℚ)) F ∈
        (Ideal.span {(X 0 : CoordinatePolynomial 4)}).map
          (map (algebraMap ℚ (AlgebraicClosure ℚ))) := by
      simpa only [Ideal.map_span, Set.image_singleton, map_X, Ideal.mem_span_singleton] using hh
    exact Ideal.mem_span_singleton.mp
      ((mem_ideal_scalar_extension_iff (Ideal.span {X 0}) F).mp hmem)
  have hfabs : AbsolutelyIrreducibleRat (affineChart 3 F) := by
    rw [AbsolutelyIrreducibleRat, ← affineChart_map]
    exact affineChart_irreducible_of_not_variable_dvd _ (hhom.map _) habs hXK
  have hfdeg : (affineChart 3 F).totalDegree = d :=
    affineChart_degree_of_not_variable_dvd F hhom hX
  obtain ⟨T,δ,hT,hcard,hcount⟩ := hcover (affineChart 3 F) hfabs hfdeg B hB
  let e := @projectiveClosureIdeal ℚ _ 3
  let δ' := fun J => δ (Function.invFun e J)
  have hinj : Function.Injective e := projectiveClosureIdeal_injective
  have hleft : Function.LeftInverse (Function.invFun e) e := Function.leftInverse_invFun hinj
  refine ⟨T.image e,δ',?_,?_,?_⟩
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hIT,hδ⟩ := hT I hI
    have : I.IsPrime := hIT.isPrime
    have : (I.map (map (algebraMap ℚ (AlgebraicClosure ℚ)))).IsPrime := hIT.geometric
    have hδeq : δ' (e I) = δ I := congrArg δ (hleft I)
    rw [hδeq]
    exact ⟨inferInstance,projectiveClosureIdeal_homogeneous I,
      projectiveClosureIdeal_geometrically_prime (L := AlgebraicClosure ℚ) I,
      (homogeneous_mem_projectiveClosureIdeal_iff I F hhom).mpr hIT.mem,
      projectiveClosureIdeal_not_X_zero I,hIT.pos,projectiveClosureIdeal_curveDegree I hIT.degree,
      hδ⟩
  · rw [Finset.card_image_of_injective T hinj]
    exact hcard
  · simpa only [e, projectiveClosure_union_chart] using hcount

end
end CCDN
