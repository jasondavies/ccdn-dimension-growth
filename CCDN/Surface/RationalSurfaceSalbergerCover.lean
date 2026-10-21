/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.SurfaceGeometricCurveCover
import CCDN.Projection.PrimitiveNormalization
import CCDN.Surface.SurfaceSalbergerCover
/-! Clearing rational coefficients preserves the exact geometric Salberger
cover and all of its uniform constants. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem rational_surface_salberger_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : CoordinatePolynomial 3),
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) f) →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
        (∀ I ∈ S, I.IsPrime ∧ I.height = 2 ∧ f ∈ I ∧
          GeometricCurveIdeal I ∧ 0 < δ I ∧ HasAffineCurveDegree I (δ I) ∧ δ I ≤ d ^ 2) ∧
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
  have hgabs : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) g) := by
    rw [heK]
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr haK).map MvPolynomial.C)).mpr habs
  obtain ⟨S,δ,hS,hcard,hcount⟩ := hcover g hgabs hgdeg B hB
  refine ⟨S,δ,?_,hcard,?_⟩
  · intro I hI
    obtain ⟨hp,hh,hg,hgeo,hpos,hdeg,hδ⟩ := hS I hI
    refine ⟨hp,hh,?_,hgeo,hpos,hdeg,hδ⟩
    rw [he] at hg
    have hh' := I.mul_mem_left (MvPolynomial.C a⁻¹) hg
    simpa only [← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, map_one, one_mul] using hh'
  · rw [he,smoothSurfaceLocus_C_mul a ha] at hcount
    exact hcount

end
end CCDN
