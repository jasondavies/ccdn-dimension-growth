/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Surface.GeometricCurveCover
import CCDN.Algebra.PrimitiveNormalization
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDNPaper.Surface.GeometricCoefficientReduction
import CCDNPaper.Surface.SalbergerHeightCover
import Mathlib.Algebra.Order.Star.Real

/-! A coefficient-uniform Salberger cover for every geometrically integral
affine surface. This has the literal curve-number and exceptional-point
exponents of CCDN Theorem 4.3.5, and uniformly bounded geometric curve degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem primitive_surface_salberger_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ), PrimitiveIntegerPolynomial f →
      AbsolutelyIrreducible f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
        (∀ I ∈ S, IsGeometricSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I) ∧ δ I ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ S, idealZeroLocus I)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  let K := surfaceCoefficientLogConstant d
  have hK : 0 ≤ K := (surfaceCoefficientLogConstant_pos d).le
  obtain ⟨C,c,hC,hc,hcover⟩ := surface_salberger_cover_of_height d hd K hK
  refine ⟨C + (d : ℝ) ^ 2 + (d : ℝ) ^ 4 + 1,c,by positivity,hc,?_⟩
  intro f hprim habs hfd B hB
  have hir := rational_irreducible_of_charZero_map f habs
  have hf0 : f ≠ 0 := by intro hz; exact hir.ne_zero (by rw [hz,map_zero])
  have hbase : 1 ≤ B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1 := by
    have hh : 0 ≤ B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.log_nonneg hB)
    linarith
  have hden : 0 ≤ Real.log (1 + Real.log B) := Real.log_nonneg (by linarith [Real.log_nonneg hB])
  have hp : 1 ≤ B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) :=
    Real.one_le_rpow hB (by positivity)
  rcases primitive_surface_geometric_coefficient_reduction f hprim hir hB with hheight | hlarge
  · have hH : 1 ≤ (integerCoefficientHeight f : ℝ) := by
      exact_mod_cast integerCoefficientHeight_pos f hf0
    obtain ⟨S,δ,hS,hcard,hcount⟩ := hcover f habs hfd (integerCoefficientHeight f : ℝ) B
      hH hB (coefficient_abs_le_integerCoefficientHeight f) (by simpa only [hfd] using hheight)
    refine ⟨S,δ,hS,?_,?_⟩
    · exact hcard.trans (mul_le_mul_of_nonneg_right
        (by nlinarith [sq_nonneg (d : ℝ), sq_nonneg ((d : ℝ)^2)]) (by linarith))
    · exact hcount.trans (mul_le_mul_of_nonneg_right
        (by nlinarith [sq_nonneg (d : ℝ), sq_nonneg ((d : ℝ)^2)]) (by linarith))
  · obtain ⟨S,δ,hS,hcard,hcount⟩ := hlarge
    refine ⟨S,δ,by simpa only [hfd] using hS,?_,?_⟩
    · have hh : (S.card : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast (hfd ▸ hcard)
      have hc' : (d : ℝ) ^ 2 ≤ C + (d : ℝ) ^ 2 + (d : ℝ) ^ 4 + 1 := by
        nlinarith [sq_nonneg (d : ℝ), sq_nonneg ((d : ℝ)^2)]
      exact hh.trans (hc'.trans (le_mul_of_one_le_right (by positivity) hbase))
    · have hmono : count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ S, idealZeroLocus I)) B ≤
          count (zeroLocus (map (Int.castRingHom ℚ) f) \
            (⋃ I ∈ S, idealZeroLocus I)) B :=
        count_mono (fun x hx => ⟨hx.1.1,hx.2⟩) le_rfl
      have hh : (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ S, idealZeroLocus I)) B : ℝ) ≤ (d : ℝ) ^ 4 := by
        exact (Nat.cast_le.mpr hmono).trans (by simpa only [hfd] using hcount)
      have hc' : (d : ℝ) ^ 4 ≤ C + (d : ℝ) ^ 2 + (d : ℝ) ^ 4 + 1 := by
        nlinarith [sq_nonneg (d : ℝ), sq_nonneg ((d : ℝ)^2)]
      exact hh.trans (hc'.trans (le_mul_of_one_le_right (by positivity) hp))

/-- Multiplying a surface equation by a nonzero rational constant does not change its
nonsingular rational points. -/
lemma smoothSurfaceLocus_C_mul (a : ℚ) (ha : a ≠ 0) (f : CoordinatePolynomial 3) :
    smoothSurfaceLocus (C a * f) = smoothSurfaceLocus f := by
  ext x
  simp only [smoothSurfaceLocus, Set.mem_sdiff, zeroLocus, singularHypersurfaceLocus,
    Set.mem_ofPred_eq, eval_mul, eval_C, pderiv_C_mul, mul_eq_zero, ha, false_or]

/-- The literal affine form of Salberger's covering theorem. Both constants
are chosen before the surface and B; every retained curve is geometrically
integral, has degree at most d², and is contained in the surface. -/
theorem surface_salberger_cover (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ),
      AbsolutelyIrreducible f →
      f.totalDegree = d → ∀ B : ℝ, 1 ≤ B →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
        (∀ I ∈ S, I.IsPrime ∧ I.height = 2 ∧ map (Int.castRingHom ℚ) f ∈ I ∧
          GeometricCurveIdeal I ∧ 0 < δ I ∧ HasAffineCurveDegree I (δ I) ∧ δ I ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ S, idealZeroLocus I)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  obtain ⟨C,c,hC,hc,hcover⟩ := primitive_surface_salberger_cover d hd
  refine ⟨C,c,hC,hc,?_⟩
  intro f habs hfd B hB
  have hf0 : f ≠ 0 := by intro hz; exact habs.ne_zero (by rw [hz,map_zero])
  obtain ⟨a,g,ha,hprim,he⟩ := exists_primitive_integer_factor f hf0
  have hgdeg : g.totalDegree = d := (integer_scalar_factor_degree hf0 ha he).trans hfd
  have hane : (a : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast ha
  have hgabs : AbsolutelyIrreducible g := by
    rw [AbsolutelyIrreducible, he,map_mul,map_C] at habs
    exact (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr hane).map MvPolynomial.C)).mp habs
  obtain ⟨S,δ,hS,hcard,hcount⟩ := hcover g hprim hgabs hgdeg B hB
  refine ⟨S,δ,?_,hcard,?_⟩
  · intro I hI
    obtain ⟨hg,hδ⟩ := hS I hI
    refine ⟨hg.isPrime,hg.height_eq,?_,hg.geometric,hg.pos,hg.degree,hδ⟩
    rw [he,map_mul,map_C]
    exact I.mul_mem_left _ hg.mem
  · rw [he,map_mul,map_C,smoothSurfaceLocus_C_mul _ (by change (a : ℚ) ≠ 0; exact_mod_cast ha)]
    exact hcount

end
end CCDN
