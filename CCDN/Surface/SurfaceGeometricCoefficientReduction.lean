/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.SurfaceGeometricCurveCover
public import CCDN.Surface.SurfaceCoefficientReduction
import CCDN.Auxiliary.PlaneAuxiliaryCount
import CCDN.Auxiliary.UnscaledHypersurfaceAuxiliary
import CCDN.Hilbert.CompleteIntersectionDegreeBudget
import Mathlib.Algebra.Order.Star.Real
/-! The large-coefficient alternative for the exact surface covering
statement: bounded-degree geometric curves and a height-independent residual. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- A degree-at-most-d proper auxiliary yields at most d² geometric curves
of degree at most d², with at most d⁴ remaining integer points. -/
theorem surface_geometric_cover_of_small_auxiliary
    (f g : MvPolynomial (Fin 3) ℤ)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    (hfg : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g)
    (hgdegree : g.totalDegree ≤ f.totalDegree)
    {B : ℝ} (hB : 0 ≤ B)
    (hzero : ∀ x : IntPoint 3, InBox x B →
      eval x f = 0 → eval x g = 0) :
    ∃ (T : Finset (Ideal (CoordinatePolynomial 3)))
      (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ T, I.IsPrime ∧ I.height = 2 ∧ map (Int.castRingHom ℚ) f ∈ I ∧
        GeometricCurveIdeal I ∧ 0 < δ I ∧ HasAffineCurveDegree I (δ I) ∧
        δ I ≤ f.totalDegree ^ 2) ∧
      T.card ≤ f.totalDegree ^ 2 ∧
      (count (zeroLocus (map (Int.castRingHom ℚ) f) \
        (⋃ I ∈ T, idealZeroLocus I)) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 4 := by
  classical
  obtain ⟨S, δ, hS, hcover, hbudget, _⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) g) hf hfg
  rw [rational_map_totalDegree, rational_map_totalDegree] at hbudget
  have hsum : (∑ I ∈ S, δ I) ≤ f.totalDegree ^ 2 :=
    hbudget.trans (by simpa only [pow_two] using Nat.mul_le_mul_left f.totalDegree hgdegree)
  have hδ (I) (hI : I ∈ S) : δ I ≤ f.totalDegree ^ 2 :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hI).trans hsum
  let T := S.filter GeometricCurveIdeal
  have hTsub : T ⊆ S := filter_subset _ _
  refine ⟨T, δ, ?_, ?_, ?_⟩
  · intro I hI
    obtain ⟨hIS, hgeom⟩ := mem_filter.mp hI
    obtain ⟨hprime, hheight, hfI, _, hpos, hdegree⟩ := hS I hIS
    exact ⟨hprime, hheight, hfI, hgeom, hpos, hdegree, hδ I hIS⟩
  · apply (card_le_card hTsub).trans
    calc
      S.card = ∑ _I ∈ S, 1 := by simp
      _ ≤ ∑ I ∈ S, δ I := sum_le_sum (fun I hI => (hS I hI).2.2.2.2.1)
      _ ≤ _ := hsum
  · have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ T, idealZeroLocus I)) B ≤
        count (⋃ I ∈ S.filter (fun I => δ I ≤ f.totalDegree ^ 2 ∧
          ¬GeometricCurveIdeal I), idealZeroLocus I) B := by
      apply card_le_card
      intro x hx
      obtain ⟨hxB, hxf, hxnot⟩ := mem_integralPoints.mp hx
      have hf0 : eval x f = 0 := by
        apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
        rw [map_eval, map_zero]
        exact hxf
      have hg0 : rationalPoint x ∈ zeroLocus (map (Int.castRingHom ℚ) g) := by
        have hh := congrArg (Int.castRingHom ℚ) (hzero x hxB hf0)
        rwa [map_eval, map_zero] at hh
      have hxcover : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := by
        rw [← hcover]
        exact ⟨hxf, hg0⟩
      obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hxcover
      obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
      have hnon : ¬GeometricCurveIdeal I := by
        intro hgeom
        exact hxnot (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
          ⟨mem_filter.mpr ⟨hIS, hgeom⟩, hxI⟩⟩)
      exact mem_integralPoints.mpr ⟨hxB, Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨hIS, hδ I hIS, hnon⟩, hxI⟩⟩⟩
    have hh := nongeometric_curve_union_count_le S δ (f.totalDegree ^ 2)
      (fun I hI => ⟨(hS I hI).1, (hS I hI).2.2.2.2⟩) hB
    have hsumR : (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) ^ 2 := by
      exact_mod_cast hsum
    calc
      _ ≤ _ := Nat.cast_le.mpr hcount
      _ ≤ (f.totalDegree ^ 2 : ℕ) * ∑ I ∈ S, (δ I : ℝ) := hh
      _ ≤ (f.totalDegree : ℝ) ^ 4 := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hsumR (sq_nonneg (f.totalDegree : ℝ))]

/-- The coefficient-height dichotomy retains geometric curves in its
large-height branch, rather than replacing them by an O(B) count. -/
theorem primitive_surface_geometric_coefficient_reduction
    (f : MvPolynomial (Fin 3) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hf : Irreducible (map (Int.castRingHom ℚ) f))
    {B : ℝ} (hB : 1 ≤ B) :
    Real.log (integerCoefficientHeight f : ℝ) ≤
      surfaceCoefficientLogConstant f.totalDegree * (Real.log B + 1) ∨
    ∃ (T : Finset (Ideal (CoordinatePolynomial 3)))
      (δ : Ideal (CoordinatePolynomial 3) → ℕ),
      (∀ I ∈ T, I.IsPrime ∧ I.height = 2 ∧ map (Int.castRingHom ℚ) f ∈ I ∧
        GeometricCurveIdeal I ∧ 0 < δ I ∧ HasAffineCurveDegree I (δ I) ∧
        δ I ≤ f.totalDegree ^ 2) ∧
      T.card ≤ f.totalDegree ^ 2 ∧
      (count (zeroLocus (map (Int.castRingHom ℚ) f) \
        (⋃ I ∈ T, idealZeroLocus I)) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 4 := by
  have hf0 : f ≠ 0 := by intro h; exact hf.ne_zero (by rw [h, map_zero])
  rcases affine_coefficient_height_dichotomy f hf0 hprim hB with
    hheight | ⟨g, _, hproper, hdeg, hzero⟩
  · left
    have hlog := Real.log_nonneg hB
    have hNlog := Real.log_natCast_nonneg ((3 + f.totalDegree).choose f.totalDegree)
    have hNd : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) * f.totalDegree := by
      positivity
    have hNlog' : (0 : ℝ) ≤ ((3 + f.totalDegree).choose f.totalDegree : ℝ) *
        Real.log ((3 + f.totalDegree).choose f.totalDegree) := by positivity
    unfold surfaceCoefficientLogConstant
    nlinarith
  · exact Or.inr (surface_geometric_cover_of_small_auxiliary f g hf
      (fun h => hproper (hprim.rational_map_dvd_iff.mp h)) hdeg (by linarith) hzero)

end
end CCDN
