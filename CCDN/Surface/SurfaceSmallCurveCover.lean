/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.SurfaceResidueCover
public import CCDN.Hypersurface.SingularHypersurfaceCount
import CCDN.Auxiliary.PlaneAuxiliaryCount
import CCDN.Hilbert.CompleteIntersectionDegreeBudget
/-! A small-curve and residual cover for a surface of controlled
coefficient height. Both the auxiliaries and the initial prime components
are constructed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Classical

theorem exists_surface_small_curve_residual_cover
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree) {K H B L X : ℝ}
    (hK : 0 ≤ K) (hH : 1 ≤ H) (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    (hheight : Real.log H ≤ K * (Real.log B + 1))
    (hderivative : 4 * Real.log ((f.totalDegree : ℝ) + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ L)
    (hX : 1 < X) (hBX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hXL : X ≤ Real.exp L) :
    ∃ F : SurfaceCongruenceFamily f B (surfaceCongruenceDegreeConstant f.totalDegree K),
      ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
        ∃ δ : Ideal (CoordinatePolynomial 3) → ℕ,
          (∀ I ∈ S, I.IsPrime ∧ I.height = 2 ∧
            map (Int.castRingHom ℚ) f ∈ I ∧
            map (Int.castRingHom ℚ) F.initial ∈ I ∧
            0 < δ I ∧ HasAffineCurveDegree I (δ I)) ∧
          (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) *
            surfaceCongruenceDegreeConstant f.totalDegree K *
            (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) ∧
          count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
            count (singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)) B +
            count (⋃ I ∈ S.filter (fun I => (δ I : ℝ) ≤
              2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K *
                surfaceResidueLogBudget B L), idealZeroLocus I) B +
            count (surfaceResidueResidualLocus F S L X hL) B := by
  classical
  have hA : 0 ≤ surfaceCongruenceDegreeConstant f.totalDegree K :=
    (surfaceCongruenceDegreeConstant_pos f.totalDegree K).le
  have hirQ := rational_irreducible_of_charZero_map f hir
  obtain ⟨F⟩ := exists_surface_congruence_family f hir hd hK hH hB hcoeff hheight
  have hproper : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) F.initial :=
    F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f)
  obtain ⟨S, δ, hS, hcover, hbudget, _⟩ :=
    exists_completeIntersection_curve_components (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) F.initial) hirQ hproper
  have hinitial : (F.initial.totalDegree : ℝ) ≤
      surfaceCongruenceDegreeConstant f.totalDegree K *
        (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
    have hh := F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
    simpa only [SurfaceCongruenceFamily.initial, sum_empty, Real.exp_zero, div_one, add_zero] using hh
  refine ⟨F, S, δ, hS, ?_, ?_⟩
  · rw [rational_map_totalDegree, rational_map_totalDegree] at hbudget
    have hb : (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) * F.initial.totalDegree := by
      exact_mod_cast hbudget
    have hm := mul_le_mul_of_nonneg_left hinitial (Nat.cast_nonneg (α := ℝ) f.totalDegree)
    exact hb.trans (by simpa only [mul_assoc] using hm)
  · let small := S.filter (fun I => (δ I : ℝ) ≤
      2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K *
        surfaceResidueLogBudget B L)
    let singular := singularHypersurfaceLocus (map (Int.castRingHom ℚ) f)
    let retained := ⋃ I ∈ small, idealZeroLocus I
    let residual := surfaceResidueResidualLocus F S L X hL
    have hpoint (x : IntPoint 3) (hx : ∀ j, |(x j : ℝ)| ≤ B)
        (hxf : eval x f = 0) :
        rationalPoint x ∈ singular ∪ retained ∪ residual := by
      by_cases hsmooth : ∃ j, eval x (pderiv j f) ≠ 0
      · have hinit := F.initial_vanishes x hx hxf
        have hxfQ : rationalPoint x ∈ zeroLocus (map (Int.castRingHom ℚ) f) := by
          have hh := congrArg (Int.castRingHom ℚ) hxf
          rw [map_eval, map_zero] at hh
          exact hh
        have hxinitQ : rationalPoint x ∈ zeroLocus (map (Int.castRingHom ℚ) F.initial) := by
          have hh := congrArg (Int.castRingHom ℚ) hinit
          rw [map_eval, map_zero] at hh
          exact hh
        have hxcover : rationalPoint x ∈ ⋃ I ∈ S, idealZeroLocus I := by
          rw [← hcover]
          exact ⟨hxfQ, hxinitQ⟩
        obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hxcover
        obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
        by_cases hsmall : (δ I : ℝ) ≤
            2 * f.totalDegree * surfaceCongruenceDegreeConstant f.totalDegree K *
              surfaceResidueLogBudget B L
        · exact Or.inl (Or.inr (Set.mem_iUnion.mpr
            ⟨I, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨hIS, hsmall⟩, hxI⟩⟩))
        · right
          obtain ⟨hIp, hIheight, hfI, hinitI, _, hdegree⟩ := hS I hIS
          exact large_curve_point_mem_surfaceResidueResidualLocus f hirQ hA hB hH hL hcoeff
            hderivative hX hBX hXL F S I hIS hIp hIheight hfI hinitI hdegree
            (lt_of_not_ge hsmall) x hx hxf hxI hsmooth
      · left
        left
        change eval (rationalPoint x) (map (Int.castRingHom ℚ) f) = 0 ∧ _
        constructor
        · have hh := congrArg (Int.castRingHom ℚ) hxf
          rw [map_eval, map_zero] at hh
          exact hh
        · intro j
          have hz : eval x (pderiv j f) = 0 := by
            by_contra hn
            exact hsmooth ⟨j, hn⟩
          have hh := congrArg (Int.castRingHom ℚ) hz
          rw [map_eval, map_zero] at hh
          rw [pderiv_map]
          exact hh
    have hcount : count (zeroLocus (map (Int.castRingHom ℚ) f)) B ≤
        count (singular ∪ retained ∪ residual) B := by
      apply card_le_card
      intro x hx
      obtain ⟨hbox, hzero⟩ := mem_integralPoints.mp hx
      have hxf : eval x f = 0 := by
        apply (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)
        rw [map_eval, map_zero]
        exact hzero
      exact mem_integralPoints.mpr ⟨hbox, hpoint x hbox hxf⟩
    exact hcount.trans ((count_union_le (singular ∪ retained) residual B).trans
      (Nat.add_le_add_right (count_union_le singular retained B) _))

end
end CCDN
