/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Surface.GeometricCurveCover
import CCDN.AuxiliaryPolynomial.PlaneAuxiliaryCount
import CCDN.Surface.MediumCurveCount
import CCDN.Surface.ResidueSalbergerCount
import CCDN.Surface.SalbergerCoverNumerics
import CCDN.Surface.SmallCurveCover

/-! The literal bounded-degree geometric curve cover for surfaces of
polynomial coefficient height. All constants precede the equation and
radius; the remaining height alternative is handled separately. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

/-- Since `B^(1/√d) ≥ 1`, the curve-component degree budget `d A (B^(1/√d) + 1)(1 + log B)` is
at most `2 d A B^(1/√d) (log B + 1)`. -/
private lemma curve_component_budget_le_double {d : ℕ} {A B s : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hs : s ≤ (d : ℝ) * A * (B ^ (1 / Real.sqrt (d : ℝ)) + 1) * (1 + Real.log B)) :
    s ≤ 2 * d * A * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) := by
  have hroot : 1 ≤ B ^ (1 / Real.sqrt (d : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hlogB := Real.log_nonneg hB
  calc
    _ ≤ _ := hs
    _ ≤ (d : ℝ) * A * (2 * B ^ (1 / Real.sqrt (d : ℝ))) * (1 + Real.log B) := by
      gcongr
      linarith
    _ = _ := by ring

/-- A subfamily of curve components of positive degrees whose total degree is at most
`A₀ B^(1/√d) (log B + 1)` has at most `2 A₀ (B^(1/√d) log B + 1)` members. -/
private lemma curve_component_card_le {ι : Type*} {S T : Finset ι} {δ : ι → ℕ} (hT : T ⊆ S)
    (hpos : ∀ I ∈ S, 0 < δ I) {d : ℕ} (hd : 1 ≤ d) {A₀ B : ℝ} (hA₀ : 0 ≤ A₀) (hB : 1 ≤ B)
    (hbudget : (∑ I ∈ S, (δ I : ℝ)) ≤
      A₀ * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) :
    (T.card : ℝ) ≤ 2 * A₀ * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) := by
  have hcard : (T.card : ℝ) ≤ ∑ I ∈ S, (δ I : ℝ) := by
    calc
      _ = ∑ _I ∈ T, (1 : ℝ) := by simp
      _ ≤ ∑ I ∈ T, (δ I : ℝ) := by
        apply sum_le_sum
        intro I hI
        exact_mod_cast hpos I (hT hI)
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hT (by intros; positivity)
  have hsqrt : 1 ≤ Real.sqrt (d : ℝ) := Real.le_sqrt_of_sq_le (by exact_mod_cast hd)
  have hα : 1 / Real.sqrt (d : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one hsqrt
  have hn := mul_le_mul_of_nonneg_left (salberger_curve_number_normalization hα hB) hA₀
  linarith [hcard.trans hbudget]

/-- A point count bounded by `d²` times a degree sum of size at most
`A₀ B^(1/√d) (log B + 1)` is at most `d² A₀ B^(2/√d) (log B + 1)^4`. -/
private lemma count_le_of_curve_degree_budget {d : ℕ} {A₀ B N s : ℝ} (hA₀ : 0 ≤ A₀) (hB : 1 ≤ B)
    (hN : N ≤ ((d ^ 2 : ℕ) : ℝ) * s)
    (hs : s ≤ A₀ * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) :
    N ≤ ((d : ℝ) ^ 2 * A₀) * B ^ (2 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ^ 4 := by
  have hw := salberger_nonnegative_weight_mono
    (show 0 ≤ 1 / Real.sqrt (d : ℝ) by positivity) hB
  have he : 2 * (1 / Real.sqrt (d : ℝ)) = 2 / Real.sqrt (d : ℝ) := by ring
  rw [he] at hw
  calc
    _ ≤ ((d ^ 2 : ℕ) : ℝ) * s := hN
    _ ≤ ((d ^ 2 : ℕ) : ℝ) * (A₀ * B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) := by gcongr
    _ = ((d : ℝ) ^ 2 * A₀) * (B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1)) := by
      push_cast; ring
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hw (show 0 ≤ (d : ℝ) ^ 2 * A₀ by positivity)
      nlinarith

/-- Literal bounded-degree geometric curve cover of a degree-`d` surface whose coefficient
height is polynomial in `B`: at most `C (B^(1/√d) log B + 1)` geometric curves of degree at most
`d²` cover all smooth points of height at most `B` outside a set of
`C B^(2/√d + c / log(1 + log B))` points. -/
theorem surface_salberger_cover_of_height (d : ℕ) (hd : 1 ≤ d)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ),
      AbsolutelyIrreducible f →
      f.totalDegree = d → ∀ H B : ℝ, 1 ≤ H → 1 ≤ B →
      CoefficientHeightLE f H →
      Real.log H ≤ K * (Real.log B + 1) →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
        (∀ I ∈ S, IsGeometricSurfaceCurve (map (Int.castRingHom ℚ) f) I (δ I) ∧ δ I ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ S, idealZeroLocus I)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
  classical
  let A := surfaceCongruenceDegreeConstant d K
  have hA : 0 ≤ A := (surfaceCongruenceDegreeConstant_pos d K).le
  let A₀ := 2 * (d : ℝ) * A
  have hA₀ : 0 ≤ A₀ := by dsimp only [A₀]; positivity
  let D := A₀ * surfaceResidueLogScale d K
  have hlogscale := surfaceResidueLogScale_one_le d hK
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  obtain ⟨Cm,hCm,hmedium⟩ := medium_degree_curve_union_bound
  obtain ⟨Cr,cr,hCr,hcr,hres⟩ := surface_residue_salberger_count d hd K A hK hA
  let E := (d : ℝ) ^ 2 * A₀ + Cm * A₀ * D ^ 2 * (D + 1)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  obtain ⟨Cn,cn,hCn,hcn,hcombine⟩ := salberger_remainders_combine E Cr cr hE hCr.le hcr
  refine ⟨2 * A₀ + Cn + 1, cn, by positivity, hcn, ?_⟩
  intro f habs hfd H B hH hB hcoeff hheight
  subst d
  have hir := rational_irreducible_of_charZero_map f habs
  have hL := surfaceResidueWindow_one_le f.totalDegree hK hB
  have hW := isSurfaceResidueWindow_of_log_height hd hK hB hH hcoeff hheight
  obtain ⟨F⟩ := exists_surface_congruence_family f habs (by omega) hK hH hB hcoeff hheight
  obtain ⟨S,δ,hS,hcover,hbudget⟩ := exists_surface_initial_curve_components f hir F
  have hbudget' := curve_component_budget_le_double hA hB hbudget
  let kept := S.filter (fun I => δ I ≤ f.totalDegree ^ 2 ∧ GeometricCurveIdeal I)
  refine ⟨kept,δ,?_,?_,?_⟩
  · intro I hI
    obtain ⟨hIS,hδ,hgeo⟩ := mem_filter.mp hI
    exact ⟨⟨(hS I hIS).toIsSurfaceCurve,hgeo,(hS I hIS).pos⟩,hδ⟩
  · have hcard := curve_component_card_le (show kept ⊆ S from filter_subset _ S)
      (fun I hI => (hS I hI).pos) hd hA₀ hB hbudget'
    have hbase : 0 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B + 1 := by
      have := Real.log_nonneg hB
      positivity
    exact hcard.trans (mul_le_mul_of_nonneg_right (by linarith) hbase)
  · let medium := S.filter (fun I => f.totalDegree ^ 2 < δ I ∧ (δ I : ℝ) ≤
      2 * f.totalDegree * A * surfaceResidueLogBudget B (surfaceResidueWindow f.totalDegree K B))
    have hmed := hmedium medium δ f.totalDegree hd A₀ D B hA₀ hD hB
      (fun I hI => by
        obtain ⟨hIS,hδ,_⟩ := mem_filter.mp hI
        exact ⟨(hS I hIS).isPrime,by nlinarith,(hS I hIS).degree⟩)
      (fun I hI => by
        have hh := (mem_filter.mp hI).2.2
        rw [surfaceResidueLogBudget_window] at hh
        simpa only [D,A₀,mul_assoc] using hh)
      ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans
        hbudget')
    have hbad := count_le_of_curve_degree_budget hA₀ hB
      (nongeometric_curve_union_count_le S δ (f.totalDegree ^ 2)
        (fun I hI => ⟨(hS I hI).isPrime,(hS I hI).pos,(hS I hI).degree⟩)
        (show 0 ≤ B by linarith)) hbudget'
    have hresidual := hres f rfl B hB F hir S δ (fun I hI => (hS I hI).toIsSurfaceCurve)
    have hpoint := surface_smooth_outside_geometric_cover f hir hA hW F S δ (f.totalDegree ^ 2)
      hS hcover
    have hpointR : (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
        (⋃ I ∈ kept, idealZeroLocus I)) B : ℝ) ≤
        count (⋃ I ∈ S.filter (fun I => δ I ≤ f.totalDegree ^ 2 ∧ ¬GeometricCurveIdeal I),
          idealZeroLocus I) B +
        count (⋃ I ∈ medium, idealZeroLocus I) B +
        count (surfaceResidueResidualLocus F S (surfaceResidueWindow f.totalDegree K B)
          (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) hL) B := by
      simpa only [Nat.cast_add, kept, medium] using (Nat.cast_le (α := ℝ)).mpr hpoint
    have htotal : (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
        (⋃ I ∈ kept, idealZeroLocus I)) B : ℝ) ≤
        E * B ^ (2 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) ^ 4 +
          Cr * B ^ (2 / Real.sqrt (f.totalDegree : ℝ) + cr / Real.log (1 + Real.log B)) := by
      have hh := add_le_add (add_le_add hbad hmed) hresidual
      apply hpointR.trans
      convert hh using 1
      dsimp only [E]
      ring
    have hp : 0 ≤ B ^ (2 / Real.sqrt (f.totalDegree : ℝ) + cn / Real.log (1 + Real.log B)) := by
      positivity
    exact (htotal.trans (hcombine (2 / Real.sqrt (f.totalDegree : ℝ)) B hB)).trans
      (mul_le_mul_of_nonneg_right (by linarith only [hA₀]) hp)

end
end CCDN
