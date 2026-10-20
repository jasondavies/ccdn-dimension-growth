module

public import AffineCurveCounting.SurfaceGeometricCurveCover
public import AffineCurveCounting.SurfaceMediumCurveCount
public import AffineCurveCounting.SurfaceResidueSalbergerCount
public import AffineCurveCounting.SalbergerCoverNumerics

/-! The literal bounded-degree geometric curve cover for surfaces of
polynomial coefficient height. All constants precede the equation and
radius; the remaining height alternative is handled separately. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Finset Classical

theorem surface_salberger_cover_of_height (d : ℕ) (hd : 1 ≤ d)
    (K : ℝ) (hK : 0 ≤ K) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ),
      Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f) →
      f.totalDegree = d → ∀ H B : ℝ, 1 ≤ H → 1 ≤ B →
      (∀ e, |(f.coeff e : ℝ)| ≤ H) →
      Real.log H ≤ K * (Real.log B + 1) →
      ∃ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ),
        (∀ I ∈ S, I.IsPrime ∧ I.height = 2 ∧ map (Int.castRingHom ℚ) f ∈ I ∧
          GeometricCurveIdeal I ∧ 0 < δ I ∧ HasAffineCurveDegree I (δ I) ∧ δ I ≤ d ^ 2) ∧
        (S.card : ℝ) ≤ C * (B ^ (1 / Real.sqrt (d : ℝ)) * Real.log B + 1) ∧
        (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
          (⋃ I ∈ S, idealZeroLocus I)) B : ℝ) ≤
          C * B ^ (2 / Real.sqrt (d : ℝ) + c / Real.log (1 + Real.log B)) := by
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
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hlogB := Real.log_nonneg hB
  have hroot : 1 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) := Real.one_le_rpow hB (by positivity)
  have hL := surfaceResidueWindow_one_le f.totalDegree hK hB
  obtain ⟨hderivative,hX,hBX,hXL⟩ := surfaceResidueWindow_parameters hd hK hB hheight
  obtain ⟨F⟩ := exists_surface_congruence_family f habs (by omega) hK hH hB hcoeff hheight
  have hproper : ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) F.initial :=
    F.proper ∅ (by simp) (emptySmoothAffineResidueFamily f)
  obtain ⟨S,δ,hS,hcover,hbudget,_⟩ := exists_completeIntersection_curve_components
    (map (Int.castRingHom ℚ) f) (map (Int.castRingHom ℚ) F.initial) hir hproper
  have hinitial : (F.initial.totalDegree : ℝ) ≤ A *
      (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B) := by
    have hh := F.degree_le ∅ (by simp) (emptySmoothAffineResidueFamily f)
    simpa only [SurfaceCongruenceFamily.initial, sum_empty, Real.exp_zero, div_one, add_zero] using hh
  have hbudget' : (∑ I ∈ S, (δ I : ℝ)) ≤
      A₀ * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) := by
    rw [rational_map_totalDegree, rational_map_totalDegree] at hbudget
    have hb : (∑ I ∈ S, (δ I : ℝ)) ≤ (f.totalDegree : ℝ) * F.initial.totalDegree := by exact_mod_cast hbudget
    calc
      _ ≤ _ := hb
      _ ≤ (f.totalDegree : ℝ) * (A *
          (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) + 1) * (1 + Real.log B)) := by gcongr
      _ ≤ (f.totalDegree : ℝ) * (A *
          (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) * (1 + Real.log B)) := by
        gcongr
        linarith
      _ = _ := by dsimp only [A₀]; ring
  let kept := S.filter (fun I => δ I ≤ f.totalDegree ^ 2 ∧ GeometricCurveIdeal I)
  let medium := S.filter (fun I => f.totalDegree ^ 2 < δ I ∧ (δ I : ℝ) ≤
    2 * f.totalDegree * A * surfaceResidueLogBudget B (surfaceResidueWindow f.totalDegree K B))
  let bad := S.filter (fun I => δ I ≤ f.totalDegree ^ 2 ∧ ¬GeometricCurveIdeal I)
  refine ⟨kept,δ,?_,?_,?_⟩
  · intro I hI
    obtain ⟨hIS,hδ,hgeo⟩ := mem_filter.mp hI
    obtain ⟨hp,hh,hf,_,hpos,hdeg⟩ := hS I hIS
    exact ⟨hp,hh,hf,hgeo,hpos,hdeg,hδ⟩
  · have hcard : (kept.card : ℝ) ≤ ∑ I ∈ S, (δ I : ℝ) := by
      calc
        _ = ∑ _I ∈ kept, (1 : ℝ) := by simp
        _ ≤ ∑ I ∈ kept, (δ I : ℝ) := by
          apply sum_le_sum
          intro I hI
          have hh := (hS I (mem_filter.mp hI).1).2.2.2.2.1
          exact_mod_cast hh
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
    have hsqrt : 1 ≤ Real.sqrt (f.totalDegree : ℝ) :=
      Real.le_sqrt_of_sq_le (by exact_mod_cast hd)
    have hα : 1 / Real.sqrt (f.totalDegree : ℝ) ≤ 1 := by
      simpa using one_div_le_one_div_of_le zero_lt_one hsqrt
    have hn := mul_le_mul_of_nonneg_left (salberger_curve_number_normalization hα hB) hA₀
    have hbase : 0 ≤ B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * Real.log B + 1 := by positivity
    nlinarith [hcard.trans hbudget']
  · have hmed := hmedium medium δ f.totalDegree hd A₀ D B hA₀ hD hB
      (fun I hI => by
        obtain ⟨hIS,hδ,_⟩ := mem_filter.mp hI
        obtain ⟨hp,_,_,_,_,hdeg⟩ := hS I hIS
        exact ⟨hp,by nlinarith,hdeg⟩)
      (fun I hI => by
        have hh := (mem_filter.mp hI).2.2
        rw [surfaceResidueLogBudget_window] at hh
        simpa only [D,A₀,mul_assoc] using hh)
      ((sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hbudget')
    have hbad := nongeometric_curve_union_count_le S δ (f.totalDegree ^ 2)
      (fun I hI => by
        obtain ⟨hp,_,_,_,hpos,hdeg⟩ := hS I hI
        exact ⟨hp,hpos,hdeg⟩) (show 0 ≤ B by linarith)
    have hbad' : (count (⋃ I ∈ bad, idealZeroLocus I) B : ℝ) ≤
        ((f.totalDegree : ℝ) ^ 2 * A₀) *
          B ^ (2 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) ^ 4 := by
      have hw := salberger_nonnegative_weight_mono
        (show 0 ≤ 1 / Real.sqrt (f.totalDegree : ℝ) by positivity) hB
      have he : 2 * (1 / Real.sqrt (f.totalDegree : ℝ)) = 2 / Real.sqrt (f.totalDegree : ℝ) := by ring
      rw [he] at hw
      calc
        _ ≤ (f.totalDegree ^ 2 : ℕ) * ∑ I ∈ S, (δ I : ℝ) := hbad
        _ ≤ (f.totalDegree ^ 2 : ℕ) *
            (A₀ * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1)) := by gcongr
        _ = ((f.totalDegree : ℝ) ^ 2 * A₀) *
            (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1)) := by push_cast; ring
        _ ≤ _ := by
          have hh := mul_le_mul_of_nonneg_left hw
            (show 0 ≤ (f.totalDegree : ℝ) ^ 2 * A₀ by positivity)
          nlinarith
    have hresidual := hres f rfl B hB F hir S δ (fun I hI => by
      obtain ⟨hp,hh,hf,_,_,hdeg⟩ := hS I hI
      exact ⟨hp,hh,hf,hdeg⟩)
    have hpoint := surface_smooth_outside_geometric_cover f hir hA hB hH hL hcoeff
      hderivative hX hBX hXL F S δ (f.totalDegree ^ 2)
      (fun I hI => by
        obtain ⟨hp,hh,hf,hg,_,hdeg⟩ := hS I hI
        exact ⟨hp,hh,hf,hg,hdeg⟩) hcover
    have hpointR : (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
        (⋃ I ∈ kept, idealZeroLocus I)) B : ℝ) ≤
        count (⋃ I ∈ bad, idealZeroLocus I) B +
        count (⋃ I ∈ medium, idealZeroLocus I) B +
        count (surfaceResidueResidualLocus F S (surfaceResidueWindow f.totalDegree K B)
          (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) hL) B := by
      simpa only [Nat.cast_add, kept, bad, medium] using (Nat.cast_le (α := ℝ)).mpr hpoint
    have htotal : (count (smoothSurfaceLocus (map (Int.castRingHom ℚ) f) \
        (⋃ I ∈ kept, idealZeroLocus I)) B : ℝ) ≤
        E * B ^ (2 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) ^ 4 +
          Cr * B ^ (2 / Real.sqrt (f.totalDegree : ℝ) + cr / Real.log (1 + Real.log B)) := by
      have hh := add_le_add (add_le_add hbad' hmed) hresidual
      apply hpointR.trans
      convert hh using 1
      dsimp only [E]
      ring
    have hh := htotal.trans (hcombine (2 / Real.sqrt (f.totalDegree : ℝ)) B hB)
    have hp : 0 ≤ B ^ (2 / Real.sqrt (f.totalDegree : ℝ) + cn / Real.log (1 + Real.log B)) := by positivity
    exact hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hA₀]) hp)

end
end AffineCurveCounting
