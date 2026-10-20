module

public import CCDN.SmallDegreeSurfaceCurveCount
public import CCDN.SurfaceDegreeOneCount
public import CCDN.PolynomialPredicates

/-! The retained part of the small-degree surface cover. Actual lines and
nonlinear prime curves are counted together, using their common degree
budget and the logarithmic cap on the retained degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Classical

theorem surface_curve_number_weight {d : ℕ} (hd : 5 ≤ d) {B : ℝ} (hB : 1 ≤ B) :
    B ^ (1 / Real.sqrt (d : ℝ)) * (Real.log B + 1) ≤
      (20 * Real.exp (1 / 20 : ℝ)) * B := by
  calc
    _ ≤ B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) := by
      apply mul_le_mul_of_nonneg_right
      · exact Real.rpow_le_rpow_of_exponent_le hB (by linarith)
      · linarith [Real.log_nonneg hB]
    _ ≤ _ := by
      have hh := surface_nonlinear_polylog_weight hd 1 hB
      norm_num only [Nat.factorial, Nat.cast_one, pow_one, div_one] at hh
      convert hh using 1

theorem retained_surface_curve_union_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : MvPolynomial (Fin 3) ℤ),
      HasAbsIrreducibleTopForm f →
      5 ≤ f.totalDegree →
      ∀ (S : Finset (Ideal (CoordinatePolynomial 3)))
        (δ : Ideal (CoordinatePolynomial 3) → ℕ) (A D B : ℝ),
      0 ≤ A → 0 ≤ D → 1 ≤ B →
      (∀ I ∈ S, I.IsPrime ∧ I.height = 2 ∧ map (Int.castRingHom ℚ) f ∈ I ∧
        0 < δ I ∧ HasAffineCurveDegree I (δ I)) →
      (∀ I ∈ S, (δ I : ℝ) ≤ D * (Real.log B + 1)) →
      (∑ I ∈ S, (δ I : ℝ)) ≤
        A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) →
      (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
        C * ((f.totalDegree : ℝ) ^ 6 + A * (D ^ 2 * (D + 1) + 1)) * B := by
  obtain ⟨Cline, hCline, hline⟩ := surface_degree_one_component_contribution
  obtain ⟨Ccurve, hCcurve, hcurve⟩ := logarithmic_degree_curve_union_bound 1
  let Ccard := 20 * Real.exp (1 / 20 : ℝ)
  have hCcard : 0 < Ccard := by dsimp only [Ccard]; positivity
  let C := Cline + Ccurve + Ccard
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro f hir hd S δ A D B hA hD hB hS hcap hbudget
  let lines := S.filter (fun I => δ I = 1)
  let curves := S.filter (fun I => 2 ≤ δ I)
  have hlineCount := hline f hir (by omega) B (by linarith) lines
    (fun I hI => by
      obtain ⟨hIS, hδ⟩ := mem_filter.mp hI
      obtain ⟨hp, hheight, _, _, hdeg⟩ := hS I hIS
      exact ⟨hp, hheight, hδ ▸ hdeg⟩)
    (fun I hI => (hS I (mem_filter.mp hI).1).2.2.1)
  have hcurveBudget : (∑ I ∈ curves, (δ I : ℝ)) ≤
      A * B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) * (Real.log B + 1) ^ 1 := by
    rw [pow_one]
    exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)).trans hbudget
  have hcurveCount := hcurve curves δ f.totalDegree hd A D B hA hD hB
    (fun I hI => by
      obtain ⟨hIS, hδ⟩ := mem_filter.mp hI
      have hh := hS I hIS
      exact ⟨hh.1, hδ, hh.2.2.2.2⟩)
    (fun I hI => hcap I (mem_filter.mp hI).1) hcurveBudget
  have hcard : (lines.card : ℝ) ≤ ∑ I ∈ S, (δ I : ℝ) := by
    calc
      _ ≤ (S.card : ℝ) := by exact_mod_cast card_le_card (filter_subset (fun I => δ I = 1) S)
      _ = ∑ _I ∈ S, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun I hI => by exact_mod_cast (hS I hI).2.2.2.1)
  have hcardBound : (lines.card : ℝ) ≤ A * Ccard * B := by
    have hh := mul_le_mul_of_nonneg_left (surface_curve_number_weight hd hB) hA
    exact (hcard.trans hbudget).trans (by simpa only [mul_assoc, Ccard] using hh)
  have hsub : (⋃ I ∈ S, idealZeroLocus I) ⊆
      (⋃ I ∈ lines, idealZeroLocus I) ∪ ⋃ I ∈ curves, idealZeroLocus I := by
    intro x hx
    obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hIS, hxI⟩ := Set.mem_iUnion.mp hxI
    by_cases hδ : δ I = 1
    · exact Or.inl (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨hIS, hδ⟩, hxI⟩⟩)
    · have hδ2 : 2 ≤ δ I := by have := (hS I hIS).2.2.2.1; omega
      exact Or.inr (Set.mem_iUnion.mpr ⟨I, Set.mem_iUnion.mpr
        ⟨mem_filter.mpr ⟨hIS, hδ2⟩, hxI⟩⟩)
  have hcount : (count (⋃ I ∈ S, idealZeroLocus I) B : ℝ) ≤
      (count (⋃ I ∈ lines, idealZeroLocus I) B : ℝ) +
        count (⋃ I ∈ curves, idealZeroLocus I) B := by
    exact_mod_cast (count_mono hsub (le_refl B)).trans
      (count_union_le (⋃ I ∈ lines, idealZeroLocus I) (⋃ I ∈ curves, idealZeroLocus I) B)
  have hCl : Cline ≤ C := by dsimp only [C]; linarith
  have hCc : Ccurve ≤ C := by dsimp only [C]; linarith
  have hCn : Ccard ≤ C := by dsimp only [C]; linarith
  have hB0 : 0 ≤ B := by linarith
  have hl := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCl
    (show 0 ≤ (f.totalDegree : ℝ) ^ 6 by positivity)) hB0
  have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCn hA) hB0
  have hc := mul_le_mul_of_nonneg_right hCc
    (show 0 ≤ A * D ^ 2 * (D + 1) * B by positivity)
  nlinarith [hcount, hlineCount, hcurveCount, hcardBound, hl, hn, hc]

end
end CCDN
