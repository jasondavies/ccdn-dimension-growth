module

public import CCDN.ProjectiveLinearCountTransfer
public import CCDN.BirationalProjectionHeight
public import CCDN.HypersurfaceDimensionGrowth

/-! The quantitative counting step for the constructed projection. The
height and finite-fiber losses remain polynomial in the original degree. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def projectiveProjectionDegreeExponent (m k : ℕ) : ℕ :=
  18 + 3 * m + (m + k + 2) + 2 * (m + k + 2) * (m + 1)

theorem projective_projection_dimension_growth (m k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (I : Ideal (MvPolynomial (Fin (m + k + 2)) ℚ)) (d : ℕ), 5 ≤ d →
      ∀ b : Fin (m + 3) → Fin (m + k + 2) → ℤ,
      (∀ i j, |b i j| ≤ integerBirationalProjectionHeight (m + k + 2) d) →
      ∀ f : MvPolynomial (Fin (m + 3)) ℚ,
      Irreducible f → f.IsHomogeneous d → f.totalDegree = d →
      aeval (fun i => integerLinearForm (b i)) f ∈ I →
      (∀ z : Fin (m + 3) → ℚ, ∀ s : Finset (Fin (m + k + 2) → ℚ),
        (∀ x ∈ s, ∀ g ∈ I, eval x g = 0) →
        (∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) →
        s.card ≤ d ^ (m + k + 2)) →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ projectiveProjectionDegreeExponent m k * B ^ (m + 1) := by
  obtain ⟨C, hC, hcount⟩ := projective_hypersurface_dimension_growth m
  let N := m + k + 2
  let T : ℝ := N * birationalProjectionHeightConstant N
  have hN : 1 ≤ N := by dsimp [N]; omega
  have hT : 1 ≤ T := by
    have hpos := birationalProjectionHeightConstant_pos N
    have hh : 1 ≤ N * birationalProjectionHeightConstant N := by
      exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) hpos)
    dsimp only [T]
    exact_mod_cast hh
  refine ⟨C * T ^ (m + 1), by positivity, ?_⟩
  intro I d hd b hb f hf hfhom hfdeg hrel hfiber B hB
  let H : ℝ := birationalProjectionHeightConstant N * (d : ℝ) ^ (2 * N)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hH : 1 ≤ H := by
    have hconst : (1 : ℝ) ≤ birationalProjectionHeightConstant N := by
      exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos N)
    exact one_le_mul_of_one_le_of_one_le hconst (one_le_pow₀ hd1)
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight N d := by
      exact_mod_cast hb i j
    apply hh.trans
    dsimp only [H]
    exact_mod_cast integerBirationalProjectionHeight_le N d (by omega)
  have hbound := projective_integer_linear_count_transfer
    (n := m + k + 1) (m := m + 2) I b f (by rwa [hfdeg])
    hrel (d ^ N) hfiber H B (by linarith) hbH
  have hheight : 1 ≤ (N : ℝ) * H * B := by
    exact one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hN) hH) hB
  have htarget := hcount f (by rwa [hfdeg]) hf (by omega) ((N : ℝ) * H * B) hheight
  rw [hfdeg] at htarget
  have hnon : (0 : ℝ) ≤ (d : ℝ) ^ N := by positivity
  have hh : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      (d : ℝ) ^ N * (C * (d : ℝ) ^ (18 + 3 * m) *
        ((N : ℝ) * H * B) ^ (m + 1)) := by
    apply (show (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      (d : ℝ) ^ N * projectiveCount (projectiveZeroLocus f) ((N : ℝ) * H * B) by
        exact_mod_cast hbound).trans
    exact mul_le_mul_of_nonneg_left htarget hnon
  convert hh using 1
  dsimp only [projectiveProjectionDegreeExponent, H, T, N]
  simp only [pow_add, pow_mul, mul_pow]
  ring

end
end CCDN
