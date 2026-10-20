module

public import CCDN.FinIntegerHilbertElimination
public import CCDN.HilbertFullDimension

/-! Constructive bounded linear Noether normalization. The coefficients of
the actual integer linear forms are bounded by n! (d+1)^n. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def integerNormalizationHeight (n d : ℕ) : ℕ := n.factorial * (d + 1) ^ n

lemma integerNormalizationHeight_pos (n d : ℕ) : 0 < integerNormalizationHeight n d := by
  dsimp [integerNormalizationHeight]
  positivity

lemma integerNormalizationHeight_mono (n : ℕ) {d e : ℕ} (h : d ≤ e) :
    integerNormalizationHeight n d ≤ integerNormalizationHeight n e := by
  dsimp [integerNormalizationHeight]
  gcongr

lemma integerNormalizationHeight_step (n d : ℕ) :
    n * integerNormalizationHeight n d * (d + 1) ≤
      integerNormalizationHeight (n + 1) d := by
  dsimp [integerNormalizationHeight]
  rw [Nat.factorial_succ, pow_succ]
  nlinarith [Nat.zero_le (n.factorial * (d + 1) ^ n * (d + 1))]

/-- Actual integer linear normalization of a prime quotient of positive
Hilbert dimension. No chosen projection, equations or normalization is assumed.
The resulting polynomial map is both injective and integral. -/
theorem exists_bounded_integer_normalization (m k : ℕ)
    (I : Ideal (MvPolynomial (Fin (m + 1 + k)) ℚ)) [I.IsPrime] (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (m + 1).factorial) :
    ∃ a : Fin (m + 1) → Fin (m + 1 + k) → ℤ,
      (∀ i j, |a i j| ≤ integerNormalizationHeight (m + 1 + k) d) ∧
      (projectionCoordinateMap I (fun i => integerLinearForm (a i))).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I (fun i => integerLinearForm (a i))) := by
  induction k generalizing d with
  | zero =>
    let a : Fin (m + 1) → Fin (m + 1) → ℤ := fun i j => if j = i then 1 else 0
    have heq : projectionCoordinateMap I (fun i => integerLinearForm (a i)) =
        Ideal.Quotient.mkₐ ℚ I := by
      ext i
      simp [projectionCoordinateMap, a, integerLinearForm_identity]
    have hI0 : I = ⊥ := ideal_eq_bot_of_full_hilbert_dimension I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›) (by simpa only [Fintype.card_fin] using hdim)
    refine ⟨a, ?_, ?_, ?_⟩
    · intro i j
      have hH : (1 : ℤ) ≤ integerNormalizationHeight (m + 1) d := by
        exact_mod_cast Nat.succ_le_of_lt (integerNormalizationHeight_pos (m + 1) d)
      by_cases he : j = i
      · simpa [a, he] using hH
      · simp only [a, ite_eq_right he, abs_zero]
        exact Nat.cast_nonneg _
    · rw [heq]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective ℚ I)
    · rw [heq]
      apply (RingHom.injective_iff_ker_eq_bot _).mpr
      change RingHom.ker ((Ideal.Quotient.mkₐ ℚ I) :
        MvPolynomial (Fin (m + 1)) ℚ →+* MvPolynomial (Fin (m + 1)) ℚ ⧸ I) = ⊥
      rwa [Ideal.Quotient.mkₐ_ker]
  | succ k ih =>
    obtain ⟨c, e, hc, he, hed, hintc, hprime, hdimJ, hdegreeJ⟩ :=
      exists_fin_integer_elimination_step (n := m + 1 + k) (m := m) I d hdim (by omega) hdegree
    let ψ := projectionCoordinateMap I (fun i => integerLinearForm (c i))
    let J := RingHom.ker ψ
    let : J.IsPrime := hprime
    obtain ⟨a, ha, hinta, hinja⟩ := ih J e hdimJ hdegreeJ
    let a' : Fin (m + 1) → Fin (m + 1 + (k + 1)) → ℤ :=
      fun i j => ∑ t, a i t * c t j
    let ψa := projectionCoordinateMap J (fun i => integerLinearForm (a i))
    let φ := Ideal.kerLiftAlg ψ
    have hφ : φ.IsIntegral := hintc.kerLift
    have hcomp := RingHom.IsIntegral.trans ψa.toRingHom φ.toRingHom hinta hφ
    have heq : φ.comp ψa = projectionCoordinateMap I (fun i => integerLinearForm (a' i)) := by
      ext i
      simp only [AlgHom.comp_apply, ψa, projectionCoordinateMap, aeval_X,
        Ideal.Quotient.mkₐ_eq_mk]
      change (Ideal.Quotient.mk I)
        (aeval (fun t => integerLinearForm (c t)) (integerLinearForm (a i))) =
          (Ideal.Quotient.mk I) (integerLinearForm (a' i))
      rw [integerLinearForm_comp]
      rfl
    refine ⟨a', ?_, ?_, ?_⟩
    · intro i j
      have hbound := integerLinearForm_matrix_height (a i) c
        (integerNormalizationHeight (m + 1 + k) e) (d + 1) (ha i)
        (fun i j => by exact_mod_cast hc i j) j
      simp only [Fintype.card_fin] at hbound
      apply hbound.trans
      have hmono := integerNormalizationHeight_mono (m + 1 + k) hed
      have hstep := integerNormalizationHeight_step (m + 1 + k) d
      exact_mod_cast (Nat.mul_le_mul_right (d + 1)
        (Nat.mul_le_mul_left (m + 1 + k) hmono)).trans hstep
    · change (φ.comp ψa).IsIntegral at hcomp
      rwa [heq] at hcomp
    · rw [← heq]
      exact (Ideal.kerLiftAlg_injective ψ).comp hinja

end
end CCDN
