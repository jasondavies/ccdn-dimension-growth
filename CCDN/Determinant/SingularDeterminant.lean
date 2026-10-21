module

public import CCDN.Determinant.PlaneMultiplicitySmooth
public import CCDN.Analysis.PrimeSums
import all ArithmeticHeights.BombieriVaaler

/-! The local exponent at a possibly singular plane reduction, bounded by
the residue-point count plus the singular correction. -/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real MvPolynomial

lemma irreducible_mvPolynomial_totalDegree_pos {K σ : Type*} [Field K]
    {f : MvPolynomial σ K} (hf : Irreducible f) : 0 < f.totalDegree := by
  by_contra hn
  have hd : f.totalDegree = 0 := by omega
  have he : f = C (f.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : f.coeff 0 ≠ 0 := by
    intro hc
    apply hf.ne_zero
    rw [he, hc, map_zero]
  apply hf.not_isUnit
  rw [he]
  exact (isUnit_iff_ne_zero.mpr hc).map C

/-- The local exponent can be bounded using the reduced point count
and the proved degree-dependent singular correction. -/
theorem singular_reduction_minorGcd_card_bound {s N p : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 2) ℤ) (g : Fin N → MvPolynomial (Fin 2) ℤ)
    (z : Fin s → Fin 2 → ℤ) (hz : ∀ i, eval (z i) f = 0)
    (hf : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hchar : f.totalDegree < p) :
    let m : ℕ := Nat.card (PlaneResidue f p) + f.totalDegree ^ 2 * (f.totalDegree - 1)
    0 < m ∧ ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * m) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i k => eval (z i) (g k)) := by
  dsimp only
  obtain ⟨hM, e, _, he, hdiv⟩ := singular_reduction_minorGcd hs f g z hf.ne_zero hz
  have hbound := planeTotalMultiplicity_le_card_add_correction f hf
    (irreducible_mvPolynomial_totalDegree_pos hf) hchar
  rw [← Nat.card_eq_fintype_card] at hbound
  refine ⟨hM.trans_le hbound, e, ?_, hdiv⟩
  apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hbound) (by norm_num)

end
end CCDN
