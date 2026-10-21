module

public import CCDN.Height.FiniteFieldSectionCount
public import CCDN.Determinant.PlaneMultiplicitySmooth
/-! The singular points of an irreducible hypersurface satisfy a
coefficient-uniform codimension-two finite-field bound. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- A nonzero partial derivative cuts the irreducible hypersurface
properly. Fixed-degree finite-field interpolation bounds all its singular points. -/
theorem hypersurface_singular_points_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {n p : ℕ} [Fact p.Prime] (f : MvPolynomial (Fin (n + 2)) (ZMod p))
    (hf : Irreducible f) (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin (n + 2) → ZMod p) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0) (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ (n + 4) ^ n * f.totalDegree * (f.totalDegree - 1) * p ^ n := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero_of_degree_lt_char (p := p) f hpos hchar
  have hdeg := pderiv_totalDegree_le f j
  have hnd : ¬ f ∣ pderiv j f := by
    intro hd
    obtain ⟨q, he⟩ := hd
    have hq : q ≠ 0 := by intro hq; simp [hq] at he; exact hj he
    have htotal := totalDegree_mul_of_isDomain hf.ne_zero hq
    rw [← he] at htotal
    omega
  have hdegrees : f.totalDegree + (pderiv j f).totalDegree ≤
      2 * (Fintype.card (ZMod p) - 1) := by
    rw [ZMod.card]
    omega
  have h := finite_field_common_zeros_card_le f (pderiv j f) hf.prime hnd hdegrees
    z hz hzf (fun i => hzsing i j)
  rw [ZMod.card] at h
  exact h.trans (Nat.mul_le_mul_right (p ^ n)
    (Nat.mul_le_mul_left ((n + 4) ^ n * f.totalDegree) hdeg))

end
end CCDN
