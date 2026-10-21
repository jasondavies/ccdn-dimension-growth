/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
import CCDN.Plane.Bezout
import CCDN.Algebra.CharZeroOrGT
import CCDN.ForMathlib.MvPolynomialDerivative

/-! The singular-point correction in the finite-field curve estimate. The
remaining estimate for all nonsingular rational points is not asserted here. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem pderiv_totalDegree_le {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) (i : σ) : (pderiv i f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply Finset.sup_le
  intro m hm
  have hcoeff : f.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have h := mem_support_iff.mp hm
    rw [coeff_pderiv] at h
    exact left_ne_zero_of_mul h
  have hd := le_totalDegree (mem_support_iff.mpr hcoeff)
  have he : (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1 := by
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  rw [he] at hd
  omega

/-- Distinct singular points of an irreducible plane equation of degree `d`
number at most `d(d-1)`, whenever the degree is smaller than the characteristic. -/
theorem plane_singular_points_card_le {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    {p : ℕ} [CharP K p] (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (hpos : 0 < f.totalDegree) (hchar : f.totalDegree < p)
    (z : ι → Fin 2 → K) (hz : Function.Injective z)
    (hzf : ∀ i, eval (z i) f = 0)
    (hzsing : ∀ i j, eval (z i) (pderiv j f) = 0) :
    Fintype.card ι ≤ f.totalDegree * (f.totalDegree - 1) := by
  obtain ⟨j, hj⟩ := exists_pderiv_ne_zero hpos (CharZeroOrGT.of_charP hchar)
  have hdeg := pderiv_totalDegree_le f j
  have hnd : ¬ f ∣ pderiv j f := by
    intro hd
    obtain ⟨q, he⟩ := hd
    have hq : q ≠ 0 := by intro hq; simp [hq] at he; exact hj he
    have htotal := totalDegree_mul_of_isDomain hf.ne_zero hq
    rw [← he] at htotal
    omega
  exact (plane_common_zeros_card_le f (pderiv j f) hf hnd z hz hzf
    (fun i => hzsing i j)).trans (Nat.mul_le_mul_left _ hdeg)

end
end CCDN
