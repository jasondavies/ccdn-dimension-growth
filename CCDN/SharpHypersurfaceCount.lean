module

public import CCDN.HypersurfaceCountError

/-! A sharp coefficient-uniform count for geometrically irreducible affine
hypersurfaces over prime fields, proved by actual plane-section averaging. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- In n+3 ambient coordinates, the leading term is p^(n+2), with an explicit
absolute square-degree square-root error. All section counts are discharged. -/
theorem affine_hypersurface_finite_field_bound_option {n : ℕ}
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Option (Fin (n + 2))) (ZMod p))
    (hf : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f))
    (hsize : 27 * (f.totalDegree : ℝ) ^ 4 < p) :
    (Nat.card {z : Option (Fin (n + 2)) → ZMod p // eval z f = 0} : ℝ) ≤
      (p : ℝ) ^ (n + 2) + 164 * (f.totalDegree : ℝ) ^ 2 * (p : ℝ) ^ (n + 1) * Real.sqrt p := by
  have hir := mvPolynomial_irreducible_of_field_map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f hf
  have hd : 0 < f.totalDegree := by
    by_contra hn
    have hc := totalDegree_eq_zero_iff_eq_C.mp (show f.totalDegree = 0 by omega)
    have h0 : f.coeff 0 ≠ 0 := by
      intro hz
      apply hir.ne_zero
      rw [hc, hz, map_zero]
    apply hir.not_isUnit
    rw [hc]
    exact (isUnit_iff_ne_zero.mpr h0).map C
  have hdR : (1 : ℝ) ≤ f.totalDegree := by exact_mod_cast hd
  have hpN : 27 * f.totalDegree ^ 4 < p := by exact_mod_cast hsize
  have hchar : 2 * f.totalDegree ^ 2 < p := by
    have h2 : 1 ≤ f.totalDegree ^ 2 := by nlinarith
    have h4 : f.totalDegree ^ 2 ≤ f.totalDegree ^ 4 := by nlinarith
    nlinarith
  have hbN := finite_field_bad_plane_parameters_card f hf hd hchar
  have hzN := finite_field_zero_plane_parameters_card f hir.ne_zero
  simp only [Fintype.card_fin, ZMod.card] at hbN hzN
  rw [show 3 * (n + 2 + 1) - 1 = 3 * n + 8 by omega] at hbN
  rw [show 3 * (n + 2) = 3 * n + 6 by omega] at hzN
  have hb : (Nat.card (BadPlaneParameters f) : ℝ) ≤
      2 * (f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 8) := by exact_mod_cast hbN
  have hz : (Nat.card (ZeroPlaneParameters f) : ℝ) ≤
      (f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 6) := by exact_mod_cast hzN
  have hi := plane_sections_incidence_bound p f hsize
  simp only [Fintype.card_option, Fintype.card_fin] at hi
  rw [show 2 * (n + 2 + 1) + 2 = 2 * n + 8 by omega,
    show 3 * (n + 2 + 1) = 3 * n + 9 by omega] at hi
  apply hypersurface_count_of_incidence_bound n hdR hsize
  calc
    _ ≤ (p : ℝ) ^ (3 * n + 9) * (p + 161 * (f.totalDegree : ℝ) ^ 2 * Real.sqrt p) +
        (2 * (f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 8)) * (f.totalDegree * p) +
        ((f.totalDegree : ℝ) ^ 3 * (p : ℝ) ^ (3 * n + 6)) * (p : ℝ) ^ 2 := by
      exact hi.trans (add_le_add
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hb (show 0 ≤ (f.totalDegree : ℝ) * p by positivity)))
        (mul_le_mul_of_nonneg_right hz (show 0 ≤ (p : ℝ) ^ 2 by positivity)))
    _ = _ := by
      rw [show 3 * n + 9 = (3 * n + 8) + 1 by omega, pow_succ,
        show 3 * n + 8 = (3 * n + 6) + 2 by omega, pow_add]
      ring

/-- Renaming coordinates preserves the actual number of affine zeros. -/
lemma polynomial_zero_card_renameEquiv {K σ τ : Type*} [CommRing K]
    (e : σ ≃ τ) (f : MvPolynomial σ K) :
    Nat.card {z : τ → K // eval z (rename e f) = 0} =
      Nat.card {z : σ → K // eval z f = 0} := by
  apply Nat.card_congr
  exact {
    toFun := fun z => ⟨z.val ∘ e, by simpa only [eval_rename] using z.property⟩
    invFun := fun z => ⟨z.val ∘ e.symm, by
      simpa only [eval_rename, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] using z.property⟩
    left_inv := fun z => by apply Subtype.ext; funext i; simp
    right_inv := fun z => by apply Subtype.ext; funext i; simp }

/-- The sharp affine count in the standard Fin-indexed ambient coordinates. -/
theorem affine_hypersurface_finite_field_bound {n : ℕ}
    (p : ℕ) [Fact p.Prime] (f : MvPolynomial (Fin (n + 3)) (ZMod p))
    (hf : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) f))
    (hsize : 27 * (f.totalDegree : ℝ) ^ 4 < p) :
    (Nat.card {z : Fin (n + 3) → ZMod p // eval z f = 0} : ℝ) ≤
      (p : ℝ) ^ (n + 2) + 164 * (f.totalDegree : ℝ) ^ 2 * (p : ℝ) ^ (n + 1) * Real.sqrt p := by
  let e : Fin (n + 3) ≃ Option (Fin (n + 2)) := finSuccEquiv' 0
  let g := rename e f
  have hg : Irreducible (MvPolynomial.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) g) := by
    rw [show g = rename e f from rfl, map_rename]
    exact (MulEquiv.irreducible_iff (f := renameEquiv (AlgebraicClosure (ZMod p)) e)).mpr hf
  have hd : g.totalDegree = f.totalDegree := totalDegree_renameEquiv e f
  have h := affine_hypersurface_finite_field_bound_option p g hg (hd ▸ hsize)
  rw [hd, polynomial_zero_card_renameEquiv] at h
  exact h

end
end CCDN
