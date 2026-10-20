module

public import AffineCurveCounting.AffineChartGlobalDeterminant
public import AffineCurveCounting.HypersurfaceBadPrimeComparison

/-! The coefficient obstruction with a chosen affine chart. The displayed
prime condition is used only to invoke the proved chart-local divisor; no
finite-field counting estimate is assumed. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- The normalized comparison retains the charge of the supplied finite prime
set. Its hypotheses are genuine good affine reductions and chart units. -/
theorem affine_chart_no_auxiliary_comparison
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n d M t : ℕ}
    (order : MonomialOrder (Fin (n + 3))) (f : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (hdM : d ≤ M)
    (hir : Irreducible (map (Int.castRingHom K) f))
    (z : Fin t → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (bad : Finset ℕ)
    (hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad → 27 * (d : ℝ) ^ 4 < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) f))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0))
    {B : ℝ} (hB : 1 ≤ B) (hbox : ∀ i j, |(z i j : ℝ)| ≤ B)
    (hrel : ∀ g : MvPolynomial (Fin (n + 3)) ℤ, g.IsHomogeneous M →
      (∀ i, eval (z i) g = 0) → f ∣ g) :
    ∃ s : ℕ, 0 < s ∧
      s + (n + 2 + (M - d)).choose (M - d) = (n + 2 + M).choose M ∧
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) * (s : ℝ) ^ (1 / (n + 1 : ℝ)) /
          ((n + 2 : ℝ) * M) *
        (Real.log s - (n + 1 : ℝ) * (4 * Real.log d + (∑ p ∈ bad, Real.log p / p)) -
          hypersurfaceBadPrimeNormalizedError n) ≤
        Real.log B - ((n + 2 + (M - d)).choose (M - d) : ℝ) / ((M : ℝ) * s) *
          Real.log |((order.leadingCoeff f : ℤ) : ℝ)| := by
  have hf0 : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  obtain ⟨s, a, _, _, hr, hi, hupper⟩ :=
    homogeneous_no_auxiliary_box_comparison order f hf hf0 hdM z hz hB hbox hrel
  have hs := hypersurface_homogeneous_rank_pos hd hdM hr
  let F := fun j => (monomial (homogeneousMonomials (n + 2) M j) 1 : MvPolynomial (Fin (n + 3)) ℤ)
  have hF : ∀ j, (F j).IsHomogeneous M := fun j =>
    isHomogeneous_monomial _ (homogeneousMonomials_degree (n + 2) M j)
  have he : (Matrix.of fun i j => eval ((z ∘ a) i) (F j)) =
      evaluationMatrix (homogeneousMonomials (n + 2) M) (z ∘ a) := by
    ext i j
    simp [F, evaluationMatrix, eval_monomial]
  have hi' : LinearIndependent ℚ
      ((Matrix.of fun i j => eval ((z ∘ a) i) (F j)).map ((↑) : ℤ → ℚ)).row := by
    rw [he]
    exact hi
  have hlower := affine_chart_determinant_log_lower_at_rank hs f hf hd F hF
    (z ∘ a) (fun i => hprim (a i)) (fun i => hz (a i)) hi' bad (by
      intro p hp hpnot hcut
      obtain ⟨hirp, hunit⟩ := hgood p (Finset.mem_sdiff.mp hpnot).2 hcut
      exact ⟨hirp, fun i => hunit (a i)⟩)
  rw [he] at hlower
  have hc := hlower.trans hupper
  refine ⟨s, hs, hr, ?_⟩
  have hnN : n + 1 + 1 = n + 2 := by omega
  have hnR : (n : ℝ) + 1 + 1 = n + 2 := by ring
  have hh := hypersurface_rank_comparison_normalized (r := n + 1) (by omega) hd hdM hr
    B |((order.leadingCoeff f : ℤ) : ℝ)| (Real.exp (∑ p ∈ bad, Real.log p / p))
    (hypersurfaceDeterminantError n)
    (by simpa only [hnN, Nat.cast_add, Nat.cast_one, hnR, Real.log_exp] using hc)
  simpa only [hypersurfaceBadPrimeNormalizedError, hnN, Nat.cast_add, Nat.cast_one, hnR,
    Real.log_exp] using hh

end
end AffineCurveCounting
