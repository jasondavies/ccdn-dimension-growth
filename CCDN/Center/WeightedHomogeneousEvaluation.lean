/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Center.WeightedPolynomialSubstitution
/-! Weighted homogeneity under polynomial evaluation over the same field. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem weighted_homogeneous_aeval
    {K σ τ : Type*} [Field K] (w : σ → ℕ) (v : τ → ℕ)
    (a : σ → MvPolynomial τ K)
    (ha : ∀ i, (a i).IsWeightedHomogeneous v (w i))
    (f : MvPolynomial σ K) (d : ℕ) (hf : f.IsWeightedHomogeneous w d) :
    (aeval a f).IsWeightedHomogeneous v d := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  rw [aeval_monomial, algebraMap_eq]
  have hh := IsWeightedHomogeneous.prod e.support (fun i => (a i) ^ e i)
    (fun i => e i • w i) (fun i _ => (ha i).pow (e i))
  have hw := hf (mem_support_iff.mp he)
  change ∑ i ∈ e.support, e i • w i = d at hw
  simpa only [Finsupp.prod, hw] using hh.C_mul (f.coeff e)

end
end CCDN
