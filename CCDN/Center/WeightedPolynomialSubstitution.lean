module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.MvPolynomial.CommRing

/-! Substitution respecting individual variable weights commutes with
weighted homogeneous components. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma weighted_substitution_monomial {K A σ τ : Type*} [CommRing K] [CommRing A]
    (ψ : K →+* A) (w : σ → ℕ) (v : τ → ℕ)
    (a : σ → MvPolynomial τ A) (ha : ∀ i, (a i).IsWeightedHomogeneous v (w i))
    (e : σ →₀ ℕ) (c : K) :
    (eval₂Hom (C.comp ψ) a (monomial e c)).IsWeightedHomogeneous v (Finsupp.weight w e) := by
  classical
  rw [coe_eval₂Hom,eval₂_monomial]
  have hh := IsWeightedHomogeneous.prod e.support (fun i => (a i) ^ e i)
    (fun i => e i • w i) (fun i _ => (ha i).pow (e i))
  simpa only [RingHom.comp_apply,Finsupp.prod,Finsupp.weight_apply,Finsupp.sum]
    using hh.C_mul (ψ c)

theorem weighted_component_substitution {K A σ τ : Type*} [CommRing K] [CommRing A]
    (ψ : K →+* A) (w : σ → ℕ) (v : τ → ℕ)
    (a : σ → MvPolynomial τ A) (ha : ∀ i, (a i).IsWeightedHomogeneous v (w i))
    (f : MvPolynomial σ K) (M : ℕ) :
    eval₂Hom (C.comp ψ) a (weightedHomogeneousComponent w M f) =
      weightedHomogeneousComponent v M (eval₂Hom (C.comp ψ) a f) := by
  classical
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial w e (f.coeff e) rfl),
    weightedHomogeneousComponent_of_mem (weighted_substitution_monomial ψ w v a ha e (f.coeff e))]
  split_ifs <;> simp only [map_zero]

end
end CCDN
