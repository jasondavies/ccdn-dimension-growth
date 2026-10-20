module

public import AffineCurveCounting.WeightedPolynomialSubstitution

/-! Weight-preserving substitutions preserve weighted homogeneity. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem weighted_homogeneous_substitution
    {K A σ τ : Type*} [CommRing K] [CommRing A]
    (ψ : K →+* A) (w : σ → ℕ) (v : τ → ℕ)
    (a : σ → MvPolynomial τ A)
    (ha : ∀ i, (a i).IsWeightedHomogeneous v (w i))
    (f : MvPolynomial σ K) (d : ℕ) (hf : f.IsWeightedHomogeneous w d) :
    (eval₂Hom (C.comp ψ) a f).IsWeightedHomogeneous v d := by
  classical
  rw [f.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro e he
  have hh := weighted_substitution_monomial ψ w v a ha e (f.coeff e)
  rwa [hf (mem_support_iff.mp he)] at hh

theorem weighted_homogeneous_rename
    {K σ τ : Type*} [CommRing K]
    (w : σ → ℕ) (v : τ → ℕ) (ρ : σ → τ) (hρ : ∀ i, v (ρ i) = w i)
    (f : MvPolynomial σ K) (d : ℕ) (hf : f.IsWeightedHomogeneous w d) :
    (rename ρ f).IsWeightedHomogeneous v d := by
  have ha (i : σ) : (X (ρ i) : MvPolynomial τ K).IsWeightedHomogeneous v (w i) := by
    rw [← hρ i]
    exact isWeightedHomogeneous_X K v (ρ i)
  have hh := weighted_homogeneous_substitution (RingHom.id K) w v
    (fun i => X (ρ i)) ha f d hf
  have he : (rename (R := K) ρ).toRingHom =
      eval₂Hom (C.comp (RingHom.id K)) (fun i => X (ρ i)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      simp
  have hef := RingHom.congr_fun he f
  change rename ρ f = eval₂Hom (C.comp (RingHom.id K)) (fun i => X (ρ i)) f at hef
  rw [hef]
  exact hh

end
end AffineCurveCounting
