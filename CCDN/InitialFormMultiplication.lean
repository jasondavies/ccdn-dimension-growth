module

public import CCDN.SingularTangent

/-! The first nonzero homogeneous form behaves multiplicatively. Consequently
multiplication by an equation of order μ cancels μ powers of the origin
ideal. These are statements about the polynomial ring and ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K σ : Type*} [CommRing K]

lemma homogeneousComponent_eq_zero_of_mem_origin_power
    {f : MvPolynomial σ K} {k N : ℕ}
    (hf : f ∈ idealOfVars σ K ^ N) (hk : k < N) :
    homogeneousComponent k f = 0 := by
  classical
  rw [mem_pow_idealOfVars_iff'] at hf
  ext e
  simp only [coeff_homogeneousComponent]
  split_ifs with he
  · exact hf e (by omega)
  · rfl

lemma first_form_product_congruence
    {f g : MvPolynomial σ K} {μ ν : ℕ}
    (hf : f ∈ idealOfVars σ K ^ μ) (hg : g ∈ idealOfVars σ K ^ ν) :
    f * g - homogeneousComponent μ f * homogeneousComponent ν g ∈
      idealOfVars σ K ^ (μ + ν + 1) := by
  have h₁ := Ideal.mul_mem_mul (sub_homogeneousComponent_mem_origin_power hf) hg
  have h₂ := Ideal.mul_mem_mul
    (homogeneous_mem_origin_power (homogeneousComponent_isHomogeneous μ f))
    (sub_homogeneousComponent_mem_origin_power hg)
  rw [← pow_add, show μ + 1 + ν = μ + ν + 1 by omega] at h₁
  rw [← pow_add, show μ + (ν + 1) = μ + ν + 1 by omega] at h₂
  convert (idealOfVars σ K ^ (μ + ν + 1)).add_mem h₁ h₂ using 1
  ring

lemma first_homogeneousComponent_mul
    {f g : MvPolynomial σ K} {μ ν : ℕ}
    (hf : f ∈ idealOfVars σ K ^ μ) (hg : g ∈ idealOfVars σ K ^ ν) :
    homogeneousComponent (μ + ν) (f * g) =
      homogeneousComponent μ f * homogeneousComponent ν g := by
  have hzero := homogeneousComponent_eq_zero_of_mem_origin_power
    (first_form_product_congruence hf hg) (Nat.lt_succ_self (μ + ν))
  rw [map_sub, homogeneousComponent_eq_self
    ((homogeneousComponent_isHomogeneous μ f).mul
      (homogeneousComponent_isHomogeneous ν g))] at hzero
  exact sub_eq_zero.mp hzero

/-- Multiplication by a polynomial whose first nonzero form has degree μ
raises the origin-adic order by exactly μ. -/
theorem origin_power_cancel_initial_form [IsDomain K]
    {f g : MvPolynomial σ K} {μ N : ℕ}
    (hf : f ∈ idealOfVars σ K ^ μ)
    (hμ : homogeneousComponent μ f ≠ 0)
    (hfg : f * g ∈ idealOfVars σ K ^ N) :
    g ∈ idealOfVars σ K ^ (N - μ) := by
  have hstep : ∀ ν ≤ N - μ, g ∈ idealOfVars σ K ^ ν := by
    intro ν
    induction ν with
    | zero => simp
    | succ ν ih =>
      intro hν
      have hg := ih (by omega)
      have hz := homogeneousComponent_eq_zero_of_mem_origin_power hfg
        (show μ + ν < N by omega)
      rw [first_homogeneousComponent_mul hf hg] at hz
      have hνzero := (mul_eq_zero.mp hz).resolve_left hμ
      simpa only [hνzero, sub_zero] using sub_homogeneousComponent_mem_origin_power hg
  exact hstep (N - μ) le_rfl

end
end CCDN
