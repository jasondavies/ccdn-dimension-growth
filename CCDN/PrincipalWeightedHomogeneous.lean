module

public import CCDN.ChowIncidenceGrading
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! A generator of a separately homogeneous principal ideal is itself
separately homogeneous. The proof constructs its degree from a nonzero term. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem principal_weighted_homogeneous_of_components
    {K σ : Type*} [Field K] (w : σ → ℕ) (f : MvPolynomial σ K) (hf : f ≠ 0)
    (hc : ∀ M, f ∣ weightedHomogeneousComponent w M f) :
    ∃ M, f.IsWeightedHomogeneous w M := by
  classical
  obtain ⟨e,he⟩ := exists_coeff_ne_zero hf
  let M := Finsupp.weight w e
  let G := weightedHomogeneousComponent w M f
  have hGe : G.coeff e = f.coeff e := by simp [G,M,coeff_weightedHomogeneousComponent]
  have hG : G ≠ 0 := by
    intro hz
    have hh : G.coeff e = 0 := by rw [hz]; rfl
    exact he (hGe.symm.trans hh)
  obtain ⟨g,hg⟩ := hc M
  have hg0 : g ≠ 0 := by
    intro hz
    exact hG (by simpa only [hz,mul_zero] using hg)
  have hdegree : G.totalDegree ≤ f.totalDegree := by
    apply totalDegree_le_of_support_subset
    rw [support_weightedHomogeneousComponent]
    exact Finset.filter_subset _ _
  have hdeg : g.totalDegree = 0 := by
    change (weightedHomogeneousComponent w M f).totalDegree ≤ _ at hdegree
    rw [hg,totalDegree_mul_of_isDomain hf hg0] at hdegree
    omega
  have hgC : g = C (g.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hcoeff : g.coeff 0 ≠ 0 := by
    intro hz
    exact hg0 (hgC.trans (by rw [hz,map_zero]))
  refine ⟨M,?_⟩
  intro k hk
  apply weightedHomogeneousComponent_isWeightedHomogeneous (w := w) M f
  rw [hg,hgC,mul_comm,coeff_C_mul]
  exact mul_ne_zero hcoeff hk

theorem chow_incidence_generator_multihomogeneous
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (F : MvPolynomial (Fin r × Fin (n + 1)) K) (hF : F ≠ 0)
    (hgen : chowIncidenceIdeal r I = Ideal.span {F}) :
    ∃ δ : Fin r → ℕ, ∀ i, F.IsWeightedHomogeneous (chowRowWeight i) (δ i) := by
  have hm : F ∈ chowIncidenceIdeal r I := by
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton F)
  have hex (i : Fin r) : ∃ M, F.IsWeightedHomogeneous (chowRowWeight i) M := by
    apply principal_weighted_homogeneous_of_components _ F hF
    intro M
    have h := chowIncidenceIdeal_multihomogeneous I F hm i M
    rw [hgen,Ideal.mem_span_singleton] at h
    exact h
  exact ⟨fun i => (hex i).choose,fun i => (hex i).choose_spec⟩

end
end CCDN
