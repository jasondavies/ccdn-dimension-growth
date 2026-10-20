module

public import AffineCurveCounting.HomogeneousProjectionNoBasePoint
public import AffineCurveCounting.BalancedParameterFiniteness
public import AffineCurveCounting.HomogeneousEvaluation
public import Mathlib.FieldTheory.AlgebraicClosure

/-! Actual homogeneous finite parameters give certificates for every
monomial in one positive homogeneous degree. Extracting homogeneous
components makes all parameter multipliers have the preceding degree. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem integral_homogeneous_parameters_full_degree
    {K τ : Type*} [Field K] [Fintype τ] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ f ∈ I, ∀ k, homogeneousComponent k f ∈ I)
    (a : τ → MvPolynomial (Fin (n + 1)) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hint : (projectionCoordinateMap I a).IsIntegral) :
    ∃ D : ℕ, 0 < D ∧ ∀ f : MvPolynomial (Fin (n + 1)) K,
      f.IsHomogeneous D → f ∈ I ⊔ Ideal.span (Set.range a) := by
  classical
  let H := I ⊔ Ideal.span (Set.range a)
  have hzero : ∀ x ∈ MvPolynomial.zeroLocus (AlgebraicClosure K) H, x = 0 := by
    intro x hx
    exact homogeneous_integral_projection_zero_fiber I hI a ha hint x
      (fun f hf => hx f (Ideal.mem_sup_left hf))
      (fun i => hx (a i) (Ideal.mem_sup_right (Ideal.subset_span ⟨i,rfl⟩)))
  have hpow (j : Fin (n + 1)) : ∃ N : ℕ, X j ^ N ∈ H := by
    have hh : X j ∈ vanishingIdeal K (MvPolynomial.zeroLocus (AlgebraicClosure K) H) := by
      intro x hx
      rw [hzero x hx]
      simp
    rw [vanishingIdeal_zeroLocus_eq_radical] at hh
    exact hh
  choose N hN using hpow
  let M := Finset.univ.sup N + 1
  have hM : 0 < M := by dsimp [M]; omega
  have hpower (j : Fin (n + 1)) : X j ^ M ∈ H := by
    have hj : N j ≤ M := (Finset.le_sup (f := N) (Finset.mem_univ j)).trans (Nat.le_succ _)
    have hh := H.mul_mem_left (X j ^ (M - N j)) (hN j)
    simpa only [← pow_add, Nat.sub_add_cancel hj] using hh
  let D := (n + 1) * M
  have hD : 0 < D := Nat.mul_pos (by omega) hM
  refine ⟨D,hD,?_⟩
  intro f hf
  rw [← f.support_sum_monomial_coeff]
  apply H.sum_mem
  intro e he
  have heD : e.degree = D := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp he)
  obtain ⟨j,hj⟩ := large_exponent_of_degree e M (by omega)
    (by simp only [Fintype.card_fin, heD]; exact le_rfl)
  let v := e - Finsupp.single j M
  have hve : v + Finsupp.single j M = e := tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)
  have hh := H.mul_mem_left (monomial v (f.coeff e)) (hpower j)
  simpa only [X_pow_eq_monomial, monomial_mul_monomial, mul_one, hve] using hh

theorem homogeneous_parameter_certificate
    {K τ : Type*} [Field K] [Fintype τ] {n D : ℕ} (hD : 0 < D)
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : ∀ f ∈ I, ∀ k, homogeneousComponent k f ∈ I)
    (a : τ → MvPolynomial (Fin (n + 1)) K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (f : MvPolynomial (Fin (n + 1)) K) (hf : f.IsHomogeneous D)
    (hmem : f ∈ I ⊔ Ideal.span (Set.range a)) :
    ∃ g : MvPolynomial (Fin (n + 1)) K, ∃ s : τ → MvPolynomial (Fin (n + 1)) K,
      g ∈ I ∧ g.IsHomogeneous D ∧ (∀ i, (s i).IsHomogeneous (D - 1)) ∧
      g + ∑ i, a i * s i = f := by
  classical
  obtain ⟨g,hg,t,ht,he⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨s,hs⟩ := Ideal.mem_span_range_iff_exists_fun.mp ht
  have hs' : ∑ i, a i * s i = t := by simpa only [mul_comm] using hs
  have heq : g + ∑ i, a i * s i = f := by rwa [hs']
  have hh := congrArg (homogeneousComponent D) heq
  rw [map_add, map_sum, homogeneousComponent_eq_self hf] at hh
  have hmul (i : τ) : homogeneousComponent D (a i * s i) =
      a i * homogeneousComponent (D - 1) (s i) := by
    conv_lhs => rw [show D = 1 + (D - 1) by omega]
    exact homogeneousComponent_mul_homogeneous_left (ha i) (s i) (D - 1)
  simp only [hmul] at hh
  exact ⟨homogeneousComponent D g, fun i => homogeneousComponent (D - 1) (s i),
    hI g hg D, homogeneousComponent_isHomogeneous _ _,
    fun _ => homogeneousComponent_isHomogeneous _ _, hh⟩

end
end AffineCurveCounting
