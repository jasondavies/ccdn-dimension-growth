module

public import CCDN.HomogeneousParameterPowers
public import CCDN.CoordinatePowerGeneration
public import CCDN.LinearProjectionFiltration
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-! Balanced coordinate-power reductions give an actual finite module
over the polynomial algebra of the parameters, hence an integral projection. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem integral_projection_of_balanced_power_reductions
    {K σ τ : Type*} [Field K] [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial σ K)) (a : τ → MvPolynomial σ K)
    (N : ℕ) (hN : 0 < N)
    (hpow : ∀ j : σ, ∃ s : τ → MvPolynomial σ K,
      (∀ i, (s i).totalDegree ≤ N - 1) ∧
      (Ideal.Quotient.mk I) (X j ^ N) =
        ∑ i, (Ideal.Quotient.mk I) (a i) * (Ideal.Quotient.mk I) (s i)) :
    (projectionCoordinateMap I a).IsIntegral := by
  classical
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let ψ : R →ₐ[K] A := projectionCoordinateMap I a
  let hAlg : Algebra R A := ψ.toRingHom.toAlgebra
  let : SMul R A := hAlg.toSMul
  let : Algebra R A := hAlg
  let : Module R A := Algebra.toModule
  let : IsScalarTower K R A := IsScalarTower.of_algHom ψ
  let q := Ideal.Quotient.mk I
  let D := Fintype.card σ * N
  let V := filteredCoordinateSpace I D
  let b := Module.finBasis K V
  let W : Submodule R A := Submodule.span R (Set.range (fun i => (b i).val))
  have hlow (f : MvPolynomial σ K) (hf : f.totalDegree ≤ D) : q f ∈ W := by
    let x : V := ⟨q f,⟨f,(mem_restrictTotalDegree _ _ _).mpr hf,rfl⟩⟩
    have he : q f = ∑ i, b.repr x i • (b i).val := by
      simpa only [Submodule.coe_sum,Submodule.coe_smul] using
        (congrArg Subtype.val (b.sum_repr x)).symm
    rw [he]
    apply W.sum_mem
    intro i _
    exact (W.restrictScalars K).smul_mem _ (Submodule.subset_span ⟨i,rfl⟩)
  have hdeg (k : ℕ) : ∀ f : MvPolynomial σ K, f.totalDegree ≤ k → q f ∈ W := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro f hf
      rw [← f.support_sum_monomial_coeff,map_sum]
      apply W.sum_mem
      intro e he
      have hed : e.degree ≤ k := (le_totalDegree he).trans hf
      by_cases hsmall : e.degree ≤ D
      · exact hlow _ ((totalDegree_monomial_le e _).trans hsmall)
      obtain ⟨j,hj⟩ := large_exponent_of_degree e N (by omega) (by dsimp [D] at hsmall; omega)
      obtain ⟨s,hs,hrel⟩ := hpow j
      let u := e - Finsupp.single j N
      have hu : u + Finsupp.single j N = e :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)
      have hud : u.degree + N = e.degree := by
        simpa only [map_add,Finsupp.degree_single] using congrArg Finsupp.degree hu
      have hm : monomial e (f.coeff e) = monomial u (f.coeff e) * X j ^ N := by
        rw [X_pow_eq_monomial,monomial_mul_monomial,mul_one,hu]
      have hred (i : τ) : (monomial u (f.coeff e) * s i).totalDegree < k := by
        have hb := totalDegree_mul (monomial u (f.coeff e)) (s i)
        have hc := totalDegree_monomial_le u (f.coeff e)
        change (monomial u (f.coeff e)).totalDegree ≤ u.degree at hc
        have hsi := hs i
        omega
      rw [hm,map_mul]
      change q (monomial u (f.coeff e)) * (Ideal.Quotient.mk I) (X j ^ N) ∈ W
      rw [hrel,Finset.mul_sum]
      apply W.sum_mem
      intro i _
      have heq : q (monomial u (f.coeff e)) *
          ((Ideal.Quotient.mk I) (a i) * (Ideal.Quotient.mk I) (s i)) =
          (X i : R) • q (monomial u (f.coeff e) * s i) := by
        change q (monomial u (f.coeff e)) * (q (a i) * q (s i)) =
          ψ (X i) * q (monomial u (f.coeff e) * s i)
        have hψX : ψ (X i) = q (a i) := by
          change (Ideal.Quotient.mk I) ((aeval a) (X i : MvPolynomial τ K)) = _
          rw [aeval_X]
        rw [hψX,map_mul]
        ring
      rw [heq]
      exact W.smul_mem _ (ih _ (hred i) _ le_rfl)
  have htop : W = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective x
    exact hdeg f.totalDegree f le_rfl
  let : Module.Finite R A := Module.Finite.of_fg_top (by
    rw [← htop]
    exact Submodule.fg_span (Set.finite_range _))
  exact fun x => IsIntegral.of_finite R x

theorem integral_projection_of_homogeneous_origin_fiber
    {K L σ τ : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    [Fintype σ] [Fintype τ]
    (I : Ideal (MvPolynomial σ K))
    (hI : ∀ f ∈ I, ∀ M, homogeneousComponent M f ∈ I)
    (a : τ → MvPolynomial σ K) (ha : ∀ i, (a i).IsHomogeneous 1)
    (hzero : ∀ z ∈ MvPolynomial.zeroLocus L (I ⊔ Ideal.span (Set.range a)), z = 0) :
    (projectionCoordinateMap I a).IsIntegral := by
  obtain ⟨N,hN,hpow⟩ := exists_homogeneous_parameter_power_reductions I hI a ha hzero
  exact integral_projection_of_balanced_power_reductions I a N hN hpow

end
end CCDN
