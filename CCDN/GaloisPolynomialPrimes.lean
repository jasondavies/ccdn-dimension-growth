module

public import CCDN.FilteredPrimeDecomposition
public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! Coefficient Galois actions and conjugacy of polynomial primes.
The invariant-ring assertion is proved coefficient by coefficient. Going
down identifies the contractions of minimal primes of an extended ideal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
open scoped Pointwise

variable (k K σ : Type*) [Field k] [Field K] [Algebra k K]

lemma coefficientGaloisPolynomial_smul (γ : Gal(K/k)) (f : MvPolynomial σ K) :
    γ • f = map γ.toRingHom f := by
  ext m
  simp only [coeff_smul, coeff_map]
  rfl

instance coefficientGaloisPolynomialAction :
    MulSemiringAction Gal(K/k) (MvPolynomial σ K) where
  smul γ f := γ • f
  one_smul f := by
    ext m
    simp only [one_smul]
  mul_smul γ δ f := by
    ext m
    simp only [coeff_smul, mul_smul]
  smul_zero γ := smul_zero _
  smul_add γ f g := smul_add _ _ _
  smul_one γ := by rw [coefficientGaloisPolynomial_smul]; exact map_one _
  smul_mul γ f g := by
    simp only [coefficientGaloisPolynomial_smul, map_mul]

attribute [local instance] MvPolynomial.algebraMvPolynomial

lemma coefficientGaloisPolynomial_fixed_base (γ : Gal(K/k)) (f : MvPolynomial σ k) :
    γ • (algebraMap (MvPolynomial σ k) (MvPolynomial σ K) f) =
      algebraMap (MvPolynomial σ k) (MvPolynomial σ K) f := by
  rw [coefficientGaloisPolynomial_smul]
  change map γ.toRingHom (map (algebraMap k K) f) = map (algebraMap k K) f
  ext m
  simp only [coeff_map]
  exact γ.commutes (f.coeff m)

instance coefficientGaloisPolynomial_smulCommClass :
    SMulCommClass Gal(K/k) (MvPolynomial σ k) (MvPolynomial σ K) where
  smul_comm γ f g := by
    simp only [Algebra.smul_def, MulSemiringAction.smul_mul,
      coefficientGaloisPolynomial_fixed_base]

instance coefficientGaloisPolynomial_invariant [IsGalois k K] :
    Algebra.IsInvariant (MvPolynomial σ k) (MvPolynomial σ K) Gal(K/k) where
  isInvariant f hf := by
    change f ∈ Set.range (map (algebraMap k K))
    apply mem_range_map_iff_coeffs_subset.mpr
    intro c hc
    obtain ⟨m, _, rfl⟩ := mem_coeffs_iff.mp hc
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro γ
    have h := congrArg (fun f : MvPolynomial σ K => f.coeff m) (hf γ)
    simp only [coefficientGaloisPolynomial_smul, coeff_map] at h
    exact h

/-- Polynomial primes with the same contraction are conjugate
under the coefficient Galois group. -/
theorem finite_galois_polynomial_primes_conjugate
    [FiniteDimensional k K] [IsGalois k K]
    (P Q : Ideal (MvPolynomial σ K)) [P.IsPrime] [Q.IsPrime]
    (hPQ : P.comap (map (algebraMap k K)) = Q.comap (map (algebraMap k K))) :
    ∃ γ : Gal(K/k), Q = P.map (map γ.toRingHom) := by
  obtain ⟨γ, hγ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
    (MvPolynomial σ k) (MvPolynomial σ K) Gal(K/k) P Q hPQ
  refine ⟨γ, ?_⟩
  rw [hγ, Ideal.pointwise_smul_def]
  congr 1

/-- A minimal prime of an extended prime ideal contracts to the original
prime. This is the shared-contraction hypothesis needed for conjugacy. -/
theorem galois_polynomial_minimalPrime_under
    [FiniteDimensional k K] [IsGalois k K]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (P : Ideal (MvPolynomial σ K))
    (hP : P ∈ (I.map (map (algebraMap k K))).minimalPrimes) :
    P.comap (map (algebraMap k K)) = I := by
  let : P.IsPrime := hP.isPrime
  let : Algebra.IsIntegral (MvPolynomial σ k) (MvPolynomial σ K) :=
    Algebra.IsInvariant.isIntegral (MvPolynomial σ k) (MvPolynomial σ K) Gal(K/k)
  have hIP : I ≤ P.under (MvPolynomial σ k) := Ideal.map_le_iff_le_comap.mp hP.le
  obtain ⟨Q, hQP, hQprime, hQover⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := I) (q := P.under (MvPolynomial σ k)) P hIP
  have hIQ : I.map (map (algebraMap k K)) ≤ Q :=
    Ideal.map_le_iff_le_comap.mpr (by
      simpa only [Ideal.under_def, MvPolynomial.algebraMap_def] using hQover.over.le)
  have hPQ : P ≤ Q := hP.2 ⟨hQprime, hIQ⟩ hQP
  have he : P = Q := le_antisymm hPQ hQP
  rw [he]
  simpa only [Ideal.under_def, MvPolynomial.algebraMap_def] using hQover.over.symm

lemma eval_coefficient_galois_at_base_point (γ : Gal(K/k))
    (x : σ → k) (f : MvPolynomial σ K) :
    eval (algebraMap k K ∘ x) (map γ.toRingHom f) =
      γ (eval (algebraMap k K ∘ x) f) := by
  rw [eval_map]
  have he : γ.toRingHom ∘ (algebraMap k K ∘ x) = algebraMap k K ∘ x := by
    funext i
    exact γ.commutes (x i)
  have h := eval₂_comp γ.toRingHom (algebraMap k K ∘ x) f
  rw [he] at h
  exact h.symm

end
end CCDN
