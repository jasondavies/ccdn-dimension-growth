module

public import CCDN.GaloisPolynomialPrimes
public import CCDN.FiniteGaloisIdealDefinition
public import CCDN.AlgebraicHilbertDimension

/-! Base-field points lie on every geometric component. Finite
Galois conjugacy first covers every prime over the original prime ideal;
finite fields of definition then remove the finite-extension restriction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem finite_galois_base_point_on_prime_over
    (k K σ : Type*) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (I : Ideal (MvPolynomial σ k)) [I.IsPrime]
    (P : Ideal (MvPolynomial σ K)) [P.IsPrime]
    (hP : P.comap (map (algebraMap k K)) = I)
    (x : σ → k) (hx : ∀ f ∈ I, eval x f = 0) :
    ∀ f ∈ P, eval (algebraMap k K ∘ x) f = 0 := by
  let J := I.map (map (algebraMap k K))
  let M := RingHom.ker (eval (algebraMap k K ∘ x))
  let : M.IsPrime := RingHom.ker_isPrime _
  have hJM : J ≤ M := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change eval (algebraMap k K ∘ x) (map (algebraMap k K) f) = 0
    rw [eval_map, ← eval₂_comp, hx f hf, map_zero]
  obtain ⟨Q, hQ, hQM⟩ := Ideal.exists_minimalPrimes_le hJM
  let : Q.IsPrime := hQ.isPrime
  obtain ⟨γ, hγ⟩ := finite_galois_polynomial_primes_conjugate k K σ P Q
    (hP.trans (galois_polynomial_minimalPrime_under k K σ I Q hQ).symm)
  intro f hf
  have hm : map γ.toRingHom f ∈ Q := by
    rw [hγ]
    exact Ideal.mem_map_of_mem _ hf
  have hz := hQM hm
  change eval (algebraMap k K ∘ x) (map γ.toRingHom f) = 0 at hz
  rw [eval_coefficient_galois_at_base_point] at hz
  exact γ.injective (hz.trans (map_zero γ).symm)

/-- The finite-dimensional restriction is removed using a constructed
finite Galois field of definition for the prime ideal. -/
theorem galois_base_point_on_prime_over
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime]
    (hP : P.comap (map (algebraMap k K)) = I)
    (x : Fin n → k) (hx : ∀ f ∈ I, eval x f = 0) :
    ∀ f ∈ P, eval (algebraMap k K ∘ x) f = 0 := by
  obtain ⟨L, hL⟩ := exists_finite_galois_ideal_definition k K P
  let Q := P.comap (map (algebraMap L K))
  let : Q.IsPrime := Ideal.comap_isPrime _ P
  have hcomp : (map (σ := Fin n) (algebraMap L K)).comp (map (algebraMap k L)) =
      map (algebraMap k K) := by
    ext i
    · simp
    · simp
  have hQ : Q.comap (map (algebraMap k L)) = I := by
    change (P.comap (map (algebraMap L K))).comap (map (algebraMap k L)) = I
    rw [Ideal.comap_comap, hcomp, hP]
  have hzero := finite_galois_base_point_on_prime_over k L (Fin n) I Q hQ x hx
  have hker : Q.map (map (algebraMap L K)) ≤
      RingHom.ker (eval (algebraMap k K ∘ x)) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change eval (algebraMap k K ∘ x) (map (algebraMap L K) f) = 0
    have he : algebraMap k K ∘ x = algebraMap L K ∘ (algebraMap k L ∘ x) := by
      funext i
      exact IsScalarTower.algebraMap_apply k L K (x i)
    rw [he, eval_map, ← eval₂_comp, hzero f hf, map_zero]
  rw [hL] at hker
  exact hker

/-- Every rational point of a prime variety lies on each minimal component
of its extension to an arbitrary algebraic Galois field. -/
theorem galois_base_point_on_every_component
    (k K : Type*) [Field k] [Field K] [Algebra k K] [IsGalois k K]
    {n : ℕ} (I : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime]
    (P : Ideal (MvPolynomial (Fin n) K))
    (hP : P ∈ (I.map (map (algebraMap k K))).minimalPrimes)
    (x : Fin n → k) (hx : ∀ f ∈ I, eval x f = 0) :
    ∀ f ∈ P, eval (algebraMap k K ∘ x) f = 0 := by
  let : P.IsPrime := hP.isPrime
  exact galois_base_point_on_prime_over k K I P
    (algebraic_polynomial_minimalPrime_under k K (Fin n) I P hP) x hx

end
end CCDN
