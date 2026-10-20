module

public import CCDN.ProjectionScalarExtension
public import Mathlib.FieldTheory.AlgebraicClosure

/-! Primality of polynomial ideals over an algebraically closed field
survives arbitrary coefficient-field extensions. Coefficient-linear
functionals reduce nonmembership to genuine base-field equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma coefficientLinearPolynomial_eval_base_point
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (φ : L →ₗ[K] K) (f : MvPolynomial (Fin n) L) (x : Fin n → K) :
    φ (eval (fun j => algebraMap K L (x j)) f) = eval x (coefficientLinearPolynomial φ f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [coefficientLinearPolynomial_C]
  | add f g hf hg => simp only [map_add, hf, hg, coefficientLinearPolynomial_add]
  | mul_X f j hf =>
    have hX : (X j : MvPolynomial (Fin n) L) = map (algebraMap K L) (X j) := by simp
    rw [hX, coefficientLinearPolynomial_mul_map, map_X]
    simp only [map_mul, eval_X, ← hf]
    simpa only [Algebra.smul_def, mul_comm, Algebra.algebraMap_self, RingHom.id_apply] using φ.map_smul (x j)
      (eval (fun j => algebraMap K L (x j)) f)

/-- Geometric primeness over an algebraically closed base is automatic for
an actual prime ideal; no extension-primality hypothesis is required. -/
theorem prime_ideal_scalar_extension_of_isAlgClosed
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    (I.map (map (algebraMap K L))).IsPrime := by
  let J := I.map (map (algebraMap K L))
  refine ⟨?_, ?_⟩
  · intro htop
    have h1 : map (algebraMap K L) (1 : MvPolynomial (Fin n) K) ∈ J := by
      change map (algebraMap K L) (1 : MvPolynomial (Fin n) K) ∈ I.map (map (algebraMap K L))
      rw [htop]; trivial
    exact Ideal.IsPrime.ne_top ‹I.IsPrime› (Ideal.eq_top_of_isUnit_mem I
      ((mem_ideal_scalar_extension_iff I 1).mp h1) isUnit_one)
  · intro f g hfg
    by_contra h
    have hf : f ∉ J := fun hh => h (Or.inl hh)
    have hg : g ∉ J := fun hh => h (Or.inr hh)
    obtain ⟨φ, hφ⟩ := exists_coefficientLinearPolynomial_not_mem I f hf
    obtain ⟨ψ, hψ⟩ := exists_coefficientLinearPolynomial_not_mem I g hg
    have hn : coefficientLinearPolynomial φ f * coefficientLinearPolynomial ψ g ∉ I := by
      intro hm
      exact (Ideal.IsPrime.mem_or_mem ‹I.IsPrime› hm).elim hφ hψ
    have hex : ∃ x : Fin n → K, (∀ p ∈ I, eval x p = 0) ∧
        eval x (coefficientLinearPolynomial φ f * coefficientLinearPolynomial ψ g) ≠ 0 := by
      by_contra! hx
      apply hn
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
      intro x hxI
      rw [aeval_eq_eval]
      exact hx x (fun p hp => by simpa only [aeval_eq_eval] using hxI p hp)
    obtain ⟨x, hx, hne⟩ := hex
    have hzero : ∀ p ∈ J, eval (fun j => algebraMap K L (x j)) p = 0 := by
      intro p hp
      change p ∈ RingHom.ker (eval (fun j => algebraMap K L (x j)))
      apply Ideal.span_le.mpr ?_ hp
      rintro _ ⟨q, hq, rfl⟩
      change eval (fun j => algebraMap K L (x j)) (map (algebraMap K L) q) = 0
      rw [eval_map]
      exact (eval₂_comp (algebraMap K L) x q).symm.trans (by rw [hx q hq, map_zero])
    have hz := hzero (f * g) hfg
    rw [map_mul, mul_eq_zero] at hz
    apply hne
    rw [map_mul]
    rcases hz with hz | hz
    · rw [← coefficientLinearPolynomial_eval_base_point φ f x, hz, map_zero, zero_mul]
    · rw [← coefficientLinearPolynomial_eval_base_point ψ g x, hz, map_zero, mul_zero]

/-- Primality descends along an injective coefficient-field extension. -/
theorem prime_ideal_of_prime_scalar_extension
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime] : I.IsPrime := by
  have he : (I.map (map (algebraMap K L))).comap (map (algebraMap K L)) = I := by
    ext f
    exact mem_ideal_scalar_extension_iff I f
  rw [← he]
  infer_instance

lemma ideal_scalar_extension_tower
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    (I.map (map (algebraMap K L))).map (map (algebraMap L E)) =
      I.map (map (algebraMap K E)) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  ext e
  simp only [RingHom.comp_apply, coeff_map]
  exact (IsScalarTower.algebraMap_apply K L E (f.coeff e)).symm

/-- Primality after base change to the algebraic closure implies primality
after every coefficient-field extension. This discharges geometric
primality at transcendental universal coefficient fields as well. -/
theorem prime_ideal_scalar_extension_of_algebraicClosure
    {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime] :
    (I.map (map (algebraMap K L))).IsPrime := by
  let E := AlgebraicClosure L
  let φ : AlgebraicClosure K →ₐ[K] E := IsAlgClosed.lift
  let : Algebra (AlgebraicClosure K) E := φ.toRingHom.toAlgebra
  let : IsScalarTower K (AlgebraicClosure K) E := IsScalarTower.of_algHom φ
  have hp := prime_ideal_scalar_extension_of_isAlgClosed (L := E)
    (I.map (map (algebraMap K (AlgebraicClosure K))))
  rw [ideal_scalar_extension_tower] at hp
  let J := I.map (map (algebraMap K L))
  have hJ : (J.map (map (algebraMap L E))).IsPrime := by
    dsimp only [J]
    rw [ideal_scalar_extension_tower]
    exact hp
  let := hJ
  exact prime_ideal_of_prime_scalar_extension (L := E) J

end
end CCDN
