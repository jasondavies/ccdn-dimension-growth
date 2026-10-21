/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Algebra.PolynomialLinearDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Algebra.IdealScalarDescent
import CCDN.Hilbert.HilbertScalarExtension
import CCDN.Projection.ProjectionScalarExtension
import Mathlib.RingTheory.Nullstellensatz

/-! Primality of polynomial ideals over an algebraically closed field
survives arbitrary coefficient-field extensions. Coefficient-linear
functionals reduce nonmembership to base-field equations. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Geometric primeness over an algebraically closed base is automatic for
a prime ideal. -/
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
    obtain ⟨φ, hφ⟩ := exists_polynomialCoefficientLinear_not_mem I f hf
    obtain ⟨ψ, hψ⟩ := exists_polynomialCoefficientLinear_not_mem I g hg
    have hn : polynomialCoefficientLinear φ f * polynomialCoefficientLinear ψ g ∉ I := by
      intro hm
      exact (Ideal.IsPrime.mem_or_mem ‹I.IsPrime› hm).elim hφ hψ
    have hex : ∃ x : Fin n → K, x ∈ idealZeroLocus I ∧
        eval x (polynomialCoefficientLinear φ f * polynomialCoefficientLinear ψ g) ≠ 0 := by
      by_contra! hx
      apply hn
      rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
      intro x hxI
      rw [aeval_eq_eval]
      exact hx x (fun p hp => by simpa only [aeval_eq_eval] using hxI p hp)
    obtain ⟨x, hx, hne⟩ := hex
    have hzero : (fun j => algebraMap K L (x j)) ∈ idealZeroLocus J := by
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
    · rw [polynomialCoefficientLinear_eval φ f x, Function.comp_def, hz, map_zero, zero_mul]
    · rw [polynomialCoefficientLinear_eval ψ g x, Function.comp_def, hz, map_zero, mul_zero]

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
after every coefficient-field extension, including transcendental
universal coefficient fields. -/
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
