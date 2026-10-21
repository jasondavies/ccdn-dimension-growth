/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Linear coordinate maps applied coefficientwise to polynomial families.
A basis at one specialization certifies generic linear independence over
the polynomial parameter ring. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Extend a linear functional coefficientwise, without requiring it to
preserve products in the coefficient algebra. -/
def coefficientLinearMap {K A σ : Type*} [Field K] [CommRing A] [Algebra K A]
    (l : A →ₗ[K] K) : MvPolynomial σ A →ₗ[K] MvPolynomial σ K where
  toFun p := AddMonoidAlgebra.ofCoeff (Finsupp.mapRange l l.map_zero p.coeff)
  map_add' p q := by ext d; simp
  map_smul' c p := by ext d; simp

@[simp] lemma coefficientLinearMap_coeff {K A σ : Type*}
    [Field K] [CommRing A] [Algebra K A] (l : A →ₗ[K] K)
    (p : MvPolynomial σ A) (d : σ →₀ ℕ) :
    (coefficientLinearMap l p).coeff d = l (p.coeff d) := rfl

lemma coefficientLinearMap_map_mul {K A σ : Type*}
    [Field K] [CommRing A] [Algebra K A] (l : A →ₗ[K] K)
    (p : MvPolynomial σ K) (q : MvPolynomial σ A) :
    coefficientLinearMap l (map (algebraMap K A) p * q) =
      p * coefficientLinearMap l q := by
  classical
  ext d
  simp only [coefficientLinearMap_coeff, coeff_mul, map_sum, coeff_map]
  apply Finset.sum_congr rfl
  intro c hc
  simpa only [Algebra.smul_def, Algebra.algebraMap_self,RingHom.id_apply] using
    l.map_smul (p.coeff c.1) (q.coeff c.2)

lemma coefficientLinearMap_eval {K A σ : Type*}
    [Field K] [CommRing A] [Algebra K A] (l : A →ₗ[K] K)
    (p : MvPolynomial σ A) (a : σ → K) :
    eval a (coefficientLinearMap l p) =
      l (eval (fun i => algebraMap K A (a i)) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp,hq]
  | monomial d c =>
    have he : coefficientLinearMap l (monomial d c) = monomial d (l c) := by
      ext e
      simp only [coefficientLinearMap_coeff, coeff_monomial]
      split_ifs <;> simp
    rw [he,eval_monomial,eval_monomial]
    simp only [Finsupp.prod]
    simpa only [Algebra.smul_def,Algebra.algebraMap_self,RingHom.id_apply,map_prod,map_pow,mul_comm] using
      (l.map_smul (∏ i ∈ d.support, a i ^ d i) c).symm

/-- A polynomial family which specializes to a basis is independent over
the entire polynomial parameter ring, not only over its constant field. -/
theorem polynomial_family_independent_of_basis_specialization
    {K A σ ι : Type*} [Field K] [CommRing A] [Algebra K A]
    [Fintype ι] (b : Module.Basis ι K A)
    (p : ι → MvPolynomial σ A) (a : σ → K)
    (hp : ∀i, eval (fun j => algebraMap K A (a j)) (p i) = b i)
    (c : ι → MvPolynomial σ K)
    (hc : ∑i, map (algebraMap K A) (c i) * p i = 0) :
    c = 0 := by
  classical
  let M : Matrix ι ι (MvPolynomial σ K) := fun i j =>
    coefficientLinearMap (b.coord i) (p j)
  have hM : M.det ≠ 0 := by
    intro he
    have hv := congrArg (eval a) he
    have hm : (eval a).mapMatrix M = 1 := by
      ext i j
      change eval a (coefficientLinearMap (b.coord i) (p j)) = _
      rw [coefficientLinearMap_eval,hp]
      simp [Module.Basis.coord_apply,Matrix.one_apply,Finsupp.single_apply,eq_comm]
    rw [RingHom.map_det,hm,Matrix.det_one,map_zero] at hv
    exact one_ne_zero hv
  have hzero : M.mulVec c = 0 := by
    funext i
    have hh := congrArg (coefficientLinearMap (b.coord i)) hc
    simp only [map_sum,map_zero,coefficientLinearMap_map_mul] at hh
    simpa only [Matrix.mulVec,dotProduct,M,mul_comm,Pi.zero_apply] using hh
  exact (Matrix.mulVec_injective_iff.mpr
    (Matrix.linearIndependent_cols_of_det_ne_zero hM)) (by simpa using hzero)

end
end CCDN
