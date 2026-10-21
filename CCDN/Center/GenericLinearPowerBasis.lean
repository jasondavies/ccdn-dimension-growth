/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.LinearForm
public import CCDN.Center.PolynomialCoefficientBasis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.PowerBasis

/-! A generic linear form is primitive whenever one linear specialization
is primitive. Independence follows from a specialization matrix;
the field degree is preserved by the explicit polynomial coefficient basis. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Let `b` be a power basis of `A` over `K`, and suppose the generic linear form `linearForm x`
specializes at `c` to the generator of `b`. Then the powers of `linearForm x` with exponents below
`b.dim` are linearly independent over `MvPolynomial σ K`. -/
theorem generic_linear_powers_polynomial_independent
    {K A σ : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype σ]
    (b : PowerBasis K A) (x : σ → A) (c : σ → K)
    (hc : ∑i, x i * algebraMap K A (c i) = b.gen) :
    LinearIndependent (MvPolynomial σ K)
      (fun i : Fin b.dim => linearForm x ^ (i : ℕ)) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro q hq i
  have he : ∀i : Fin b.dim,
      eval (fun j => algebraMap K A (c j)) (linearForm x ^ (i : ℕ)) =
        b.basis i := by
    intro i
    rw [map_pow,eval_linearForm,hc,b.basis_eq_pow]
  have hz := polynomial_family_independent_of_basis_specialization b.basis
    (fun i : Fin b.dim => linearForm x ^ (i : ℕ)) c he q (by
      simpa only [Algebra.smul_def,MvPolynomial.algebraMap_def] using hq)
  exact congrFun hz i

/-- The powers of the generic linear combination give a power
basis after adjoining independent rational parameters. -/
def genericLinearPowerBasis
    {K A R F σ : Type*} [Field K] [Field A] [Algebra K A]
    [Field R] [Field F] [Fintype σ]
    [Algebra (MvPolynomial σ K) R] [IsFractionRing (MvPolynomial σ K) R]
    [Algebra (MvPolynomial σ A) F] [IsFractionRing (MvPolynomial σ A) F]
    [Algebra (MvPolynomial σ K) F] [Algebra R F]
    [IsScalarTower (MvPolynomial σ K) R F]
    [IsScalarTower (MvPolynomial σ K) (MvPolynomial σ A) F]
    (b : PowerBasis K A) (x : σ → A) (c : σ → K)
    (hc : ∑i, x i * algebraMap K A (c i) = b.gen) : PowerBasis R F := by
  let u := algebraMap (MvPolynomial σ A) F (linearForm x)
  have hrank : Module.finrank R F = b.dim := by
    simpa only [Fintype.card_fin] using
      polynomial_fraction_extension_finrank (R := R) (F := F) (σ := σ) b.basis
  letI : FiniteDimensional R F := FiniteDimensional.of_finrank_pos (hrank.symm ▸ b.dim_pos)
  have hiP : LinearIndependent (MvPolynomial σ K) (fun i : Fin b.dim => u ^ (i : ℕ)) := by
    have hi := generic_linear_powers_polynomial_independent b x c hc
    have hm := hi.map' (IsScalarTower.toAlgHom (MvPolynomial σ K)
      (MvPolynomial σ A) F).toLinearMap
      (LinearMap.ker_eq_bot.mpr (IsFractionRing.injective (MvPolynomial σ A) F))
    change LinearIndependent (MvPolynomial σ K)
      (fun i : Fin b.dim => algebraMap (MvPolynomial σ A) F
        (linearForm x ^ (i : ℕ))) at hm
    simpa only [map_pow,u] using hm
  have hi : LinearIndependent R (fun i : Fin b.dim => u ^ (i : ℕ)) :=
    (LinearIndependent.iff_fractionRing (MvPolynomial σ K) R).mp hiP
  let basis := basisOfLinearIndependentOfCardEqFinrank'
    (fun i : Fin b.dim => u ^ (i : ℕ)) hi (by simpa only [Fintype.card_fin] using hrank.symm)
  exact {
    gen := u
    dim := b.dim
    basis := basis
    basis_eq_pow := fun i => congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank' _ hi _) i }

end
end CCDN
