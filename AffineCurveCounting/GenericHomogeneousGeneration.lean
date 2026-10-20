module

public import AffineCurveCounting.HomogeneousEvaluation
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-! A complete homogeneous monomial basis at one coefficient specialization
certifies generation of that whole homogeneous piece at algebraically
independent coefficients. The certificate is its actual determinant. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

/-- If polynomial relations specialize to the entire degree-D monomial
basis, their generic values generate that homogeneous piece modulo any
ideal containing those values. No rank or nonzero minor is assumed. -/
theorem homogeneous_generation_of_basis_specialization
    {K L σ : Type*} [Field K] [Field L] [Algebra K L] {n D : ℕ}
    (p : Fin ((n + D).choose D) → MvPolynomial (Fin (n + 1)) (MvPolynomial σ K))
    (hp : ∀ j, (p j).IsHomogeneous D)
    (c : σ → K)
    (hc : ∀ j, map (eval c) (p j) = monomial (homogeneousMonomials n D j) 1)
    (u : σ → L) (hu : AlgebraicIndependent K u)
    (J : Ideal (MvPolynomial (Fin (n + 1)) L))
    (hJ : ∀ j, map (aeval u).toRingHom (p j) ∈ J)
    (f : MvPolynomial (Fin (n + 1)) L) (hf : f.IsHomogeneous D) : f ∈ J := by
  classical
  let M : Matrix (Fin ((n + D).choose D)) (Fin ((n + D).choose D)) (MvPolynomial σ K) :=
    fun i j => (p i).coeff (homogeneousMonomials n D j)
  have hspec : (eval c).mapMatrix M = 1 := by
    ext i j
    have hh := congrArg (fun q : MvPolynomial (Fin (n + 1)) K =>
      q.coeff (homogeneousMonomials n D j)) (hc i)
    change eval c ((p i).coeff (homogeneousMonomials n D j)) = _
    simpa only [coeff_map, coeff_monomial, (homogeneousMonomials_injective n D).eq_iff,
      Matrix.map_apply, Matrix.one_apply, M] using hh
  have hM : M.det ≠ 0 := by
    intro hz
    have hh := congrArg (eval c) hz
    rw [RingHom.map_det, hspec, Matrix.det_one, map_zero] at hh
    exact one_ne_zero hh
  let N := (aeval u).toRingHom.mapMatrix M
  have hN : N.det ≠ 0 := by
    rw [← RingHom.map_det]
    exact fun hz => hM ((injective_iff_map_eq_zero (aeval u : MvPolynomial σ K →ₐ[K] L)).mp hu M.det hz)
  let A := MvPolynomial (Fin (n + 1)) L ⧸ J
  let q := Ideal.Quotient.mk J
  let T := (algebraMap L A).mapMatrix N
  have hT : IsUnit T.det := by
    rw [← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr hN).map (algebraMap L A)
  let v : Fin ((n + D).choose D) → A := fun j => q (monomial (homogeneousMonomials n D j) 1)
  have hv : T.mulVec v = 0 := by
    funext i
    have hz := Ideal.Quotient.eq_zero_iff_mem.mpr (hJ i)
    rw [homogeneous_eq_sum_coeff _ ((hp i).map (aeval u).toRingHom), map_sum] at hz
    change (∑ j : Fin ((n + D).choose D), T i j * v j) = (0 : A)
    convert hz using 1
    apply Finset.sum_congr rfl
    intro j _
    change algebraMap L A (aeval u ((p i).coeff (homogeneousMonomials n D j))) *
      q (monomial (homogeneousMonomials n D j) 1) =
      q (monomial (homogeneousMonomials n D j)
        ((map (aeval u).toRingHom (p i)).coeff (homogeneousMonomials n D j)))
    rw [coeff_map]
    change q (C _) * q (monomial _ 1) = _
    rw [← map_mul, C_mul_monomial, mul_one]
    rfl
  have hv0 : v = 0 := by
    have hh := congrArg (fun w => T⁻¹.mulVec w) hv
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul T hT, Matrix.one_mulVec,
      Matrix.mulVec_zero] at hh
    exact hh
  rw [homogeneous_eq_sum_coeff f hf]
  apply J.sum_mem
  intro j _
  have hm : monomial (homogeneousMonomials n D j) (1 : L) ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hv0 j)
  have hh := J.mul_mem_left (C (f.coeff (homogeneousMonomials n D j))) hm
  simpa only [C_mul_monomial, mul_one] using hh

end
end AffineCurveCounting
