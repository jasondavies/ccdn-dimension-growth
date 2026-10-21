module

public import CCDN.Auxiliary.HypersurfaceGoodDirection
public import CCDN.Determinant.PlaneSmoothGeometricIrreducibility
public import CCDN.Projection.ShearNormalization
/-! The chain rule for partial derivatives along a homomorphism of
polynomial algebras. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The polynomial chain rule for a homomorphism of polynomial algebras. -/
theorem pderiv_algHom_chain {K σ τ : Type*} [CommRing K] [Fintype σ]
    (φ : MvPolynomial σ K →ₐ[K] MvPolynomial τ K) (f : MvPolynomial σ K) (k : τ) :
    pderiv k (φ f) = ∑ i, φ (pderiv i f) * pderiv k (φ (X i)) := by
  classical
  have hC (a : K) : φ (C a) = C a := φ.commutes a
  induction f using MvPolynomial.induction_on with
  | C a => simp [hC]
  | add f g hf hg => simp only [map_add, hf, hg, add_mul, Finset.sum_add_distrib]
  | mul_X f j hf =>
    rw [map_mul, pderiv_mul, hf]
    calc
      _ = ∑ i, (φ (pderiv i f) * φ (X j) * pderiv k (φ (X i)) +
          if j = i then φ f * pderiv k (φ (X i)) else 0) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : j = i <;>
          simp [pderiv_X, hi, add_mul, mul_comm, add_comm]

end
end CCDN
