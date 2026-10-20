module

public import AffineCurveCounting.HypersurfaceGoodDirection
public import AffineCurveCounting.PlaneSmoothGeometricIrreducibility
public import AffineCurveCounting.ShearNormalization

/-! Actual affine two-plane substitutions, their degree bounds, and their
smooth base point. The irreducibility conclusion explicitly requires ordinary
irreducibility of the restricted equation; generic-plane irreducibility is a
separate obligation. -/

@[expose] public section
namespace AffineCurveCounting
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

/-- Restrict to the affine plane z + x*b + y*c. -/
def affinePlaneRestriction {K σ : Type*} [CommRing K]
    (z b c : σ → K) : MvPolynomial σ K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval (fun i => C (z i) + C (b i) * X 0 + C (c i) * X 1)

@[simp] lemma affinePlaneRestriction_eval_zero {K σ : Type*} [CommRing K]
    (z b c : σ → K) (f : MvPolynomial σ K) :
    eval (0 : Fin 2 → K) (affinePlaneRestriction z b c f) = eval z f := by
  change (eval (0 : Fin 2 → K)).comp (affinePlaneRestriction z b c).toRingHom f = _
  have he : (eval (0 : Fin 2 → K)).comp (affinePlaneRestriction z b c).toRingHom = eval z := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [affinePlaneRestriction]
    · intro i
      simp [affinePlaneRestriction]
  rw [he]

lemma affinePlaneRestriction_pderiv_zero {K σ : Type*} [CommRing K] [Fintype σ]
    (z b c : σ → K) (f : MvPolynomial σ K) :
    eval (0 : Fin 2 → K) (pderiv 0 (affinePlaneRestriction z b c f)) =
      ∑ i, eval z (pderiv i f) * b i := by
  rw [pderiv_algHom_chain, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, affinePlaneRestriction_eval_zero]
  congr 1
  simp [affinePlaneRestriction]

lemma affinePlaneRestriction_totalDegree_le {K σ : Type*} [Field K]
    (z b c : σ → K) (f : MvPolynomial σ K) :
    (affinePlaneRestriction z b c f).totalDegree ≤ f.totalDegree := by
  apply linear_eval₂_totalDegree_le _ _ _ f
  intro i
  apply (totalDegree_add _ _).trans
  apply max_le
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)
  · exact (totalDegree_mul _ _).trans (by simp)

/-- Every ordinarily irreducible plane through a smooth point in a transverse
direction is geometrically irreducible. -/
theorem irreducible_map_affinePlaneRestriction_of_transverse
    {K L σ : Type*} [Field K] [Field L] [Algebra K L] [Fintype σ]
    (f : MvPolynomial σ K) (z b c : σ → K)
    (hz : eval z f = 0) (hb : (∑ i, eval z (pderiv i f) * b i) ≠ 0)
    (hf : Irreducible (affinePlaneRestriction z b c f)) :
    Irreducible (MvPolynomial.map (algebraMap K L) (affinePlaneRestriction z b c f)) := by
  apply irreducible_map_of_smooth_plane_point _ hf (0 : Fin 2 → K) 0
  · simpa only [affinePlaneRestriction_eval_zero] using hz
  · simpa only [affinePlaneRestriction_pderiv_zero] using hb

end
end AffineCurveCounting
