module

public import CCDN.HilbertLinearCoordinates
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Nullstellensatz

/-! An integral polynomial projection has exactly its kernel's zero locus
as its image over an algebraically closed field. Lying over constructs a
maximal ideal upstairs, and the Nullstellensatz constructs the actual point. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem integral_projection_exists_point
    {K σ τ : Type*} [Field K] [IsAlgClosed K] [Finite σ]
    (I : Ideal (MvPolynomial σ K)) (l : τ → MvPolynomial σ K)
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (z : τ → K)
    (hz : ∀ p ∈ RingHom.ker (projectionCoordinateMap I l), eval z p = 0) :
    ∃ x : σ → K, (∀ f ∈ I, eval x f = 0) ∧ ∀ i, eval x (l i) = z i := by
  classical
  let R := MvPolynomial τ K
  let A := MvPolynomial σ K ⧸ I
  let φ : R →ₐ[K] A := projectionCoordinateMap I l
  let : Algebra R A := φ.toRingHom.toAlgebra
  let : Algebra.IsIntegral R A := ⟨hint⟩
  let P : Ideal R := RingHom.ker (eval z)
  let : P.IsMaximal := RingHom.ker_isMaximal_of_surjective (eval z)
    (fun c => ⟨C c, eval_C c⟩)
  have hker : RingHom.ker (algebraMap R A) ≤ P := hz
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) P hker
  let : Q.IsMaximal := hQ
  let J := Q.comap (Ideal.Quotient.mk I)
  have hJ : J.IsMaximal := Ideal.comap_isMaximal_of_surjective _
    Ideal.Quotient.mk_surjective
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
  have hxJ (g : MvPolynomial σ K) : g ∈ J ↔ eval x g = 0 := by
    rw [hx, MvPolynomial.mem_vanishingIdeal_singleton_iff, aeval_eq_eval]
  refine ⟨x, ?_, ?_⟩
  · intro f hf
    apply (hxJ f).mp
    change Ideal.Quotient.mk I f ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact Q.zero_mem
  · intro i
    have hX : X i - C (z i) ∈ P := by
      change eval z (X i - C (z i)) = 0
      simp
    rw [← hQP] at hX
    have hmem : l i - C (z i) ∈ J := by
      change Ideal.Quotient.mk I (l i - C (z i)) ∈ Q
      change φ (X i - C (z i)) ∈ Q at hX
      dsimp only [φ] at hX
      rw [projectionCoordinateMap_eq_aeval, map_sub, aeval_X, aeval_C] at hX
      exact hX
    have he := (hxJ _).mp hmem
    simpa only [eval_sub, eval_C, sub_eq_zero] using he

end
end CCDN
