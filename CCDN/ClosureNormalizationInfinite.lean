module

public import CCDN.FixedCoordinateEliminationInfinite
public import CCDN.ClosureIntegralComposition

/-! Finite linear normalization retaining the homogenizing coordinate over
any infinite field, in every dimension including zero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

theorem exists_closure_normalization_infinite
    {K : Type*} [Field K] [Infinite K] (m k : ℕ)
    (I : Ideal (MvPolynomial (Fin (m + k)) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m) :
    ∃ a : Fin m → MvPolynomial (Fin (m + k)) K,
      (∀ i, (a i).IsHomogeneous 1) ∧
      (projectionCoordinateMap I a).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I a) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a)).IsIntegral := by
  induction k with
  | zero =>
    let a : Fin m → MvPolynomial (Fin m) K := X
    have he : projectionCoordinateMap I a = Ideal.Quotient.mkₐ K I := by
      ext i
      simp [projectionCoordinateMap, a]
    have hI0 : I = ⊥ := ideal_eq_bot_of_full_hilbert_dimension I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›) (by simpa only [Fintype.card_fin, Nat.add_zero] using hdim)
    refine ⟨a, fun i => isHomogeneous_X K i, ?_, ?_, ?_⟩
    · rw [he]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective K I)
    · rw [he]
      apply (RingHom.injective_iff_ker_eq_bot _).mpr
      change RingHom.ker ((Ideal.Quotient.mkₐ K I).toRingHom) = ⊥
      rwa [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker]
    · have hc : projectionCoordinateMap (projectiveClosureIdeal I)
          (closureProjectionCoordinates a) = Ideal.Quotient.mkₐ K (projectiveClosureIdeal I) := by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [projectionCoordinateMap, closureProjectionCoordinates, a]
      rw [hc]
      exact RingHom.isIntegral_of_surjective _ (Ideal.Quotient.mkₐ_surjective K _)
  | succ k ih =>
    have hI0 : I ≠ ⊥ := by
      intro hz
      rw [hz, filteredHilbertPolynomial_bot, Polynomial.natDegree_preHilbertPoly] at hdim
      simp only [Fintype.card_fin] at hdim
      omega
    obtain ⟨f,hfi,hf⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    obtain ⟨c,hc,hintc,hconec⟩ := exists_closure_integral_elimination_infinite I f hf hfi
    let ψ := projectionCoordinateMap I c
    let J := RingHom.ker ψ
    let : J.IsPrime := RingHom.ker_isPrime ψ.toRingHom
    have hdimJ : (filteredHilbertPolynomial J).natDegree = m :=
      (integral_projection_hilbert_dimension_eq I ψ hintc).trans hdim
    obtain ⟨a,ha,hinta,hinja,hconea⟩ := ih J hdimJ
    let a' := fun i => aeval c (a i)
    let φ := Ideal.kerLiftAlg ψ
    have hφ : φ.IsIntegral := hintc.kerLift
    have hint := RingHom.IsIntegral.trans (projectionCoordinateMap J a).toRingHom
      φ.toRingHom hinta hφ
    have he : φ.comp (projectionCoordinateMap J a) = projectionCoordinateMap I a' := by
      ext i
      simp only [AlgHom.comp_apply, projectionCoordinateMap, aeval_X, Ideal.Quotient.mkₐ_eq_mk]
      rfl
    refine ⟨a', fun i => ?_, ?_, ?_, ?_⟩
    · simpa only [Nat.one_mul] using (ha i).aeval c hc
    · change (φ.comp (projectionCoordinateMap J a)).IsIntegral at hint
      rwa [he] at hint
    · rw [← he]
      exact (Ideal.kerLiftAlg_injective ψ).comp hinja
    · exact closure_projection_integral_comp I c hc a hconec hconea

theorem exists_closure_normalization_infinite_of_le
    {K : Type*} [Field K] [Infinite K] (m n : ℕ) (hmn : m ≤ n)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : (filteredHilbertPolynomial I).natDegree = m) :
    ∃ a : Fin m → MvPolynomial (Fin n) K,
      (∀ i, (a i).IsHomogeneous 1) ∧
      (projectionCoordinateMap I a).IsIntegral ∧
      Function.Injective (projectionCoordinateMap I a) ∧
      (projectionCoordinateMap (projectiveClosureIdeal I)
        (closureProjectionCoordinates a)).IsIntegral := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  exact exists_closure_normalization_infinite m k I hdim

end
end CCDN
