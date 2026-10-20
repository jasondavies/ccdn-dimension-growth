module

public import AffineCurveCounting.ProjectionScalarExtension
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Nullstellensatz

/-! The image of an actual integral polynomial projection over an
algebraically closed field is exactly the zero locus of its kernel.
Lying over and the Nullstellensatz construct every preimage point. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

theorem exists_point_of_integral_projection_kernel_zero
    {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K)
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (z : Fin m → K)
    (hz : ∀ f ∈ RingHom.ker (projectionCoordinateMap I a), eval z f = 0) :
    ∃ x : Fin n → K, (∀ f ∈ I, eval x f = 0) ∧
      ∀ i, eval x (a i) = z i := by
  classical
  let ψ := projectionCoordinateMap I a
  let P := RingHom.ker (eval z)
  let J := P.map ψ.toRingHom
  have hker : RingHom.ker ψ.toRingHom ≤ P := hz
  have hJ : J ≠ ⊤ := by
    intro h
    exact RingHom.ker_ne_top (eval z)
      ((Ideal.map_eq_top_iff_of_ker_le ψ.toRingHom hker hint).mp h)
  let S := J.comap (Ideal.Quotient.mk I)
  have hS : S ≠ ⊤ := by
    intro h
    apply hJ
    exact Ideal.comap_eq_top_iff.mp h
  obtain ⟨M, hM, hSM⟩ := Ideal.exists_le_maximal S hS
  obtain ⟨x, hx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hM
  have hxS (f : MvPolynomial (Fin n) K) (hf : f ∈ S) : eval x f = 0 := by
    have hh := hSM hf
    rw [hx] at hh
    exact hh x (Set.mem_singleton x)
  refine ⟨x, ?_, ?_⟩
  · intro f hf
    apply hxS
    change (Ideal.Quotient.mk I) f ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact J.zero_mem
  · intro i
    have hP : X i - C (z i) ∈ P := by
      change eval z (X i - C (z i)) = 0
      simp
    have hJmem := Ideal.mem_map_of_mem ψ.toRingHom hP
    change (Ideal.Quotient.mk I) (aeval a (X i - C (z i))) ∈ J at hJmem
    have hh := hxS (aeval a (X i - C (z i))) hJmem
    simpa only [map_sub, aeval_X, aeval_C, algebraMap_eq, eval_C, sub_eq_zero] using hh

theorem integral_projection_image_zero_locus
    {K : Type*} [Field K] [IsAlgClosed K] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (a : Fin m → MvPolynomial (Fin n) K)
    (hint : (projectionCoordinateMap I a).IsIntegral) :
    (fun x : Fin n → K => fun i => eval x (a i)) '' MvPolynomial.zeroLocus K I =
      MvPolynomial.zeroLocus K (RingHom.ker (projectionCoordinateMap I a)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ f hf
    have hh := hx (aeval a f) ((mem_projectionCoordinateMap_ker I a f).mp hf)
    rw [comp_aeval_apply] at hh
    exact hh
  · intro hz
    obtain ⟨x, hx, he⟩ := exists_point_of_integral_projection_kernel_zero I a hint z
      (fun f hf => hz f hf)
    refine ⟨x, ?_, funext he⟩
    exact hx

end
end AffineCurveCounting
