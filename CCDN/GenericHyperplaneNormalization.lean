module

public import CCDN.GenericHyperplaneAvoidance
public import CCDN.HomogeneousProjectiveCone
public import CCDN.BalancedParameterFiniteness
public import CCDN.ProjectiveClosureHilbertPolynomial
public import CCDN.HilbertScalarExtension
public import CCDN.IntegralProjectionHilbert
public import CCDN.HilbertFullDimension

/-! Universal hyperplanes give a finite linear normalization of
the projective closure cone. Finiteness and independence are proved from
the source ideal and algebraic independence of their coefficient tuple. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def genericHyperplaneForms {L : Type*} [Field L] {n r : ℕ}
    (u : Fin r × Fin (n + 1) → L) : Fin r → MvPolynomial (Fin (n + 1)) L :=
  fun i => ∑ j, C (u (i,j)) * X j

lemma genericHyperplaneForms_homogeneous {L : Type*} [Field L] {n r : ℕ}
    (u : Fin r × Fin (n + 1) → L) (i : Fin r) :
    (genericHyperplaneForms u i).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ j)

theorem generic_hyperplane_projection_integral
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r)
    (u : Fin r × Fin (n + 1) → L) (hu : AlgebraicIndependent K u) :
    (projectionCoordinateMap (projectiveClosureIdeal (I.map (map (algebraMap K L))))
      (genericHyperplaneForms u)).IsIntegral := by
  let J := projectiveClosureIdeal (I.map (map (algebraMap K L)))
  have havoid := independent_hyperplanes_avoid_projective_closure I hr u hu
  apply integral_projection_of_homogeneous_origin_fiber (L := L) J
    (projectiveClosureIdeal_homogeneous _) (genericHyperplaneForms u)
    (genericHyperplaneForms_homogeneous u)
  intro x hx
  apply homogeneous_cone_zero_of_no_projective_incidence J
    (projectiveClosureIdeal_homogeneous _) u havoid x
  · intro f hf
    simpa only [aeval_eq_eval] using hx f (Ideal.mem_sup_left hf)
  · intro i
    have hh := hx (genericHyperplaneForms u i)
      (Ideal.mem_sup_right (Ideal.subset_span ⟨i,rfl⟩))
    simpa [genericHyperplaneForms,aeval_eq_eval] using hh

theorem generic_hyperplane_normalization_independent
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsAlgClosed L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K L))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin (m + 1) × Fin (n + 1) → L) (hu : AlgebraicIndependent K u) :
    AlgebraicIndependent L (fun i =>
      (Ideal.Quotient.mk (projectiveClosureIdeal (I.map (map (algebraMap K L)))))
        (genericHyperplaneForms u i)) := by
  let IL := I.map (map (algebraMap K L))
  let J := projectiveClosureIdeal IL
  let ψ := projectionCoordinateMap J (genericHyperplaneForms u)
  have hIL : (filteredHilbertPolynomial IL).natDegree = m := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hm
  obtain ⟨d,_,_,hd⟩ := filteredHilbertPolynomial_positive_multiplicity IL
    (Ideal.IsPrime.ne_top ‹IL.IsPrime›)
  have hJ : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (projectiveClosureIdeal_hilbertPolynomial_parameters IL m d hIL (by simpa only [hIL] using hd)).1
  have hint : ψ.IsIntegral :=
    generic_hyperplane_projection_integral I (by rw [hm]; omega) u hu
  have hdim := integral_projection_hilbert_dimension_eq J ψ hint
  have hk : RingHom.ker ψ = ⊥ := ideal_eq_bot_of_full_hilbert_dimension _
    (RingHom.ker_ne_top _) (by simpa only [Fintype.card_fin,hJ] using hdim)
  have hi : Function.Injective ψ := (RingHom.injective_iff_ker_eq_bot ψ).mpr hk
  dsimp only [ψ] at hi
  rw [projectionCoordinateMap_eq_aeval] at hi
  exact hi

end
end CCDN
