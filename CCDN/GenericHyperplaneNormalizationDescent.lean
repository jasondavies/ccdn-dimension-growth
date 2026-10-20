module

public import CCDN.GenericHyperplaneNormalization
public import CCDN.GeometricIdealPrimality

/-! Generic homogeneous normalization over the coefficient field itself.
The algebraic closure is used only to test the actual zero fiber, and
geometric primality is discharged from the base algebraic closure. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma generic_hyperplane_geometric_origin_fiber
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E] [IsAlgClosed E]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K E))).IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r)
    (u : Fin r × Fin (n + 1) → L)
    (hu : AlgebraicIndependent K (fun q => algebraMap L E (u q)))
    (x : Fin (n + 1) → E)
    (hx : x ∈ MvPolynomial.zeroLocus E
      (projectiveClosureIdeal (I.map (map (algebraMap K L))) ⊔
        Ideal.span (Set.range (genericHyperplaneForms u)))) : x = 0 := by
  let IL := I.map (map (algebraMap K L))
  let IE := I.map (map (algebraMap K E))
  let J := projectiveClosureIdeal IL
  let v : Fin r × Fin (n + 1) → E := fun q => algebraMap L E (u q)
  have havoid := independent_hyperplanes_avoid_projective_closure I hr v hu
  have hJmap : J.map (map (algebraMap L E)) = projectiveClosureIdeal IE := by
    rw [projectiveClosureIdeal_scalar_extension, ideal_scalar_extension_tower]
  apply homogeneous_cone_zero_of_no_projective_incidence (projectiveClosureIdeal IE)
    (projectiveClosureIdeal_homogeneous _) v havoid x
  · intro f hf
    have hle : J.map (map (algebraMap L E)) ≤ RingHom.ker (eval x) := by
      rw [Ideal.map_le_iff_le_comap]
      intro p hp
      change eval x (map (algebraMap L E) p) = 0
      simpa only [eval_map, aeval_def] using hx p (Ideal.mem_sup_left hp)
    apply hle
    rwa [hJmap]
  · intro i
    have hh := hx (genericHyperplaneForms u i)
      (Ideal.mem_sup_right (Ideal.subset_span ⟨i,rfl⟩))
    simpa only [genericHyperplaneForms, map_sum, map_mul, aeval_C, aeval_X] using hh

theorem generic_hyperplane_projection_integral_of_geometric_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hr : (filteredHilbertPolynomial I).natDegree < r)
    (u : Fin r × Fin (n + 1) → L) (hu : AlgebraicIndependent K u) :
    (projectionCoordinateMap (projectiveClosureIdeal (I.map (map (algebraMap K L))))
      (genericHyperplaneForms u)).IsIntegral := by
  let E := AlgebraicClosure L
  let : (I.map (map (algebraMap K E))).IsPrime :=
    prime_ideal_scalar_extension_of_algebraicClosure (L := E) I
  have hv : AlgebraicIndependent K (fun q => algebraMap L E (u q)) :=
    hu.map' (f := IsScalarTower.toAlgHom K L E) (algebraMap L E).injective
  apply integral_projection_of_homogeneous_origin_fiber (L := E)
    (projectiveClosureIdeal (I.map (map (algebraMap K L))))
    (projectiveClosureIdeal_homogeneous _) (genericHyperplaneForms u)
    (genericHyperplaneForms_homogeneous u)
  exact generic_hyperplane_geometric_origin_fiber I hr u hv

theorem generic_hyperplane_normalization_injective_of_geometric_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {n m : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [(I.map (map (algebraMap K (AlgebraicClosure K)))).IsPrime]
    (hm : (filteredHilbertPolynomial I).natDegree = m)
    (u : Fin (m + 1) × Fin (n + 1) → L) (hu : AlgebraicIndependent K u) :
    Function.Injective
      (projectionCoordinateMap (projectiveClosureIdeal (I.map (map (algebraMap K L))))
        (genericHyperplaneForms u)) := by
  let IL := I.map (map (algebraMap K L))
  let : IL.IsPrime := prime_ideal_scalar_extension_of_algebraicClosure (L := L) I
  let J := projectiveClosureIdeal IL
  let ψ := projectionCoordinateMap J (genericHyperplaneForms u)
  have hIL : (filteredHilbertPolynomial IL).natDegree = m := by
    rw [filteredHilbertPolynomial_scalar_extension]
    exact hm
  obtain ⟨d,_,_,hd⟩ := filteredHilbertPolynomial_positive_multiplicity IL
    (Ideal.IsPrime.ne_top ‹IL.IsPrime›)
  have hJ : (filteredHilbertPolynomial J).natDegree = m + 1 :=
    (projectiveClosureIdeal_hilbertPolynomial_parameters IL m d hIL
      (by simpa only [hIL] using hd)).1
  have hint : ψ.IsIntegral :=
    generic_hyperplane_projection_integral_of_geometric_prime I (by rw [hm]; omega) u hu
  have hdim := integral_projection_hilbert_dimension_eq J ψ hint
  have hk : RingHom.ker ψ = ⊥ := ideal_eq_bot_of_full_hilbert_dimension _
    (RingHom.ker_ne_top _) (by simpa only [Fintype.card_fin,hJ] using hdim)
  exact (RingHom.injective_iff_ker_eq_bot ψ).mpr hk

end
end CCDN
