module

public import CCDN.Height.LinearParameterPrimitive
public import CCDN.Projection.HomogeneousFiniteProjectionDegree
public import CCDN.Projection.HomogeneousProjectionEquation
public import CCDN.Projection.HilbertProjectionDegree
public import CCDN.Center.HomogeneousIntegralRelation
public import CCDN.Algebra.PolynomialPredicates
/-! Primitive augmentation of a finite homogeneous normalization
produces an irreducible equation whose degree in the new variable is exactly
the Hilbert multiplicity. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The equation is constructed from the given normalization; its homogeneous
and univariate degrees are both the Hilbert multiplicity. -/
theorem exists_homogeneous_normalization_primitive_equation
    {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    [Algebra (MvPolynomial (Fin n) K ⧸ I) F]
    [IsScalarTower K (MvPolynomial (Fin n) K ⧸ I) F]
    [IsFractionRing (MvPolynomial (Fin n) K ⧸ I) F]
    (hI : IsHomogeneousIdeal I)
    (a : Fin (m + 1) → MvPolynomial (Fin n) K)
    (ha : ∀ i, (a i).IsHomogeneous 1)
    (hi : Function.Injective (projectionCoordinateMap I a))
    (hint : (projectionCoordinateMap I a).IsIntegral)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d) :
    ∃ z : MvPolynomial (Fin n) K, ∃ f : MvPolynomial (Fin (m + 2)) K,
      IntermediateField.adjoin K
        (Set.range (fun i : Fin (m + 2) => algebraMap (MvPolynomial (Fin n) K ⧸ I) F
          ((Ideal.Quotient.mk I) (Fin.cases z a i)))) = ⊤ ∧
      Irreducible f ∧ f.IsHomogeneous d ∧ f.totalDegree = d ∧ 0 < d ∧
      RingHom.ker (projectionCoordinateMap I (Fin.cases z a)) = Ideal.span {f} ∧
      (finSuccEquiv K (m + 1) f).natDegree = d := by
  classical
  obtain ⟨hdim, hdegree⟩ := hdimdeg
  obtain ⟨k, _, hfield⟩ := exists_bounded_linear_parameter_primitive (F := F)
    I a (fun i => (ha i).totalDegree_le) hi d ⟨hdim, hdegree⟩
  let z := momentCoordinate K n k
  let l : Fin (m + 2) → MvPolynomial (Fin n) K := Fin.cases z a
  have hl (i) : (l i).IsHomogeneous 1 := by
    refine Fin.cases ?_ (fun j => ha j) i
    change (momentCoordinate K n k).IsHomogeneous 1
    unfold momentCoordinate
    exact IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X ((k : K) ^ j.val) j)
  let ψ := projectionCoordinateMap I l
  have heq : ψ.comp (rename Fin.succ) = projectionCoordinateMap I a := by
    ext i
    simp only [AlgHom.comp_apply, rename_X, projectionCoordinateMap, aeval_X,
      Ideal.Quotient.mkₐ_eq_mk]
    change (Ideal.Quotient.mk I) (aeval l (X i.succ)) = (Ideal.Quotient.mk I) (a i)
    rw [aeval_X]
    rfl
  have hintl : ψ.IsIntegral := by
    apply RingHom.IsIntegral.tower_top (rename Fin.succ).toRingHom ψ.toRingHom
    change (ψ.comp (rename Fin.succ)).IsIntegral
    rwa [heq]
  have hAI : AlgebraicIndependent K (fun i : Fin (m + 1) => ψ (X i.succ)) := by
    have hh : AlgebraicIndependent K (fun i => (Ideal.Quotient.mk I) (a i)) := by
      change Function.Injective (aeval (fun i => (Ideal.Quotient.mk I) (a i)))
      rw [← projectionCoordinateMap_eq_aeval]
      exact hi
    convert hh using 1
    funext i
    change (Ideal.Quotient.mk I) (aeval l (X i.succ)) = (Ideal.Quotient.mk I) (a i)
    rw [aeval_X]
    rfl
  obtain ⟨f, hf, hfpos, _, hker⟩ := exists_hypersurface_projection_equation_degree_le
    I l (fun i => (hl i).totalDegree_le) d ⟨hdim, hdegree⟩
    (fun i => X i.succ) (fun _ => by simp) hAI
  have hfield' : IntermediateField.adjoin K
      (Set.range (fun i : Fin (m + 2) => algebraMap (MvPolynomial (Fin n) K ⧸ I) F
        ((Ideal.Quotient.mk I) (l i)))) = ⊤ := hfield
  have hlead := homogeneous_finite_birational_projection_leadingCoeff_eq
    (F := F) I hI l hl hintl hfield'
  rw [hker, principal_filteredHilbertPolynomial_leadingCoeff f hf.ne_zero hfpos,
    hdegree] at hlead
  have hfdeg : f.totalDegree = d := by
    have hh := (div_left_inj' (by positivity : ((m + 1).factorial : ℚ) ≠ 0)).mp hlead
    exact_mod_cast hh
  have hfhom : f.IsHomogeneous d := by
    rw [← hfdeg]
    exact homogeneous_projection_equation I hI l hl f hf.ne_zero hker
  exact ⟨z, f, hfield', hf, hfhom, hfdeg, hfdeg ▸ hfpos, hker,
    integral_homogeneous_projection_relation_natDegree I a hint z f hfhom hker⟩

end
end CCDN
