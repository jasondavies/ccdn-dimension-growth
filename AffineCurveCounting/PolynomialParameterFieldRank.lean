module

public import AffineCurveCounting.GenericLinearParameterField

/-! The degree of a finite coefficient-field extension is unchanged by
adjoining rational parameters, measured over the actual parameter
intermediate field inside an arbitrary polynomial fraction field. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem polynomial_parameter_field_finrank
    {K A F σ : Type*} [Field K] [Field A] [Algebra K A]
    [Module.Finite K A] [Field F] [Algebra K F]
    [Algebra (MvPolynomial σ A) F]
    [IsFractionRing (MvPolynomial σ A) F]
    [IsScalarTower K (MvPolynomial σ A) F] :
    Module.finrank (polynomialParameterField (K := K) (A := A) (F := F) (σ := σ)) F =
      Module.finrank K A := by
  classical
  let P := MvPolynomial σ K
  let Q := MvPolynomial σ A
  let η : Q →ₐ[K] F := IsScalarTower.toAlgHom K Q F
  let v : σ → F := fun i => η (X i)
  let R := polynomialParameterField (K := K) (A := A) (F := F) (σ := σ)
  let u : σ → R := fun i => ⟨v i,IntermediateField.subset_adjoin K _ ⟨i,rfl⟩⟩
  have hQ : AlgebraicIndependent K (X : σ → Q) := by
    have he : (aeval (X : σ → Q) : P →ₐ[K] Q).toRingHom = map (algebraMap K A) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change (aeval (X : σ → Q) : P →ₐ[K] Q) (C c) = _
        rw [aeval_C]
        change algebraMap K (MvPolynomial σ A) c =
          MvPolynomial.map (algebraMap K A) (C c)
        simp only [MvPolynomial.map_C,MvPolynomial.algebraMap_apply]
      · intro i
        change (aeval (X : σ → Q) : P →ₐ[K] Q) (X i) = _
        rw [aeval_X]
        change (X i : MvPolynomial σ A) =
          MvPolynomial.map (algebraMap K A) (X i)
        rw [MvPolynomial.map_X]
    change Function.Injective (aeval (X : σ → Q) : P →ₐ[K] Q)
    change Function.Injective (aeval (X : σ → Q) : P →ₐ[K] Q).toRingHom
    rw [he]
    exact map_injective _ (algebraMap K A).injective
  have hF : AlgebraicIndependent K v := hQ.map' (IsFractionRing.injective Q F)
  have hR : AlgebraicIndependent K u := AlgebraicIndependent.of_comp R.val hF
  let ρ : P →ₐ[K] R := aeval u
  let ψ : P →ₐ[K] F := aeval v
  have heq : R.val.comp ρ = ψ := by ext i; simp [ρ,ψ,u]
  let : Algebra P R := ρ.toRingHom.toAlgebra
  let : Algebra P F := ψ.toRingHom.toAlgebra
  let : IsScalarTower P R F := IsScalarTower.of_algebraMap_eq' (congrArg AlgHom.toRingHom heq).symm
  let : IsScalarTower P Q F := IsScalarTower.of_algebraMap_eq' (by
    change ψ.toRingHom = (algebraMap Q F).comp (map (algebraMap K A))
    apply MvPolynomial.ringHom_ext
    · intro c
      change (aeval v) (C c) = algebraMap Q F
        (MvPolynomial.map (algebraMap K A) (C c))
      rw [aeval_C,MvPolynomial.map_C]
      exact IsScalarTower.algebraMap_apply K Q F c
    · intro i
      change (aeval v) (X i) = algebraMap Q F
        (MvPolynomial.map (algebraMap K A) (X i))
      rw [aeval_X,MvPolynomial.map_X]
      rfl)
  have hgen : IntermediateField.adjoin K (Set.range u) = ⊤ := by
    apply IntermediateField.lift_injective R
    rw [IntermediateField.lift_adjoin,IntermediateField.lift_top,← Set.range_comp]
    rfl
  let : IsFractionRing P R := isFractionRing_of_generating_tuple ρ hR
    (fun i => X i) (by
      convert hgen using 2
      congr 1
      funext i
      change (aeval u) (X i) = u i
      rw [aeval_X])
  simpa only [Fintype.card_fin] using
    polynomial_fraction_extension_finrank (R := R) (F := F) (σ := σ) (Module.finBasis K A)

end
end AffineCurveCounting
