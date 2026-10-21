module

public import CCDN.Center.ChowLastRowSplit
/-! The Chow incidence field in its nested final-row presentation.
The parameter field is computed from its displayed generators exactly. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

local instance nestedIncidenceCoefficientRing {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) : CommRing (MvPolynomial τ (MvPolynomial σ K ⧸ I)) := by
  letI : CommRing (MvPolynomial σ K ⧸ I) := inferInstance
  infer_instance

abbrev ChowFirstRowCoordinateRing {K : Type*} [Field K] {n : ℕ} (m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :=
  MvPolynomial (Fin m × Fin n) (MvPolynomial (Fin n) K ⧸ I)

abbrev ChowNestedCoordinateRing {K : Type*} [Field K] {n : ℕ} (m : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) :=
  MvPolynomial (Fin n) (ChowFirstRowCoordinateRing m I)

def chowNestedIncidenceMap {K F : Type*} [Field K] [Field F] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (ChowNestedCoordinateRing m I) F] : ChowIncidenceCoordinateRing m I →+* F :=
  (algebraMap (ChowNestedCoordinateRing m I) F).comp (chowLastRowSplit m I).toRingHom

lemma chowNestedIncidenceMap_isFractionRing {K F : Type*} [Field K] [Field F] {m n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (ChowNestedCoordinateRing m I) F]
    [IsFractionRing (ChowNestedCoordinateRing m I) F] :
    let : Algebra (ChowIncidenceCoordinateRing m I) F := (chowNestedIncidenceMap I).toAlgebra
    IsFractionRing (ChowIncidenceCoordinateRing m I) F := by
  exact (IsFractionRing.isFractionRing_iff_of_base_ringEquiv
    (S := F) (chowLastRowSplit m I).symm.toRingEquiv).mp inferInstance

lemma chowNestedIncidenceMap_ground {K F : Type*} [Field K] [Field F]
    [Algebra K F] {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (ChowNestedCoordinateRing m I) F]
    [IsScalarTower K (ChowNestedCoordinateRing m I) F] (c : K) :
    chowNestedIncidenceMap (m := m) (F := F) I
      (algebraMap K (ChowIncidenceCoordinateRing m I) c) = algebraMap K F c := by
  change algebraMap (ChowNestedCoordinateRing m I) F
    (chowLastRowSplit m I (C (Ideal.Quotient.mk I (C c)))) = _
  rw [chowLastRowSplit_C]
  exact (IsScalarTower.algebraMap_apply K (ChowNestedCoordinateRing m I) F c).symm

lemma chow_nested_parameter_field {K F : Type*} [Field K] [Field F]
    [Algebra K F] {m n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    [Algebra (ChowFirstRowCoordinateRing m I) F]
    [Algebra (ChowNestedCoordinateRing m I) F]
    [IsScalarTower (ChowFirstRowCoordinateRing m I) (ChowNestedCoordinateRing m I) F] :
    let : Algebra (ChowIncidenceCoordinateRing m I) F := (chowNestedIncidenceMap I).toAlgebra
    chowParameterField (E := F) m I = IntermediateField.adjoin K
      ((Set.range (fun q : Fin m × Fin n => algebraMap (ChowFirstRowCoordinateRing m I) F (X q)) ∪
        Set.range (fun i : Fin m => algebraMap (ChowFirstRowCoordinateRing m I) F
          (chowIncidenceMap m I (X (i,0))))) ∪
        Set.range (fun j : Fin n => algebraMap (ChowNestedCoordinateRing m I) F (X j))) := by
  let : Algebra (ChowIncidenceCoordinateRing m I) F := (chowNestedIncidenceMap I).toAlgebra
  change IntermediateField.adjoin K _ = _
  congr 1
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    cases q with
    | inl q =>
      rcases q with ⟨i,j⟩
      refine Fin.lastCases ?_ (fun k => ?_) i
      · right
        refine ⟨j,?_⟩
        simp only [chowIndependentVariables,chowIncidenceMap,aeval_X]
        change algebraMap (ChowNestedCoordinateRing m I) F (X j) =
          algebraMap (ChowNestedCoordinateRing m I) F (chowLastRowSplit m I (X (Fin.last m,j)))
        rw [chowLastRowSplit_X_last]
      · left; left
        refine ⟨(k,j),?_⟩
        simp only [chowIndependentVariables,chowIncidenceMap,aeval_X]
        change algebraMap (ChowFirstRowCoordinateRing m I) F (X (k,j)) =
          algebraMap (ChowNestedCoordinateRing m I) F (chowLastRowSplit m I (X (k.castSucc,j)))
        rw [chowLastRowSplit_X_first]
        exact IsScalarTower.algebraMap_apply _ _ _ _
    | inr i =>
      left; right
      refine ⟨i,?_⟩
      change algebraMap (ChowFirstRowCoordinateRing m I) F (chowIncidenceMap m I (X (i,0))) =
        algebraMap (ChowNestedCoordinateRing m I) F
          (chowLastRowSplit m I (chowIncidenceMap (m + 1) I (X (i.castSucc,0))))
      rw [chowLastRowSplit_incidence_first]
      exact IsScalarTower.algebraMap_apply _ _ _ _
  · rintro ((⟨⟨i,j⟩,rfl⟩ | ⟨i,rfl⟩) | ⟨j,rfl⟩)
    · refine ⟨Sum.inl (i.castSucc,j),?_⟩
      simp only [chowIndependentVariables,chowIncidenceMap,aeval_X]
      change algebraMap (ChowNestedCoordinateRing m I) F
        (chowLastRowSplit m I (X (i.castSucc,j))) = _
      rw [chowLastRowSplit_X_first]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    · refine ⟨Sum.inr i,?_⟩
      change algebraMap (ChowNestedCoordinateRing m I) F
        (chowLastRowSplit m I (chowIncidenceMap (m + 1) I (X (i.castSucc,0)))) = _
      rw [chowLastRowSplit_incidence_first]
      exact (IsScalarTower.algebraMap_apply _ _ _ _).symm
    · refine ⟨Sum.inl (Fin.last m,j),?_⟩
      simp only [chowIndependentVariables,chowIncidenceMap,aeval_X]
      change algebraMap (ChowNestedCoordinateRing m I) F
        (chowLastRowSplit m I (X (Fin.last m,j))) = _
      rw [chowLastRowSplit_X_last]

end
end CCDN
