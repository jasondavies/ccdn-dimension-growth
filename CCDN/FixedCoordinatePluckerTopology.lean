module

public import CCDN.CenterPluckerZariski
public import CCDN.BirationalCenterSubspace

/-! Centers contained in X0=0, as matrices with zero first column and as
subspaces with the topology induced from the Plücker topology. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology projectivePointZariskiTopology
  centerSubspacePluckerZariskiTopology

abbrev FixedCoordinateCenterMatrix (K : Type*) [Field K] (r n : ℕ) :=
  {x : Fin r × Fin (n + 1) → K //
    (∀ i j, j ∈ ({0} : Finset (Fin (n + 1))) → x (i,j) = 0) ∧
    LinearIndependent K (fun i : Fin r => fun j : Fin (n + 1) => x (i,j))}

def fixedCoordinateBirationalCenterLocus
    {K : Type*} [Field K] {n r s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    Set (FixedCoordinateCenterMatrix K r n) :=
  {x | IsBirationalMatrixCenter (projectiveClosureIdeal I) e
    (Matrix.of fun i j => x.val (i,j))}

abbrev FixedCoordinateCenterSubspace (K : Type*) [Field K] (r n : ℕ) :=
  {W : CenterSubspace K r (n + 1) // ∀ v ∈ W.val, v 0 = 0}

def fixedCoordinateMatrixSpan {K : Type*} [Field K] {r n : ℕ}
    (x : FixedCoordinateCenterMatrix K r n) : FixedCoordinateCenterSubspace K r n :=
  ⟨centerMatrixSpan ⟨x.val, x.property.2⟩, by
    have hle : Submodule.span K (Set.range (fun i : Fin r => fun j : Fin (n + 1) => x.val (i,j))) ≤
        (LinearMap.proj (0 : Fin (n + 1)) : (Fin (n + 1) → K) →ₗ[K] K).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact x.property.1 i 0 (Finset.mem_singleton_self _)
    exact fun v hv => hle hv⟩

theorem fixedCoordinateMatrixSpan_surjective
    {K : Type*} [Field K] {r n : ℕ} :
    Function.Surjective (fixedCoordinateMatrixSpan (K := K) (r := r) (n := n)) := by
  intro W
  obtain ⟨x, hx⟩ := centerMatrixSpan_surjective W.val
  have hz (i : Fin r) : x.val (i, 0) = 0 := by
    apply W.property (fun j => x.val (i,j))
    rw [← hx]
    exact Submodule.subset_span ⟨i, rfl⟩
  let y : FixedCoordinateCenterMatrix K r n :=
    ⟨x.val, fun i j hj => by simpa only [Finset.mem_singleton.mp hj] using hz i,
      x.property⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  exact hx

theorem fixedCoordinateMatrixSpan_continuous
    {K : Type*} [Field K] {r n : ℕ} :
    Continuous (fixedCoordinateMatrixSpan (K := K) (r := r) (n := n)) := by
  let forget : FixedCoordinateCenterMatrix K r n → IndependentCenterMatrix K r (n + 1) :=
    fun x => ⟨x.val, x.property.2⟩
  have hf : Continuous forget := continuous_subtype_val.subtype_mk _
  exact (centerMatrixSpan_plucker_continuous.comp hf).subtype_mk _

def fixedCoordinateBirationalSubspaceLocus
    {K : Type*} [Field K] {n r s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    Set (FixedCoordinateCenterSubspace K r n) :=
  Subtype.val ⁻¹' birationalCenterSubspaceLocus (projectiveClosureIdeal I) e

theorem fixedCoordinateBirationalSubspaceLocus_preimage
    {K : Type*} [Field K] {n r s : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (e : Fin (s + 2) ≃ (Fin (r + 1) ↪ Fin (n + 1))) :
    fixedCoordinateMatrixSpan ⁻¹' fixedCoordinateBirationalSubspaceLocus I e =
      fixedCoordinateBirationalCenterLocus I e := by
  ext x
  change centerMatrixSpan (⟨x.val, x.property.2⟩ : IndependentCenterMatrix K r (n + 1)) ∈
    birationalCenterSubspaceLocus (projectiveClosureIdeal I) e ↔ _
  change (⟨x.val, x.property.2⟩ : IndependentCenterMatrix K r (n + 1)) ∈
    centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus (projectiveClosureIdeal I) e ↔ _
  rw [birationalCenterSubspaceLocus_preimage]
  rfl

end
end CCDN
