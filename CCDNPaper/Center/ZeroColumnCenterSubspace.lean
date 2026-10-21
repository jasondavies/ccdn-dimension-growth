/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDNPaper.Center.BirationalCenterSubspace
public import CCDNPaper.Center.PluckerZariski

/-! Centers with prescribed zero columns, as matrices and as subspaces with
the topology induced from the Plücker topology. Centers contained in X0=0
are the case of the zero column set `{0}`. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology projectivePointZariskiTopology
  centerSubspacePluckerZariskiTopology

/-- Independent center matrices whose columns in `S` vanish. -/
abbrev ZeroColumnCenterMatrix (K : Type*) [Field K] (r n : ℕ) (S : Finset (Fin n)) :=
  {x : Fin r × Fin n → K //
    (∀ i j, j ∈ S → x (i,j) = 0) ∧ LinearIndependent K (fun i : Fin r => fun j : Fin n => x (i,j))}

/-- Center subspaces on which the coordinates in `S` vanish. -/
abbrev ZeroColumnCenterSubspace (K : Type*) [Field K] (r n : ℕ) (S : Finset (Fin n)) :=
  {W : CenterSubspace K r n // ∀ v ∈ W.val, ∀ j ∈ S, v j = 0}

/-- Independent `r × (n + 1)` center matrices whose column `0` vanishes, so that the spanned
center lies in the hyperplane `X 0 = 0`. -/
abbrev FixedCoordinateCenterMatrix (K : Type*) [Field K] (r n : ℕ) :=
  ZeroColumnCenterMatrix K r (n + 1) {0}

/-- Center subspaces of dimension `r` in `Fin (n + 1) → K` on which the coordinate `0` vanishes,
that is, centers contained in the hyperplane `X 0 = 0`. -/
abbrev FixedCoordinateCenterSubspace (K : Type*) [Field K] (r n : ℕ) :=
  ZeroColumnCenterSubspace K r (n + 1) {0}

/-- The row span of an independent center matrix with zero columns `S`, as a center subspace on
which the coordinates in `S` vanish. -/
def zeroColumnMatrixSpan {K : Type*} [Field K] {r n : ℕ} {S : Finset (Fin n)}
    (x : ZeroColumnCenterMatrix K r n S) : ZeroColumnCenterSubspace K r n S :=
  ⟨centerMatrixSpan ⟨x.val, x.property.2⟩, by
    intro v hv j hj
    have hle : Submodule.span K (Set.range (fun i : Fin r => fun j : Fin n => x.val (i,j))) ≤
        (LinearMap.proj j : (Fin n → K) →ₗ[K] K).ker := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact x.property.1 i j hj
    exact hle hv⟩

/-- Every center subspace on which the coordinates in `S` vanish is the row span of an independent
center matrix with zero columns `S`. -/
theorem zeroColumnMatrixSpan_surjective
    {K : Type*} [Field K] {r n : ℕ} {S : Finset (Fin n)} :
    Function.Surjective (zeroColumnMatrixSpan (K := K) (r := r) (S := S)) := by
  intro W
  obtain ⟨x, hx⟩ := centerMatrixSpan_surjective W.val
  have hz (i : Fin r) (j : Fin n) (hj : j ∈ S) : x.val (i, j) = 0 := by
    apply W.property (fun j => x.val (i,j)) _ j hj
    rw [← hx]
    exact Submodule.subset_span ⟨i, rfl⟩
  exact ⟨⟨x.val, hz, x.property⟩, Subtype.ext hx⟩

/-- Taking the row span of a matrix with zero columns `S` is continuous for the Zariski topology on
matrices and the Plücker topology on subspaces. -/
theorem zeroColumnMatrixSpan_continuous
    {K : Type*} [Field K] {r n : ℕ} {S : Finset (Fin n)} :
    Continuous (zeroColumnMatrixSpan (K := K) (r := r) (S := S)) := by
  let forget : ZeroColumnCenterMatrix K r n S → IndependentCenterMatrix K r n :=
    fun x => ⟨x.val, x.property.2⟩
  have hf : Continuous forget := continuous_subtype_val.subtype_mk _
  exact (centerMatrixSpan_plucker_continuous.comp hf).subtype_mk _

/-- The center matrices with vanishing column `0` that are birational centers for the projective
closure of the affine prime ideal `I`. -/
def fixedCoordinateBirationalCenterLocus
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    Set (FixedCoordinateCenterMatrix K r n) :=
  {x | IsBirationalMatrixCenter (projectiveClosureIdeal I) (Matrix.of fun i j => x.val (i,j))}

/-- The center subspaces in the hyperplane `X 0 = 0` that are birational centers for the
projective closure of the affine prime ideal `I`. -/
def fixedCoordinateBirationalSubspaceLocus
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    Set (FixedCoordinateCenterSubspace K r n) :=
  Subtype.val ⁻¹' birationalCenterSubspaceLocus (projectiveClosureIdeal I)

/-- A center matrix with vanishing column `0` is a birational center for the projective closure of
`I` exactly when its row span is a birational center subspace. -/
theorem fixedCoordinateBirationalSubspaceLocus_preimage
    {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    zeroColumnMatrixSpan ⁻¹' fixedCoordinateBirationalSubspaceLocus (r := r) I =
      fixedCoordinateBirationalCenterLocus (r := r) I := by
  ext x
  change (⟨x.val, x.property.2⟩ : IndependentCenterMatrix K r (n + 1)) ∈
    centerMatrixSpan ⁻¹' birationalCenterSubspaceLocus (projectiveClosureIdeal I) ↔ _
  rw [birationalCenterSubspaceLocus_preimage]
  rfl

end
end CCDN
