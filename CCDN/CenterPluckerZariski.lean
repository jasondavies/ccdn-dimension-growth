module

public import CCDN.CenterPluckerCoordinates

/-! Zariski topology defined by homogeneous projective equations, and its
induced topology on actual center subspaces under the injective Plücker map.
The row-span map from independent matrices is continuous for this topology.
No identification with the row-span quotient topology is assumed. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Matrix
attribute [local instance] affinePointZariskiTopology

def projectiveHomogeneousPrincipalOpen {K σ : Type*} [Field K]
    (f : MvPolynomial σ K) : Set (Projectivization K (σ → K)) :=
  {p | eval p.rep f ≠ 0}

@[instance_reducible]
def projectivePointZariskiTopology (K σ : Type*) [Field K] :
    TopologicalSpace (Projectivization K (σ → K)) :=
  TopologicalSpace.generateFrom
    {U | ∃ (d : ℕ) (f : MvPolynomial σ K),
      f.IsHomogeneous d ∧ U = projectiveHomogeneousPrincipalOpen f}

attribute [local instance] projectivePointZariskiTopology

theorem projectiveHomogeneousPrincipalOpen_isOpen
    {K σ : Type*} [Field K] {d : ℕ}
    (f : MvPolynomial σ K) (hf : f.IsHomogeneous d) :
    IsOpen (projectiveHomogeneousPrincipalOpen f) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨d, f, hf, rfl⟩

theorem independentCenterPlucker_preimage_principalOpen
    {K : Type*} [Field K] {r n d : ℕ}
    (f : MvPolynomial (Fin r ↪ Fin n) K) (hf : f.IsHomogeneous d) :
    independentCenterPlucker ⁻¹' projectiveHomogeneousPrincipalOpen f =
      {x : IndependentCenterMatrix K r n | eval x.val (centerMinorPolynomial f) ≠ 0} := by
  ext x
  change (eval (independentCenterPlucker x).rep f ≠ 0) ↔
    eval x.val (centerMinorPolynomial f) ≠ 0
  rw [eval_centerMinorPolynomial]
  exact not_congr (homogeneous_eval_independentCenterPlucker f hf x)

theorem independentCenterPlucker_continuous
    {K : Type*} [Field K] {r n : ℕ} :
    Continuous (independentCenterPlucker (K := K) (r := r) (n := n)) := by
  apply continuous_generateFrom_iff.mpr
  rintro U ⟨d, f, hf, rfl⟩
  rw [independentCenterPlucker_preimage_principalOpen f hf]
  exact (affine_polynomial_nonzero_set_open (centerMinorPolynomial f)).preimage
    continuous_subtype_val

@[instance_reducible]
def centerSubspacePluckerZariskiTopology (K : Type*) [Field K] (r n : ℕ) :
    TopologicalSpace (CenterSubspace K r n) :=
  TopologicalSpace.induced centerSubspacePlucker inferInstance

attribute [local instance] centerSubspacePluckerZariskiTopology

theorem centerSubspacePlucker_isEmbedding
    {K : Type*} [Field K] {r n : ℕ} :
    Topology.IsEmbedding (centerSubspacePlucker (K := K) (r := r) (n := n)) :=
  ⟨⟨rfl⟩, centerSubspacePlucker_injective⟩

theorem centerMatrixSpan_plucker_continuous
    {K : Type*} [Field K] {r n : ℕ} :
    Continuous (centerMatrixSpan (K := K) (r := r) (n := n)) := by
  apply continuous_induced_rng.mpr
  have he : centerSubspacePlucker ∘ (centerMatrixSpan (K := K) (r := r) (n := n)) =
      independentCenterPlucker := by
    funext x
    exact centerSubspacePlucker_matrixSpan x
  rw [he]
  exact independentCenterPlucker_continuous

def centerPluckerPrincipalOpen {K : Type*} [Field K] {r n : ℕ}
    (f : MvPolynomial (Fin r ↪ Fin n) K) : Set (CenterSubspace K r n) :=
  centerSubspacePlucker ⁻¹' projectiveHomogeneousPrincipalOpen f

theorem centerPluckerPrincipalOpen_isOpen
    {K : Type*} [Field K] {r n d : ℕ}
    (f : MvPolynomial (Fin r ↪ Fin n) K) (hf : f.IsHomogeneous d) :
    IsOpen (centerPluckerPrincipalOpen f) :=
  (projectiveHomogeneousPrincipalOpen_isOpen f hf).preimage
    centerSubspacePlucker_isEmbedding.continuous

theorem centerMatrixSpan_preimage_pluckerPrincipalOpen
    {K : Type*} [Field K] {r n d : ℕ}
    (f : MvPolynomial (Fin r ↪ Fin n) K) (hf : f.IsHomogeneous d) :
    centerMatrixSpan ⁻¹' centerPluckerPrincipalOpen f =
      {x : IndependentCenterMatrix K r n | eval x.val (centerMinorPolynomial f) ≠ 0} := by
  have he : centerSubspacePlucker ∘ (centerMatrixSpan (K := K) (r := r) (n := n)) =
      independentCenterPlucker := by
    funext x
    exact centerSubspacePlucker_matrixSpan x
  change (centerSubspacePlucker ∘ centerMatrixSpan) ⁻¹' projectiveHomogeneousPrincipalOpen f = _
  rw [he]
  exact independentCenterPlucker_preimage_principalOpen f hf

/-- Density descends to the Zariski topology induced by actual Plücker
coordinates, not only to the previously defined row-span quotient topology. -/
theorem center_subspace_image_plucker_dense
    {K : Type*} [Field K] {r n : ℕ}
    (S : Set (IndependentCenterMatrix K r n)) (hS : Dense S) :
    Dense (centerMatrixSpan '' S) :=
  centerMatrixSpan_surjective.denseRange.dense_image
    centerMatrixSpan_plucker_continuous hS

theorem centerPluckerPrincipalOpen_dense
    {K : Type*} [Field K] [Infinite K] {r n d : ℕ}
    (f : MvPolynomial (Fin r ↪ Fin n) K) (hf : f.IsHomogeneous d)
    (x : IndependentCenterMatrix K r n)
    (hx : eval x.val (centerMinorPolynomial f) ≠ 0) :
    Dense (centerPluckerPrincipalOpen f) := by
  obtain ⟨c, hc, _⟩ := exists_nonzero_minor_of_independent_rows
    (Matrix.of fun i j => x.val (i,j)) x.property
  have hne : centerMinorPolynomial f ≠ 0 := by
    intro hz
    exact hx (by rw [hz, map_zero])
  have hd := full_row_rank_polynomial_locus_dense_subspace ⟨c, hc⟩
    (centerMinorPolynomial f) hne
  have he : centerMatrixSpan '' {y : IndependentCenterMatrix K r n |
      eval y.val (centerMinorPolynomial f) ≠ 0} = centerPluckerPrincipalOpen f := by
    rw [← centerMatrixSpan_preimage_pluckerPrincipalOpen f hf]
    exact Set.image_preimage_eq _ centerMatrixSpan_surjective
  rw [← he]
  exact center_subspace_image_plucker_dense _ hd

end
end CCDN
