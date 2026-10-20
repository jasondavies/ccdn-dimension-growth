module

public import AffineCurveCounting.BirationalCenterLocus

/-! Actual fixed-dimensional linear subspaces as the quotient of independent
center matrices by equality of row spans. The topology is explicitly the
quotient topology; no identification with a Pluecker embedding is asserted. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open Matrix Module
attribute [local instance] affinePointZariskiTopology

abbrev CenterSubspace (K : Type*) [Field K] (r n : ℕ) :=
  {W : Submodule K (Fin n → K) // Module.finrank K W = r}

def centerMatrixSpan {K : Type*} [Field K] {r n : ℕ}
    (x : IndependentCenterMatrix K r n) : CenterSubspace K r n :=
  ⟨Submodule.span K (Set.range (fun i : Fin r => fun j : Fin n => x.val (i,j))),
    by simpa only [Fintype.card_fin] using finrank_span_eq_card x.property⟩

lemma centerMatrixSpan_surjective {K : Type*} [Field K] {r n : ℕ} :
    Function.Surjective (centerMatrixSpan (K := K) (r := r) (n := n)) := by
  intro W
  let b := Module.finBasisOfFinrankEq K W.val W.property
  let v : Fin r → Fin n → K := fun i => (b i).val
  have hv : LinearIndependent K v :=
    b.linearIndependent.map' W.val.subtype (Submodule.ker_subtype W.val)
  have hspan : Submodule.span K (Set.range v) = W.val := by
    have hh := congrArg (Submodule.map W.val.subtype) b.span_eq
    simpa only [Submodule.map_span,← Set.range_comp,Function.comp_def,
      Submodule.map_top,Submodule.range_subtype,Submodule.subtype_apply,v] using hh
  refine ⟨⟨fun q => v q.1 q.2,hv⟩,?_⟩
  apply Subtype.ext
  exact hspan

@[instance_reducible]
def centerSubspaceQuotientTopology (K : Type*) [Field K] (r n : ℕ) :
    TopologicalSpace (CenterSubspace K r n) :=
  TopologicalSpace.coinduced centerMatrixSpan inferInstance

attribute [local instance] centerSubspaceQuotientTopology

lemma centerMatrixSpan_isQuotientMap {K : Type*} [Field K] {r n : ℕ} :
    Topology.IsQuotientMap (centerMatrixSpan (K := K) (r := r) (n := n)) :=
  ⟨⟨rfl⟩,centerMatrixSpan_surjective⟩

lemma centerMatrixSpan_eq_iff {K : Type*} [Field K] {r n : ℕ}
    (x y : IndependentCenterMatrix K r n) :
    centerMatrixSpan x = centerMatrixSpan y ↔
      Submodule.span K (Set.range (fun i : Fin r => fun j : Fin n => x.val (i,j))) =
      Submodule.span K (Set.range (fun i : Fin r => fun j : Fin n => y.val (i,j))) :=
  Subtype.ext_iff

/-- An invariant open matrix condition descends to an open subset of the
actual space of subspaces, with its quotient topology. -/
theorem center_subspace_image_isOpen
    {K : Type*} [Field K] {r n : ℕ}
    (S : Set (IndependentCenterMatrix K r n)) (hS : IsOpen S)
    (hsat : ∀ x y, centerMatrixSpan x = centerMatrixSpan y → (x ∈ S ↔ y ∈ S)) :
    IsOpen (centerMatrixSpan '' S) := by
  have he : centerMatrixSpan ⁻¹' (centerMatrixSpan '' S) = S := by
    ext x
    constructor
    · rintro ⟨y,hy,heq⟩
      exact (hsat y x heq).mp hy
    · intro hx
      exact ⟨x,hx,rfl⟩
  apply centerMatrixSpan_isQuotientMap.isCoinducing.isOpen_preimage.mp
  rwa [he]

theorem center_subspace_image_dense
    {K : Type*} [Field K] {r n : ℕ}
    (S : Set (IndependentCenterMatrix K r n)) (hS : Dense S) :
    Dense (centerMatrixSpan '' S) :=
  centerMatrixSpan_surjective.denseRange.dense_image
    centerMatrixSpan_isQuotientMap.continuous hS

end
end AffineCurveCounting
