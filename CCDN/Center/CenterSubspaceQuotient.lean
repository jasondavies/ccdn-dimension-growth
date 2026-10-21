module

public import CCDN.Center.BirationalCenterLocus
/-! Fixed-dimensional linear subspaces, as the row spans of independent
center matrices. Their topology is the Zariski topology induced by Plücker
coordinates (`CenterPluckerZariski`). -/

@[expose] public section
namespace CCDN
noncomputable section
open Matrix Module

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

lemma centerMatrixSpan_eq_iff {K : Type*} [Field K] {r n : ℕ}
    (x y : IndependentCenterMatrix K r n) :
    centerMatrixSpan x = centerMatrixSpan y ↔
      Submodule.span K (Set.range (fun i : Fin r => fun j : Fin n => x.val (i,j))) =
      Submodule.span K (Set.range (fun i : Fin r => fun j : Fin n => y.val (i,j))) :=
  Subtype.ext_iff

end
end CCDN
