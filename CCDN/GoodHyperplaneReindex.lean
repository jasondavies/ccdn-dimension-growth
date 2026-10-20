module

public import CCDN.BoundedGoodHyperplane

/-! Transporting the constructed good hyperplane to coordinates suited to
the universal Noether family. No generic-section premise is introduced. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma graphHyperplaneRestriction_rename {K σ τ : Type*}
    [CommRing K] [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (a : τ → K) (f : MvPolynomial (Option σ) K) :
    rename e (graphHyperplaneRestriction (a ∘ e) f) =
      graphHyperplaneRestriction a (rename (Equiv.optionCongr e) f) := by
  have he : (rename e).toRingHom.comp
      (graphHyperplaneRestriction (a ∘ e)).toRingHom =
      (graphHyperplaneRestriction a).toRingHom.comp
        (rename (Equiv.optionCongr e)).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [graphHyperplaneRestriction]
    · intro i
      cases i with
      | none =>
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          graphHyperplaneRestriction, aeval_X, Option.elim_none, map_sum, map_mul,
          rename_C, rename_X, Function.comp_apply, Equiv.optionCongr_apply]
        exact e.sum_comp (fun j => C (a j) * X j)
      | some i => simp [graphHyperplaneRestriction]
  exact RingHom.congr_fun he f

/-- The already constructed bounded integer normal yields a
geometrically integral rational graph section in the double-Option coordinates. -/
theorem exists_geometrically_good_graph_reindexed {n : ℕ}
    (f : MvPolynomial (Option (Option (Fin (2 + n)))) ℤ)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree) :
    ∃ a : Option (Fin (2 + n)) → ℚ,
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ))
        (graphHyperplaneRestriction a (map (Int.castRingHom ℚ) f))) := by
  let e : Option (Fin (2 + n)) ≃ Fin (3 + n) :=
    (_root_.finSuccEquiv (2 + n)).symm.trans (finCongr (by omega))
  let F := rename (Equiv.optionCongr e) f
  have hFir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) F) := by
    rw [map_rename]
    exact (MulEquiv.irreducible_iff
      (f := (renameEquiv (AlgebraicClosure ℚ) (Equiv.optionCongr e)).toMulEquiv)).mpr hir
  have hFdeg : F.totalDegree = f.totalDegree := totalDegree_renameEquiv _ _
  obtain ⟨D,a,_,_,_,_,hgood⟩ := exists_bounded_geometrically_good_hyperplane F hFir (hFdeg ▸ hd)
  let α : Fin (3 + n) → ℚ := fun i => (a i : ℚ) / D
  refine ⟨α ∘ e, ?_⟩
  have he := congrArg (map (algebraMap ℚ (AlgebraicClosure ℚ)))
    (graphHyperplaneRestriction_rename e α (map (Int.castRingHom ℚ) f))
  rw [map_rename] at he
  apply (MulEquiv.irreducible_iff
    (f := (renameEquiv (AlgebraicClosure ℚ) e).toMulEquiv)).mp
  change Irreducible (rename e (map (algebraMap ℚ (AlgebraicClosure ℚ))
    (graphHyperplaneRestriction (α ∘ e) (map (Int.castRingHom ℚ) f))))
  rw [he]
  simpa only [F, map_rename] using hgood

end
end CCDN
