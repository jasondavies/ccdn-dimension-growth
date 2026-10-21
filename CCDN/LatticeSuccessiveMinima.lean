module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Data.Set.Finite.Lemmas

/-! Greedy shortest independent lattice vectors. The minima are attained
in the lattice, and each vector minimizes the norm outside the span
of its predecessors. This supplies the flag used in a product-of-minima
estimate. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_shortest_lattice_vector_outside
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (U : Submodule ℝ E) (hU : U ≠ ⊤) :
    ∃ v : E, v ∈ L ∧ v ∉ U ∧
      ∀ x : E, x ∈ L → x ∉ U → ‖v‖ ≤ ‖x‖ := by
  classical
  have hex : ∃ x : E, x ∈ L ∧ x ∉ U := by
    by_contra! h
    have hh : Submodule.span ℝ (L : Set E) ≤ U := Submodule.span_le.mpr h
    rw [IsZLattice.span_top] at hh
    exact hU (top_le_iff.mp hh)
  obtain ⟨x₀, hx₀, hx₀U⟩ := hex
  let S : Set E := {x | x ∈ L ∧ x ∉ U ∧ ‖x‖ ≤ ‖x₀‖}
  have hfinite : S.Finite := by
    have : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
    have hf : (Metric.closedBall 0 ‖x₀‖ ∩ (L : Set E)).Finite :=
      Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
        Metric.isBounded_closedBall L.toAddSubgroup.isClosed_of_discreteTopology
    exact hf.subset fun x hx => ⟨by simpa using hx.2.2, hx.1⟩
  obtain ⟨v, hv, hmin⟩ := Set.exists_min_image S norm hfinite ⟨x₀, hx₀, hx₀U, le_rfl⟩
  refine ⟨v, hv.1, hv.2.1, ?_⟩
  intro x hx hxU
  by_cases hh : ‖x‖ ≤ ‖x₀‖
  · exact hmin x ⟨hx, hxU, hh⟩
  · exact hv.2.2.trans (le_of_not_ge hh)

theorem snoc_image_Iio_castSucc {α : Type*} {k : ℕ} (v : Fin k → α) (x : α) (i : Fin k) :
    Fin.snoc v x '' Set.Iio i.castSucc = v '' Set.Iio i := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hjk : j.val < k := lt_trans hj i.isLt
    let j' : Fin k := ⟨j.val, hjk⟩
    have he : j = j'.castSucc := rfl
    refine ⟨j', hj, ?_⟩
    rw [he, Fin.snoc_castSucc]
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j.castSucc, hj, Fin.snoc_castSucc _ _ _⟩

theorem snoc_image_Iio_last {α : Type*} {k : ℕ} (v : Fin k → α) (x : α) :
    Fin.snoc v x '' Set.Iio (Fin.last k) = Set.range v := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    let j' : Fin k := ⟨j.val, hj⟩
    have he : j = j'.castSucc := rfl
    refine ⟨j', ?_⟩
    rw [he, Fin.snoc_castSucc]
  · rintro ⟨j, rfl⟩
    exact ⟨j.castSucc, j.isLt, Fin.snoc_castSucc _ _ _⟩

end
end CCDN
