/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Shortest lattice vectors outside a subspace

## Main results

* `ZLattice.exists_shortest_vector_notMem`: if a real subspace `U` of a finite-dimensional
  normed space does not contain the full-rank lattice `L`, some vector of `L` outside `U` has
  minimal norm among the vectors of `L` outside `U`. Iterating this gives the greedy
  successive-minima flag of `L`.
-/

@[expose] public section

namespace ZLattice

open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a real subspace `U` does not contain the full-rank lattice `L`, some lattice vector outside
`U` has minimal norm among all lattice vectors outside `U`. -/
theorem exists_shortest_vector_notMem
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

end ZLattice
