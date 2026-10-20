module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Data.Set.Finite.Lemmas

/-! Greedy shortest independent lattice vectors. The minima are attained
in the actual lattice, and each vector minimizes the norm outside the span
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

/-- Each vector is shortest among the lattice vectors outside the preceding
flag. Linear independence is included explicitly. -/
def IsGreedyLatticeFamily (L : Submodule ℤ E) {k : ℕ} (v : Fin k → E) : Prop :=
  LinearIndependent ℝ v ∧
    (∀ i, v i ∈ L) ∧
    ∀ i x, x ∈ L → x ∉ Submodule.span ℝ (v '' Set.Iio i) → ‖v i‖ ≤ ‖x‖

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem snoc_image_Iio_castSucc {k : ℕ} (v : Fin k → E) (x : E) (i : Fin k) :
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem snoc_image_Iio_last {k : ℕ} (v : Fin k → E) (x : E) :
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

omit [FiniteDimensional ℝ E] in
theorem IsGreedyLatticeFamily.snoc
    {L : Submodule ℤ E} {k : ℕ} {v : Fin k → E}
    (hv : IsGreedyLatticeFamily L v) {x : E} (hx : x ∈ L)
    (hxU : x ∉ Submodule.span ℝ (Set.range v))
    (hmin : ∀ y, y ∈ L → y ∉ Submodule.span ℝ (Set.range v) → ‖x‖ ≤ ‖y‖) :
    IsGreedyLatticeFamily L (Fin.snoc v x) := by
  refine ⟨hv.1.finSnoc hxU, ?_, ?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hv.2.1 j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last, snoc_image_Iio_last] using hmin
    · simpa only [Fin.snoc_castSucc, snoc_image_Iio_castSucc] using hv.2.2 j

theorem exists_greedy_lattice_family
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (k : ℕ) (hk : k ≤ Module.finrank ℝ E) :
    ∃ v : Fin k → E, IsGreedyLatticeFamily L v := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, linearIndependent_empty_type, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih (by omega)
    have hU : Submodule.span ℝ (Set.range v) ≠ ⊤ := by
      intro he
      have hdim := finrank_span_eq_card hv.1
      rw [he, finrank_top, Fintype.card_fin] at hdim
      omega
    obtain ⟨x, hx, hxU, hmin⟩ := exists_shortest_lattice_vector_outside L _ hU
    exact ⟨Fin.snoc v x, hv.snoc hx hxU hmin⟩

omit [FiniteDimensional ℝ E] in
theorem IsGreedyLatticeFamily.norm_mono
    {L : Submodule ℤ E} {k : ℕ} {v : Fin k → E}
    (hv : IsGreedyLatticeFamily L v) :
    Monotone (fun i => ‖v i‖) := by
  intro i j hij
  apply hv.2.2 i (v j) (hv.2.1 j)
  exact hv.1.notMem_span_image (not_lt_of_ge hij)

/-- A real basis formed by actual successive lattice minima, with no
chosen independent family or basis supplied as an input. -/
theorem exists_greedy_lattice_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E, IsGreedyLatticeFamily L b := by
  obtain ⟨v, hv⟩ := exists_greedy_lattice_family L (Module.finrank ℝ E) le_rfl
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.1 (Fintype.card_fin _)
  exact ⟨b, by simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv⟩

end
end CCDN
