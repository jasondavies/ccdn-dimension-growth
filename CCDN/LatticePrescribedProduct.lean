module

public import CCDN.LatticePrescribedMinima
public import CCDN.LatticeMinimaProduct

/-! The product-of-lengths bound for a prescribed first lattice vector.
The construction uses genuine later minima and the proved covolume bound
for positive monotone flag thresholds. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem prescribed_greedy_lattice_basis_product_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {n : ℕ} {w : E} (b : Basis (Fin (n + 1)) ℝ E)
    (hb : IsPrescribedGreedyLatticeFamily L w b)
    {δ : ℝ} (hδ : 0 < δ) (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    (∏ i, ‖b i‖) ≤ (‖w‖ / δ) * (n + 1 : ℝ) ^ (n + 1) * ZLattice.covolume L := by
  obtain ⟨c, hflag⟩ := exists_orthonormal_basis_with_same_flag b
  have hprod := lattice_flag_minima_product_le (by omega : 0 < n + 1) L c
    (prescribedLatticeMinima b δ) (hb.minima_pos hδ) (hb.minima_mono hlower)
    (fun i x hx hxU => hb.minima_outside hlower i x hx (by rwa [← hflag i]))
  rw [prescribedLatticeMinima_prod b hb.2.1 hδ.ne']
  have hh := mul_le_mul_of_nonneg_left hprod (div_nonneg (norm_nonneg w) hδ.le)
  simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hh

/-- The shortest-outside-span property and product estimate hold for the
same constructed basis, allowing later arguments to use its last minimum. -/
theorem exists_prescribed_greedy_lattice_basis_norm_product_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    ∃ b : Basis (Fin (n + 1)) ℝ E,
      IsPrescribedGreedyLatticeFamily L w b ∧
      (∏ i, ‖b i‖) ≤ (‖w‖ / δ) * (n + 1 : ℝ) ^ (n + 1) * ZLattice.covolume L := by
  obtain ⟨b, hb⟩ := exists_prescribed_greedy_lattice_basis L w hw hw0 hn
  exact ⟨b, hb, prescribed_greedy_lattice_basis_product_le L b hb hδ hlower⟩

/-- A constructed real basis of lattice vectors, beginning with
any prescribed nonzero lattice vector. The only cost of prescribing it
is its length divided by the lower bound for all nonzero lattice lengths. -/
theorem exists_prescribed_lattice_basis_norm_product_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1)
    (δ : ℝ) (hδ : 0 < δ) (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    ∃ b : Basis (Fin (n + 1)) ℝ E,
      b 0 = w ∧ (∀ i, b i ∈ L) ∧ (∀ i, δ ≤ ‖b i‖) ∧
      (∏ i, ‖b i‖) ≤ (‖w‖ / δ) * (n + 1 : ℝ) ^ (n + 1) * ZLattice.covolume L := by
  obtain ⟨b, hb⟩ := exists_prescribed_greedy_lattice_basis L w hw hw0 hn
  exact ⟨b, hb.2.1, hb.2.2.1, fun i => hlower (b i) (hb.2.2.1 i) (b.ne_zero i),
    prescribed_greedy_lattice_basis_product_le L b hb hδ hlower⟩

end
end CCDN
