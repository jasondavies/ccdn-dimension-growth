module

public import CCDN.LatticePrescribedMinima
public import CCDN.LatticeMinimaProduct

/-! The product-of-lengths bound for a prescribed first lattice vector.
Each later vector is shortest outside the preceding span, and the covolume
bound for positive monotone flag thresholds applies. -/

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

end
end CCDN
