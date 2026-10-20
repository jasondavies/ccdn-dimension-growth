module

public import CCDN.LatticeMinimaFlag
public import CCDN.LatticeSeparatedVolume
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! A uniform product-of-minima bound from Blichfeldt's principle.
The constant n^n is sufficient for the number-field lattice application.
No successive-minima theorem is assumed. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Any positive monotone sequence of flag minima has product at
most n^n times the lattice covolume. -/
theorem lattice_flag_minima_product_le
    {n : ℕ} (hn : 0 < n) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (c : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (hpos : ∀ i, 0 < a i) (hmono : Monotone a)
    (hminimum : ∀ i x, x ∈ L → x ∉ Submodule.span ℝ (c '' Set.Iio i) → a i ≤ ‖x‖) :
    ∏ i, a i ≤ (n : ℝ) ^ n * ZLattice.covolume L := by
  classical
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let r : Fin n → ℝ := fun i => a i / n
  have hr (i) : 0 < r i := div_pos (hpos i) hnR
  let u := c.toBasis.unitsSMul (fun i => Units.mk0 (r i) (hr i).ne')
  have hrepr (x : E) (i : Fin n) :
      c.toBasis.repr x i = r i * u.repr x i := by
    simp only [u, Basis.repr_unitsSMul, Units.smul_def, Units.val_inv_eq_inv_val,
      Units.val_mk0, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (hr i).ne', one_mul]
  have hcoord (x : E) (hx : x ∈ ZSpan.fundamentalDomain u) (i : Fin n) :
      0 ≤ c.toBasis.repr x i ∧ c.toBasis.repr x i < r i := by
    have hi := (ZSpan.mem_fundamentalDomain u).mp hx i
    rw [hrepr]
    exact ⟨mul_nonneg (hr i).le hi.1, by simpa using (mul_lt_mul_of_pos_left hi.2 (hr i))⟩
  have hsep : ∀ x ∈ ZSpan.fundamentalDomain u,
      ∀ y ∈ ZSpan.fundamentalDomain u, x - y ∈ L → x = y := by
    intro x hx y hy hxy
    apply sub_eq_zero.mp
    apply lattice_flag_coordinate_box_zero hn L c a hpos hmono hminimum hxy
    intro i
    have hxi := hcoord x hx i
    have hyi := hcoord y hy i
    rw [map_sub, Finsupp.sub_apply]
    apply abs_lt.mpr
    change -(r i) < _ ∧ _ < r i
    constructor <;> linarith
  have hbound := lattice_separated_measure_le L volume
    (ZSpan.fundamentalDomain_measurableSet u) hsep
  have hunit : volume.real (ZSpan.fundamentalDomain c.toBasis) = 1 := by
    rw [measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped c.toBasis volume)]
    change (volume (parallelepiped c)).toReal = 1
    rw [c.volume_parallelepiped, ENNReal.toReal_one]
  have hvol : volume.real (ZSpan.fundamentalDomain u) =
      (∏ i, a i) / (n : ℝ) ^ n := by
    rw [ZSpan.measureReal_fundamentalDomain u volume c.toBasis]
    rw [hunit, mul_one]
    change |c.toBasis.det (c.toBasis.unitsSMul _)| = _
    rw [Basis.det_unitsSMul_self]
    simp only [Units.val_mk0]
    rw [abs_of_pos (Finset.prod_pos (fun i _ => hr i))]
    simp only [r, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hvol] at hbound
  exact (div_le_iff₀ (pow_pos hnR n)).mp hbound |>.trans_eq (mul_comm _ _)

/-- The product of the lengths of a greedy lattice basis is
uniformly controlled by the covolume. -/
theorem greedy_lattice_basis_product_le
    {n : ℕ} (hn : 0 < n) (L : Submodule ℤ E)
    [DiscreteTopology L] [IsZLattice ℝ L]
    (b : Basis (Fin n) ℝ E) (hb : IsGreedyLatticeFamily L b) :
    ∏ i, ‖b i‖ ≤ (n : ℝ) ^ n * ZLattice.covolume L := by
  obtain ⟨c, hflag⟩ := exists_orthonormal_basis_with_same_flag b
  apply lattice_flag_minima_product_le hn L c (fun i => ‖b i‖)
    (fun i => norm_pos_iff.mpr (b.ne_zero i)) hb.norm_mono
  intro i x hx hxU
  exact hb.2.2 i x hx (by rwa [← hflag i])

/-- Construct a complete independent family in the lattice and
prove the product bound, without a supplied family or minima hypothesis. -/
theorem exists_lattice_basis_norm_product_le
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (hn : 0 < Module.finrank ℝ E) :
    ∃ b : Basis (Fin (Module.finrank ℝ E)) ℝ E,
      (∀ i, b i ∈ L) ∧
      (∏ i, ‖b i‖) ≤ (Module.finrank ℝ E : ℝ) ^ Module.finrank ℝ E *
        ZLattice.covolume L := by
  obtain ⟨b, hb⟩ := exists_greedy_lattice_basis L
  exact ⟨b, hb.2.1, greedy_lattice_basis_product_le hn L b hb⟩

end
end CCDN
