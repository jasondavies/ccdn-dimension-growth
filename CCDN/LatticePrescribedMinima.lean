module

public import CCDN.LatticeSuccessiveMinima

/-! A lattice basis with a prescribed nonzero first vector. Every later
vector is shortest outside the previous span. A given global
lower bound replaces the first vector's norm in the monotone thresholds. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Only the first vector is prescribed; all subsequent minima are attained
in the lattice outside the preceding flag. -/
def IsPrescribedGreedyLatticeFamily (L : Submodule ℤ E) (w : E)
    {k : ℕ} (v : Fin (k + 1) → E) : Prop :=
  LinearIndependent ℝ v ∧ v 0 = w ∧ (∀ i, v i ∈ L) ∧
    ∀ i, i ≠ 0 → ∀ x, x ∈ L → x ∉ span ℝ (v '' Set.Iio i) → ‖v i‖ ≤ ‖x‖

omit [FiniteDimensional ℝ E] in
theorem IsPrescribedGreedyLatticeFamily.snoc
    {L : Submodule ℤ E} {w : E} {k : ℕ} {v : Fin (k + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {x : E} (hx : x ∈ L)
    (hxU : x ∉ span ℝ (Set.range v))
    (hmin : ∀ y, y ∈ L → y ∉ span ℝ (Set.range v) → ‖x‖ ≤ ‖y‖) :
    IsPrescribedGreedyLatticeFamily L w (Fin.snoc v x) := by
  refine ⟨hv.1.finSnoc hxU, ?_, ?_, ?_⟩
  · simpa using hv.2.1
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using hx
    · simpa using hv.2.2.1 j
  · intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro _
      simpa only [Fin.snoc_last, snoc_image_Iio_last] using hmin
    · intro hj
      have hj0 : j ≠ 0 := by intro hz; apply hj; simp [hz]
      simpa only [Fin.snoc_castSucc, snoc_image_Iio_castSucc] using hv.2.2.2 j hj0

/-- Prescribed-first greedy independent lattice vectors of every possible
length. -/
theorem exists_prescribed_greedy_lattice_family
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    (k : ℕ) (hk : k + 1 ≤ Module.finrank ℝ E) :
    ∃ v : Fin (k + 1) → E, IsPrescribedGreedyLatticeFamily L w v := by
  induction k with
  | zero =>
    let : Subsingleton (Fin (0 + 1)) := Fin.subsingleton_iff_le_one.mpr (by omega)
    refine ⟨fun _ => w, (linearIndependent_subsingleton_index_iff _).mpr (fun _ => hw0), rfl, fun _ => hw, ?_⟩
    intro i hi
    exact False.elim (hi (Subsingleton.elim _ _))
  | succ k ih =>
    obtain ⟨v, hv⟩ := ih (by omega)
    have hU : span ℝ (Set.range v) ≠ ⊤ := by
      intro he
      have hdim := finrank_span_eq_card hv.1
      rw [he, finrank_top, Fintype.card_fin] at hdim
      omega
    obtain ⟨x, hx, hxU, hmin⟩ := exists_shortest_lattice_vector_outside L _ hU
    exact ⟨Fin.snoc v x, hv.snoc hx hxU hmin⟩

theorem exists_prescribed_greedy_lattice_basis
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (w : E) (hw : w ∈ L) (hw0 : w ≠ 0)
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1) :
    ∃ b : Basis (Fin (n + 1)) ℝ E, IsPrescribedGreedyLatticeFamily L w b := by
  obtain ⟨v, hv⟩ := exists_prescribed_greedy_lattice_family L w hw hw0 n (by omega)
  let b := basisOfLinearIndependentOfCardEqFinrank' v hv.1 (by simpa using hn.symm)
  exact ⟨b, by simpa only [b, coe_basisOfLinearIndependentOfCardEqFinrank'] using hv⟩

omit [FiniteDimensional ℝ E] in
def prescribedLatticeMinima {n : ℕ} (v : Fin (n + 1) → E) (δ : ℝ) : Fin (n + 1) → ℝ :=
  fun i => if i = 0 then δ else ‖v i‖

omit [FiniteDimensional ℝ E] in
theorem IsPrescribedGreedyLatticeFamily.minima_pos
    {L : Submodule ℤ E} {w : E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {δ : ℝ} (hδ : 0 < δ) :
    ∀ i, 0 < prescribedLatticeMinima v δ i := by
  intro i
  unfold prescribedLatticeMinima
  split_ifs
  · exact hδ
  · exact norm_pos_iff.mpr (hv.1.ne_zero i)

omit [FiniteDimensional ℝ E] in
theorem IsPrescribedGreedyLatticeFamily.minima_mono
    {L : Submodule ℤ E} {w : E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {δ : ℝ}
    (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    Monotone (prescribedLatticeMinima v δ) := by
  intro i j hij
  by_cases hi : i = 0
  · by_cases hj : j = 0
    · simp [prescribedLatticeMinima, hi, hj]
    · simpa [prescribedLatticeMinima, hi, hj] using
        hlower (v j) (hv.2.2.1 j) (hv.1.ne_zero j)
  · have hj : j ≠ 0 := by intro hz; apply hi; exact le_antisymm (hz ▸ hij) (Fin.zero_le i)
    simp only [prescribedLatticeMinima, ite_eq_right hi, ite_eq_right hj]
    exact hv.2.2.2 i hi (v j) (hv.2.2.1 j)
      (hv.1.notMem_span_image (not_lt_of_ge hij))

omit [FiniteDimensional ℝ E] in
theorem IsPrescribedGreedyLatticeFamily.minima_outside
    {L : Submodule ℤ E} {w : E} {n : ℕ} {v : Fin (n + 1) → E}
    (hv : IsPrescribedGreedyLatticeFamily L w v) {δ : ℝ}
    (hlower : ∀ x, x ∈ L → x ≠ 0 → δ ≤ ‖x‖) :
    ∀ i x, x ∈ L → x ∉ span ℝ (v '' Set.Iio i) → prescribedLatticeMinima v δ i ≤ ‖x‖ := by
  intro i x hx hxU
  by_cases hi : i = 0
  · rw [prescribedLatticeMinima, ite_eq_left hi]
    apply hlower x hx
    intro hz
    exact hxU (hz ▸ Submodule.zero_mem _)
  · rw [prescribedLatticeMinima, ite_eq_right hi]
    exact hv.2.2.2 i hi x hx hxU

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
theorem prescribedLatticeMinima_prod {n : ℕ} (v : Fin (n + 1) → E)
    {w : E} (hw : v 0 = w) {δ : ℝ} (hδ : δ ≠ 0) :
    (∏ i, ‖v i‖) = (‖w‖ / δ) * ∏ i, prescribedLatticeMinima v δ i := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
  simp only [prescribedLatticeMinima, Fin.succ_ne_zero, ↓reduceIte, hw]
  rw [← mul_assoc, div_mul_cancel₀ _ hδ]

end
end CCDN
