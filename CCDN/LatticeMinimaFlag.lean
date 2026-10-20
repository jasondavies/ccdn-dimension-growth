module

public import CCDN.LatticeSuccessiveMinima

/-! An orthonormal flag adapted to actual greedy lattice vectors. A small
coordinate box in this flag contains no nonzero lattice vector. -/

@[expose] public section
namespace CCDN
noncomputable section
open Module Submodule InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_orthonormal_basis_with_same_flag {n : ℕ}
    (b : Basis (Fin n) ℝ E) :
    ∃ c : OrthonormalBasis (Fin n) ℝ E, ∀ i,
      Submodule.span ℝ (c '' Set.Iio i) = Submodule.span ℝ (b '' Set.Iio i) := by
  have hdim : Module.finrank ℝ E = Fintype.card (Fin n) := Module.finrank_eq_card_basis b
  let c := gramSchmidtOrthonormalBasis hdim b
  have hc : (c : Fin n → E) = gramSchmidtNormed ℝ b := by
    funext i
    apply gramSchmidtOrthonormalBasis_apply
    intro he
    have hn := gramSchmidtNormed_unit_length i b.linearIndependent
    rw [he, norm_zero] at hn
    norm_num at hn
  refine ⟨c, fun i => ?_⟩
  rw [hc, span_gramSchmidtNormed, span_gramSchmidt_Iio]

omit [FiniteDimensional ℝ E] in
/-- With side lengths equal to the flag minima divided by dimension,
the open symmetric coordinate box has no nonzero lattice vector. -/
theorem lattice_flag_coordinate_box_zero
    {n : ℕ} (hn : 0 < n) (L : Submodule ℤ E)
    (c : OrthonormalBasis (Fin n) ℝ E) (a : Fin n → ℝ)
    (hpos : ∀ i, 0 < a i) (hmono : Monotone a)
    (hminimum : ∀ i x, x ∈ L → x ∉ Submodule.span ℝ (c '' Set.Iio i) → a i ≤ ‖x‖)
    {x : E} (hx : x ∈ L)
    (hbox : ∀ i, |c.toBasis.repr x i| < a i / n) : x = 0 := by
  classical
  by_contra hx0
  let S := (c.toBasis.repr x).support
  have hS : S.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    have hr : c.toBasis.repr x = 0 := Finsupp.support_eq_empty.mp he
    exact hx0 (c.toBasis.repr.injective (by simpa using hr))
  let j := S.max' hS
  have hj : j ∈ S := Finset.max'_mem _ hS
  have hnot : x ∉ Submodule.span ℝ (c '' Set.Iio j) := by
    intro h
    have hsupport := c.toBasis.repr_support_subset_of_mem_span (Set.Iio j) h
    exact (lt_irrefl j) (hsupport hj)
  have hmin : a j ≤ ‖x‖ := hminimum j x hx hnot
  have hnj : 0 < a j := hpos j
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm (i : Fin n) : ‖c.toBasis.repr x i • c i‖ < a j / n := by
    rw [norm_smul, c.orthonormal.1 i, mul_one, Real.norm_eq_abs]
    by_cases hi : i ≤ j
    · exact (hbox i).trans_le (div_le_div_of_nonneg_right (hmono hi) hnR.le)
    · have hz : c.toBasis.repr x i = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro him
        exact hi (Finset.le_max' _ _ him)
      rw [hz, abs_zero]
      positivity
  have hstrict :
      ∑ i : Fin n, ‖c.toBasis.repr x i • c i‖ < a j := by
    have hsum := Finset.sum_lt_sum_of_nonempty
      (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨⟨0, hn⟩, Finset.mem_univ _⟩)
      (fun i _ => hterm i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_div_cancel₀ _ (ne_of_gt hnR)] using hsum
  have hnorm : ‖x‖ ≤ ∑ i : Fin n, ‖c.toBasis.repr x i • c i‖ := by
    calc
      ‖x‖ = ‖∑ i : Fin n, c.toBasis.repr x i • c i‖ := by
        congr 1
        exact c.toBasis.sum_repr x |>.symm
      _ ≤ _ := norm_sum_le _ _
  exact (not_lt_of_ge hmin) (hnorm.trans_lt hstrict)

omit [FiniteDimensional ℝ E] in
theorem greedy_lattice_coordinate_box_zero
    {n : ℕ} (hn : 0 < n) (L : Submodule ℤ E)
    (b : Basis (Fin n) ℝ E) (hb : IsGreedyLatticeFamily L b)
    (c : OrthonormalBasis (Fin n) ℝ E)
    (hflag : ∀ i, Submodule.span ℝ (c '' Set.Iio i) =
      Submodule.span ℝ (b '' Set.Iio i))
    {x : E} (hx : x ∈ L)
    (hbox : ∀ i, |c.toBasis.repr x i| < ‖b i‖ / n) : x = 0 := by
  apply lattice_flag_coordinate_box_zero hn L c (fun i => ‖b i‖)
    (fun i => norm_pos_iff.mpr (b.ne_zero i)) hb.norm_mono _ hx hbox
  intro i y hy hyU
  exact hb.2.2 i y hy (by rwa [← hflag i])

end
end CCDN
