module

public import CCDN.NonabsolutePlaneCount
public import CCDN.CompleteIntersectionDegreeBudget
public import CCDN.CurveBoxDegreeBound

/-! CCDN Corollary 4.1.4 for irreducible affine hypersurfaces in three
variables. Splitting of the full equation over any field extension gives
an auxiliary equation of degree at most d. The prime curve
components of the resulting section have total degree at most d², giving
the sharp elementary bound d²(2B+1), whatever the highest homogeneous
component. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Linear descent of both proper factors produces a base-field auxiliary
equation vanishing at every base-field zero, with degree at most d. -/
theorem nonabsolute_affine_auxiliary {k K : Type*}
    [Field k] [Field K] [Algebra k K] {n : ℕ}
    (f : MvPolynomial (Fin n) k) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap k K) f)) :
    ∃ q : MvPolynomial (Fin n) k, q ≠ 0 ∧
      q.totalDegree ≤ f.totalDegree ∧ ¬ f ∣ q ∧
      ∀ x : Fin n → k, eval x f = 0 → eval x q = 0 := by
  have hd := totalDegree_pos_of_nonzero_nonunit f hir.ne_zero hir.not_isUnit
  have hmap0 : map (algebraMap k K) f ≠ 0 := by
    intro he
    apply hir.ne_zero
    exact map_injective (algebraMap k K) (algebraMap k K).injective (by simpa using he)
  have hmapd : (map (algebraMap k K) f).totalDegree = f.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ (algebraMap k K).injective]
  have hmapu : ¬ IsUnit (map (algebraMap k K) f) := by
    intro hu
    have he := (isUnit_iff_totalDegree_of_isReduced.mp hu).2
    rw [hmapd] at he
    omega
  have hfac : ∃ g h : MvPolynomial (Fin n) K,
      map (algebraMap k K) f = g * h ∧ ¬ IsUnit g ∧ ¬ IsUnit h := by
    by_contra! hn
    apply hred
    refine ⟨hmapu, ?_⟩
    intro g h he
    by_cases hu : IsUnit g
    · exact Or.inl hu
    · exact Or.inr (hn g h he hu)
  obtain ⟨g, h, hfac, hgu, hhu⟩ := hfac
  have hg0 : g ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hh0 : h ≠ 0 := fun he => hmap0 (by simp [hfac, he])
  have hgd := totalDegree_pos_of_nonzero_nonunit g hg0 hgu
  have hhd := totalDegree_pos_of_nonzero_nonunit h hh0 hhu
  have hdegrees : g.totalDegree + h.totalDegree = f.totalDegree := by
    rw [hfac, totalDegree_mul_of_isDomain hg0 hh0] at hmapd
    exact hmapd
  obtain ⟨g₀, hg₀, hgd₀, hgz⟩ := exists_nonzero_polynomial_linear_descent (k := k) g hg0
  obtain ⟨h₀, hh₀, hhd₀, hhz⟩ := exists_nonzero_polynomial_linear_descent (k := k) h hh0
  refine ⟨g₀ * h₀, mul_ne_zero hg₀ hh₀, ?_, ?_, ?_⟩
  · rw [totalDegree_mul_of_isDomain hg₀ hh₀]
    omega
  · intro hdiv
    rcases hir.prime.dvd_or_dvd hdiv with hgdiv | hhdiv
    · have he := totalDegree_le_of_dvd_of_isDomain hgdiv hg₀
      omega
    · have he := totalDegree_le_of_dvd_of_isDomain hhdiv hh₀
      omega
  · intro x hx
    have he := congrArg (algebraMap k K) hx
    rw [map_eval, hfac, eval_mul, map_zero] at he
    rw [eval_mul]
    rcases mul_eq_zero.mp he with hgzero | hhzero
    · rw [hgz x hgzero, zero_mul]
    · rw [hhz x hhzero, mul_zero]

theorem finite_curve_union_count_le_box_side
    (S : Finset (Ideal (CoordinatePolynomial 3)))
    (d : Ideal (CoordinatePolynomial 3) → ℕ)
    (hcurve : ∀ P ∈ S, P.IsPrime ∧ P.height = 2 ∧ HasAffineCurveDegree P (d P))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) ≤
      (∑ P ∈ S, (d P : ℝ)) * (2 * B + 1) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert P S hPS ih =>
    have hP := hcurve P (Finset.mem_insert_self _ _)
    let : P.IsPrime := hP.1
    have hS := ih (fun Q hQ => hcurve Q (Finset.mem_insert_of_mem hQ))
    rw [Finset.set_biUnion_insert, Finset.sum_insert hPS, add_mul]
    have hcount : (count (idealZeroLocus P ∪ ⋃ Q ∈ S, idealZeroLocus Q) B : ℝ) ≤
        count (idealZeroLocus P) B + count (⋃ Q ∈ S, idealZeroLocus Q) B := by
      exact_mod_cast count_union_le (idealZeroLocus P) (⋃ Q ∈ S, idealZeroLocus Q) B
    exact hcount.trans (add_le_add (curve_count_le_degree_mul_box_side P hP.2.1 hP.2.2 hB) hS)

/-- The exact nonabsolute affine-surface estimate, over any extension in
which the irreducible rational equation splits. -/
theorem nonabsolute_surface_count_le {K : Type*} [Field K] [Algebra ℚ K]
    (f : CoordinatePolynomial 3) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤ (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) := by
  obtain ⟨g, _, hgd, hfg, hzeros⟩ := nonabsolute_affine_auxiliary f hir hred
  obtain ⟨S, d, hcurve, hcover, hbudget, _⟩ :=
    exists_completeIntersection_curve_components f g hir hfg
  have hsub : zeroLocus f ⊆ ⋃ P ∈ S, idealZeroLocus P := by
    intro x hx
    rw [← hcover]
    exact ⟨hx, hzeros x hx⟩
  have hsum : (∑ P ∈ S, (d P : ℝ)) ≤ (f.totalDegree : ℝ) ^ 2 := by
    have hh := hbudget.trans (Nat.mul_le_mul_left f.totalDegree hgd)
    exact_mod_cast (by simpa only [pow_two] using hh)
  calc
    _ ≤ (count (⋃ P ∈ S, idealZeroLocus P) B : ℝ) := by
      exact_mod_cast count_mono hsub le_rfl
    _ ≤ (∑ P ∈ S, (d P : ℝ)) * (2 * B + 1) :=
      finite_curve_union_count_le_box_side S d (by
        intro P hP
        have hh := hcurve P hP
        exact ⟨hh.1, hh.2.1, hh.2.2.2.2.2⟩) hB
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by linarith)

/-- For B at least one, a single explicit constant suffices for every
irreducible rational surface equation splitting over the given extension. -/
theorem nonabsolute_surface_count_le_three_degree_sq_mul
    {K : Type*} [Field K] [Algebra ℚ K]
    (f : CoordinatePolynomial 3) (hir : Irreducible f)
    (hred : ¬ Irreducible (map (algebraMap ℚ K) f))
    {B : ℝ} (hB : 1 ≤ B) :
    (count (zeroLocus f) B : ℝ) ≤ 3 * (f.totalDegree : ℝ) ^ 2 * B := by
  calc
    _ ≤ (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) :=
      nonabsolute_surface_count_le f hir hred (by linarith)
    _ ≤ (f.totalDegree : ℝ) ^ 2 * (3 * B) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    _ = _ := by ring

/-- The exact bound for an integer equation, with rational irreducibility
and splitting after extension expressed on its coefficient images. -/
theorem nonabsolute_integer_surface_count_le
    {K : Type*} [Field K] [Algebra ℚ K]
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    (hred : ¬ Irreducible (map (algebraMap ℚ K) (map (Int.castRingHom ℚ) f)))
    {B : ℝ} (hB : 0 ≤ B) :
    (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ≤
      (f.totalDegree : ℝ) ^ 2 * (2 * B + 1) := by
  have hd : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree := by
    unfold totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
  simpa only [hd] using
    nonabsolute_surface_count_le (map (Int.castRingHom ℚ) f) hir hred hB

end
end CCDN
