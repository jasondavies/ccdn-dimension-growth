module

public import CCDN.Hilbert.HilbertCoefficientEquiv
public import CCDN.Hilbert.PrimeIdealDimensionDrop
public import CCDN.Algebra.LowDegreePointSeparation
/-! The sharp grid bound for prime varieties moved by a coefficient
automorphism. A low-degree equation of the conjugate is constructed and
is a proper section of the original variety. Fixed-field points lie on it. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma eval_coefficientEquiv_of_fixed
    {K σ : Type*} [Field K] (e : K ≃+* K) (x : σ → K)
    (hx : ∀ i, e (x i) = x i) (f : MvPolynomial σ K) :
    eval x (mapEquiv σ e f) = e (eval x f) := by
  rw [mapEquiv_apply, eval_map]
  have he := eval₂_comp e.toRingHom x f
  have hcomp : e.toRingHom ∘ x = x := funext hx
  rw [hcomp] at he
  exact he.symm

theorem conjugate_prime_grid_card_le
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : K ≃+* K) (hne : I.map (mapEquiv (Fin n) e) ≠ I)
    (S : Finset K) (s : Finset (Fin n → K))
    (hzero : ∀ x ∈ s, ∀ f ∈ I, eval x f = 0)
    (hfixed : ∀ x ∈ s, ∀ i, e (x i) = x i)
    (hgrid : ∀ x ∈ s, ∀ i, x i ∈ S) :
    s.card ≤ d ^ 2 * S.card ^ m := by
  classical
  let J := I.map (mapEquiv (Fin n) e)
  let : J.IsPrime := Ideal.map_isPrime_of_equiv _
  have hpoly : filteredHilbertPolynomial J = filteredHilbertPolynomial I :=
    filteredHilbertPolynomial_coefficientEquiv I e
  have hJdim : (filteredHilbertPolynomial J).natDegree = m + 1 := by rw [hpoly, hdim]
  have hnot : ¬ J ≤ I := prime_ideal_not_le_of_same_positive_dimension J I hJdim hdim hne
  obtain ⟨f, hfJ, hfd, hfI⟩ := exists_low_degree_ideal_separator J I d
    (by rw [hpoly, hdim]; exact hdegree) hnot
  have hsectionzero (x) (hx : x ∈ s) : eval x f = 0 := by
    obtain ⟨g, hg, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (mapEquiv (Fin n) e) (mapEquiv (Fin n) e).surjective).mp hfJ
    rw [eval_coefficientEquiv_of_fixed e x (hfixed x hx), hzero x hx g hg, map_zero]
  have hh := principal_section_grid_card_le I d hdim hdegree f hfI S s
    hzero hsectionzero hgrid
  exact hh.trans (Nat.mul_le_mul_right _ (by simpa only [pow_two] using Nat.mul_le_mul_left d hfd))

/-- Rational points on a variety with coefficients in an extension of Q. -/
def rationalIdealZeroLocusOver {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) : Set (RatPoint n) :=
  {x | ∀ f ∈ I, eval (fun i => algebraMap ℚ K (x i)) f = 0}

theorem conjugate_prime_count_le_box
    {K : Type*} [Field K] [Algebra ℚ K] [IsAlgClosed K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = m + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = (d : ℚ) / (m + 1).factorial)
    (e : K ≃ₐ[ℚ] K) (hne : I.map (mapEquiv (Fin n) e.toRingEquiv) ≠ I)
    {B : ℝ} (hB : 0 ≤ B) :
    (count (rationalIdealZeroLocusOver I) B : ℝ) ≤
      (d : ℝ) ^ 2 * (2 * B + 1) ^ m := by
  classical
  let : CharZero K := Algebra.charZero_of_charZero ℚ K
  let T := integralPoints (rationalIdealZeroLocusOver I) B
  let S : Finset K := (Finset.Icc (-⌊B⌋) ⌊B⌋).image (fun t : ℤ => (t : K))
  let point : IntPoint n → Fin n → K := fun x i => (x i : K)
  have hi : Function.Injective point := by
    intro x y h
    funext i
    exact Int.cast_injective (congrFun h i)
  have hz : ∀ x ∈ T.image point, ∀ f ∈ I, eval x f = 0 := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    have hh := (mem_integralPoints.mp ha).2
    simpa only [rationalIdealZeroLocusOver, Set.mem_ofPred_eq, rationalPoint, map_intCast, point] using hh
  have hf : ∀ x ∈ T.image point, ∀ i, e.toRingEquiv (x i) = x i := by
    intro x hx i
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    exact map_intCast e (a i)
  have hg : ∀ x ∈ T.image point, ∀ i, x i ∈ S := by
    intro x hx i
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨a i, ?_, rfl⟩
    obtain ⟨hlo, hhi⟩ := abs_le.mp ((mem_integralPoints.mp ha).1 i)
    have hn : -(a i) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact Finset.mem_Icc.mpr ⟨by omega, Int.le_floor.mpr hhi⟩
  have hh := conjugate_prime_grid_card_le I d hdim hdegree e.toRingEquiv hne S
    (T.image point) hz hf hg
  rw [Finset.card_image_of_injective _ hi] at hh
  have hcard : (count (rationalIdealZeroLocusOver I) B : ℝ) ≤
      (d : ℝ) ^ 2 * (S.card : ℝ) ^ m := by exact_mod_cast hh
  have hScard : (S.card : ℝ) ≤ 2 * B + 1 := by
    have hfloor : 0 ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
    dsimp only [S]
    rw [Finset.card_image_of_injective _ Int.cast_injective, Int.card_Icc]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    push_cast
    linarith [Int.floor_le B]
  exact hcard.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hScard m) (by positivity))

end
end CCDN
