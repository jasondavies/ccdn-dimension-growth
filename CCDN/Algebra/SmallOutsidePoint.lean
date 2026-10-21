/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Algebra.PolynomialPredicates
public import CCDN.Height.ProjectiveBox
public import CCDN.Hilbert.FilteredHilbertPolynomial
import CCDN.Height.ProjectiveIntegerHeight
import CCDN.Hilbert.HilbertLowDegreeEquation
import CCDN.LowerBound.GridPointInterpolation
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Star.Rat
/-! CCDN Corollary 4.1.2: integer points outside a proper irreducible
affine variety, with coordinates bounded by its Hilbert degree, and the
corresponding rational projective points of bounded height. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma exists_integer_grid_field_eval_ne_zero_fin
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : f ≠ 0) (d : ℕ) (hd : f.totalDegree ≤ d) :
    ∃ a : Fin n → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧
      eval (fun i => (a i : K)) f ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  let S : Finset K := (Finset.range (d + 1)).image (fun t : ℕ => (t : K))
  have hS : S.card = d + 1 := by
    rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
  have he : (Fintype.piFinset fun _ : Fin n => S).filter (fun v => eval v f = 0) =
      Fintype.piFinset (fun _ : Fin n => S) := by
    apply Finset.filter_eq_self.mpr
    intro x hx
    have hi (i) : ∃ t : ℕ, t ≤ d ∧ (t : K) = x i := by
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp ((Fintype.mem_piFinset.mp hx) i)
      exact ⟨t, by have := Finset.mem_range.mp ht; omega, he⟩
    choose t ht htx using hi
    have hh := hn (fun i => (t i : ℤ)) (fun i => ⟨by positivity, by exact_mod_cast ht i⟩)
    simpa only [Int.cast_natCast, htx] using hh
  have h := schwartz_zippel_totalDegree hf S
  rw [he] at h
  have hR : (1 : ℚ) ≤ (f.totalDegree : ℚ) / (d + 1) := by
    simpa [hS] using (NNRat.cast_le (K := ℚ)).mpr h
  have hh := (le_div_iff₀ (show (0 : ℚ) < d + 1 by positivity)).mp hR
  have hdR : (f.totalDegree : ℚ) ≤ d := by exact_mod_cast hd
  linarith

theorem exists_integer_grid_field_eval_ne_zero
    {K σ : Type*} [Field K] [CharZero K] [Fintype σ]
    (f : MvPolynomial σ K) (hf : f ≠ 0) (d : ℕ) (hd : f.totalDegree ≤ d) :
    ∃ a : σ → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧
      eval (fun i => (a i : K)) f ≠ 0 := by
  let e := Fintype.equivFin σ
  let g := rename e f
  have hg : g ≠ 0 := (map_ne_zero_iff _ (rename_injective e e.injective)).mpr hf
  obtain ⟨a, ha, he⟩ := exists_integer_grid_field_eval_ne_zero_fin g hg d
    ((totalDegree_rename_le e f).trans hd)
  refine ⟨a ∘ e, fun i => ha (e i), ?_⟩
  simpa only [g, eval_rename, Function.comp_def] using he

/-- A zero-dimensional affine coordinate ring has at most its
Hilbert degree many distinct points, over the given coefficient field. -/
theorem zero_dimensional_affine_points_card_le
    {K σ ι : Type*} [Field K] [Fintype σ] [LinearOrder σ] [Fintype ι]
    (I : Ideal (MvPolynomial σ K)) (d : ℕ)
    (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d)
    (z : ι → σ → K) (hz : Function.Injective z)
    (hzero : ∀ i f, f ∈ I → eval (z i) f = 0) : Fintype.card ι ≤ d := by
  classical
  obtain ⟨N₀, hN₀⟩ := filteredHilbertPolynomial_spec I
  have hP : filteredHilbertPolynomial I = Polynomial.C (d : ℚ) := by
    have hh := Polynomial.eq_C_of_natDegree_eq_zero hdim
    rw [Polynomial.leadingCoeff, hdim] at hdegree
    exact hh.trans (congrArg Polynomial.C hdegree)
  let S : Finset K := Finset.univ.biUnion (fun i : ι => Finset.univ.image (z i))
  let N := max N₀ (Fintype.card σ * (S.card - 1))
  have hdimN : Module.finrank K (filteredCoordinateSpace I N) = d := by
    have hh := hN₀ N (le_max_left _ _)
    rw [hP, Polynomial.eval_C] at hh
    exact_mod_cast hh.symm
  have hh := grid_points_filtered_lower I S z hz (fun i j => by
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩)
    hzero (le_max_right _ _ : _ ≤ N)
  exact hh.trans_eq hdimN

/-- The affine conclusion of Corollary 4.1.2, including dimension zero.
The point is integral even when the variety is defined over a larger
characteristic-zero coefficient field. -/
theorem exists_small_integer_point_outside_prime_ideal
    {K σ : Type*} [Field K] [CharZero K] [Fintype σ] [LinearOrder σ]
    (I : Ideal (MvPolynomial σ K)) [I.IsPrime] (d : ℕ)
    (hcodim : (filteredHilbertPolynomial I).natDegree < Fintype.card σ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    ∃ a : σ → ℤ, (∀ i, 0 ≤ a i ∧ a i ≤ d) ∧
      ∃ f ∈ I, eval (fun i => (a i : K)) f ≠ 0 := by
  classical
  by_cases hdim : (filteredHilbertPolynomial I).natDegree = 0
  · have hnon : Nonempty σ := Fintype.card_pos_iff.mp (by omega)
    let i₀ : σ := Classical.choice hnon
    by_contra hn
    push Not at hn
    let z : Fin (d + 1) → σ → K := fun t _ => (t.val : K)
    have hz : Function.Injective z := by
      intro t u h
      have hh := congrFun h i₀
      exact Fin.ext (Nat.cast_injective hh)
    have hzero (t : Fin (d + 1)) (f) (hf : f ∈ I) : eval (z t) f = 0 := by
      have hh := hn (fun _ : σ => (t.val : ℤ))
        (fun _ => ⟨by positivity, by exact_mod_cast (show t.val ≤ d by omega)⟩) f hf
      simpa only [z, Int.cast_natCast] using hh
    have hh := zero_dimensional_affine_points_card_le I d hdim
      (by simpa only [hdim, Nat.factorial_zero, Nat.cast_one, div_one] using hdegree) z hz hzero
    simp only [Fintype.card_fin] at hh
    omega
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show 1 ≤ (filteredHilbertPolynomial I).natDegree by omega)
    have hm' : (filteredHilbertPolynomial I).natDegree = m + 1 := by omega
    obtain ⟨f, hf, hfi, hfd⟩ := exists_mem_ideal_degree_le_multiplicity I d
      ⟨hm', by simpa only [hm'] using hdegree⟩ (by omega)
    obtain ⟨a, ha, he⟩ := exists_integer_grid_field_eval_ne_zero f hf d hfd
    exact ⟨a, ha, f, hfi, he⟩

lemma homogeneous_ideal_eval_zero {K σ : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (hproper : I ≠ ⊤)
    (hhom : IsHomogeneousIdeal I)
    (f : MvPolynomial σ K) (hf : f ∈ I) : eval (0 : σ → K) f = 0 := by
  have hcI : C (f.coeff 0) ∈ I := by
    simpa only [homogeneousComponent_zero] using hhom f hf 0
  have hc : f.coeff 0 = 0 := by
    by_contra hn
    apply hproper
    exact Ideal.eq_top_of_isUnit_mem I hcI
      ((isUnit_iff_ne_zero.mpr hn).map C)
  rw [eval_zero]
  exact hc

/-- A bounded integer representative gives a rational projective point
outside the variety even when its equations have coefficients in a larger
characteristic-zero field. Both the rational height and the
projective nonmembership over that field occur in the conclusion. -/
theorem exists_small_projective_integer_representative_outside
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K)) [I.IsPrime]
    (hhom : IsHomogeneousIdeal I)
    (d : ℕ)
    (hcodim : (filteredHilbertPolynomial I).natDegree < n + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    ∃ (a : Fin (n + 1) → ℤ) (ha : a ≠ 0)
      (haK : (fun i => (a i : K)) ≠ 0),
      (∀ i, |a i| ≤ d) ∧
      (Projectivization.mk ℚ (rationalPoint a) (rationalPoint_ne_zero ha)).mulHeight ≤ d ∧
      Projectivization.mk K (fun i => (a i : K)) haK ∉ projectiveIdealZeroLocus I := by
  obtain ⟨a, ha, f, hfi, hf⟩ := exists_small_integer_point_outside_prime_ideal I d
    (by simpa only [Fintype.card_fin] using hcodim) hdegree
  have haK : (fun i => (a i : K)) ≠ 0 := by
    intro hz
    apply hf
    rw [hz]
    exact homogeneous_ideal_eval_zero I (Ideal.IsPrime.ne_top ‹I.IsPrime›) hhom f hfi
  have ha0 : a ≠ 0 := by
    intro hz
    apply haK
    simp only [hz, Pi.zero_apply, Int.cast_zero]
    rfl
  have hbound (i) : |a i| ≤ d := by
    rw [abs_of_nonneg (ha i).1]
    exact (ha i).2
  refine ⟨a, ha0, haK, hbound, ?_, ?_⟩
  · apply projective_integer_height_le a ha0
    intro i
    exact_mod_cast hbound i
  · intro hmem
    exact hf (hmem _ haK rfl f hfi)

/-- The projective conclusion of CCDN Corollary 4.1.2 for rational
homogeneous prime ideals, using the projective height. -/
theorem exists_small_rational_projective_point_outside_prime_ideal
    {n : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ)) [I.IsPrime]
    (hhom : IsHomogeneousIdeal I)
    (d : ℕ)
    (hcodim : (filteredHilbertPolynomial I).natDegree < n + 1)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial) :
    ∃ x : ProjectivePoint n, x.mulHeight ≤ d ∧ x ∉ projectiveIdealZeroLocus I := by
  obtain ⟨a, ha, haQ, _, hheight, houtside⟩ :=
    exists_small_projective_integer_representative_outside I hhom d hcodim hdegree
  exact ⟨Projectivization.mk ℚ (rationalPoint a) (rationalPoint_ne_zero ha),
    hheight, houtside⟩

end
end CCDN
