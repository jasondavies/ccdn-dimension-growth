/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredHilbertPolynomial
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import CCDN.Algebra.IdealZeroLocus
public import CCDN.Hilbert.LinearProjectionFiltration
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import CCDN.Hypersurface.SmallOutsidePoint
import CCDN.Projection.HilbertProjectionDegree
import CCDN.Projection.IntegralProjectionClosedImage
import CCDN.Projection.LinearNormalizationInfinite
import Mathlib.RingTheory.Nullstellensatz
import CCDN.Algebra.BoundedLinearSeparation
import CCDN.Projection.BoundedDegreeNormalizationFiber

/-!
Set-theoretic degree-bounded equations for an affine prime variety.
An arbitrary outside point is separated by an ideal member of degree
at most the Hilbert multiplicity. The proof constructs an integral linear
projection, separates its finite fiber, and uses lying over.

Fibers of a linear normalization are finite. An additional
homogeneous linear form separates an outside point from the whole fiber.
-/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

private theorem linear_normalization_fiber_finite
    {K : Type*} [Field K] [CharZero K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (l : Fin (m + 1) → MvPolynomial (Fin n) K)
    (hl : ∀ i, (l i).totalDegree ≤ 1)
    (hi : Function.Injective (projectionCoordinateMap I l))
    (hint : (projectionCoordinateMap I l).IsIntegral)
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (z : Fin (m + 1) → K) :
    {x : Fin n → K | x ∈ idealZeroLocus I ∧ ∀ i, eval x (l i) = z i}.Finite := by
  classical
  by_contra h
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h (d + 1)
  have hh := bounded_degree_normalization_fiber_card_le I 1 (by omega) l hl hi hint
    d hdimdeg z s (fun x hx => (hs hx).1) (fun x hx => (hs hx).2)
  simp only [one_pow, mul_one, hcard] at hh
  omega

private theorem exists_linear_form_separating_finite_set
    {K : Type*} [Field K] [CharZero K] {n : ℕ}
    (s : Finset (Fin n → K)) (z : Fin n → K) (hz : z ∉ s) :
    ∃ t : MvPolynomial (Fin n) K, t.IsHomogeneous 1 ∧
      ∀ x ∈ s, eval x t ≠ eval z t := by
  classical
  let S := insert z s
  obtain ⟨k, _, hk⟩ := exists_bounded_moment_separation
    (fun x : S => x.val) Subtype.val_injective
  let t : MvPolynomial (Fin n) K := ∑ j : Fin n, C ((k : K) ^ j.val) * X j
  have ht (x : Fin n → K) : eval x t = ∑ j : Fin n, x j * (k : K) ^ j.val := by
    simp only [t, map_sum, eval_mul, eval_C, eval_X, mul_comm]
  refine ⟨t, IsHomogeneous.sum _ _ 1 (fun j _ => isHomogeneous_C_mul_X _ _), ?_⟩
  intro x hx he
  have hxe : (⟨x, Finset.mem_insert_of_mem hx⟩ : S) =
      ⟨z, Finset.mem_insert_self _ _⟩ := by
    apply hk
    simpa only [← ht] using he
  have hxz : x = z := congrArg Subtype.val hxe
  exact hz (hxz ▸ hx)

end
end CCDN

namespace CCDN
noncomputable section
open MvPolynomial

private theorem exists_low_degree_point_separator_of_pos_dimension
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdimdeg : HasProjectiveDimensionDegree I m d)
    (z : Fin n → K) (hz : ¬ ∀ f ∈ I, eval z f = 0) :
    ∃ g : MvPolynomial (Fin n) K, g ∈ I ∧ g.totalDegree ≤ d ∧ eval z g ≠ 0 := by
  classical
  have hmn : m + 1 ≤ n := by
    obtain ⟨_, _, hd, _⟩ := filteredHilbertPolynomial_positive_multiplicity I
      (Ideal.IsPrime.ne_top ‹I.IsPrime›)
    simpa only [hdimdeg.natDegree_eq, Fintype.card_fin] using hd
  obtain ⟨l, hl, hint, hinj⟩ :=
    exists_linear_integral_normalization_infinite_of_le m n hmn I hdimdeg.natDegree_eq
  let V := {x : Fin n → K | x ∈ idealZeroLocus I ∧
    ∀ i, eval x (l i) = eval z (l i)}
  have hV : V.Finite := linear_normalization_fiber_finite I l
    (fun i => (hl i).totalDegree_le) hinj hint d hdimdeg (fun i => eval z (l i))
  have hzV : z ∉ hV.toFinset := by
    intro h
    exact hz (hV.mem_toFinset.mp h).1
  obtain ⟨t, ht, hsep⟩ := exists_linear_form_separating_finite_set hV.toFinset z hzV
  let a : Fin (m + 2) → MvPolynomial (Fin n) K := Fin.lastCases t l
  let b : Fin (m + 1) → MvPolynomial (Fin (m + 2)) K := fun i => X i.castSucc
  have ha (i) : (a i).totalDegree ≤ 1 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [a, Fin.lastCases_last] using ht.totalDegree_le
    · simpa only [a, Fin.lastCases_castSucc] using (hl j).totalDegree_le
  have hb (i) : (b i).totalDegree ≤ 1 := by simp [b]
  have he : (projectionCoordinateMap I a).comp (aeval b) = projectionCoordinateMap I l := by
    ext i
    simp [projectionCoordinateMap, a, b]
  have hi : AlgebraicIndependent K (fun i => projectionCoordinateMap I a (b i)) := by
    change Function.Injective (aeval (fun i => projectionCoordinateMap I a (b i)))
    rw [← comp_aeval, he]
    exact hinj
  obtain ⟨F, _, _, hFd, hker⟩ :=
    exists_hypersurface_projection_equation_degree_le I a ha d hdimdeg b hb hi
  have hintA : (projectionCoordinateMap I a).IsIntegral := by
    intro x
    apply RingHom.IsIntegralElem.of_comp (f := (aeval (R := K) b).toRingHom)
    change ((projectionCoordinateMap I a).comp (aeval b)).IsIntegralElem x
    rw [he]
    exact hint x
  have heval (x : Fin n → K) :
      eval x ((aeval a) F) = eval (fun i => eval x (a i)) F := by
    change (MvPolynomial.aeval x) ((aeval a) F) = _
    rw [comp_aeval_apply]
    rfl
  refine ⟨(aeval a) F, ?_,
    (aeval_totalDegree_le a ha F).trans (by simpa only [one_mul] using hFd), ?_⟩
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hmem : F ∈ RingHom.ker (projectionCoordinateMap I a) := by
      rw [hker]
      exact Ideal.subset_span (Set.mem_singleton F)
    exact hmem
  · intro hzero
    have hFzero : eval (fun i => eval z (a i)) F = 0 := by rwa [heval] at hzero
    have hzker : ∀ p ∈ RingHom.ker (projectionCoordinateMap I a),
        eval (fun i => eval z (a i)) p = 0 := by
      rw [hker]
      change Ideal.span {F} ≤ RingHom.ker (eval (fun i => eval z (a i)))
      apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact hFzero
    obtain ⟨x, hxI, hxa⟩ := integral_projection_exists_point I a hintA
      (fun i => eval z (a i)) hzker
    have hxV : x ∈ V := ⟨hxI, fun i => by
      simpa only [a, Fin.lastCases_castSucc] using hxa i.castSucc⟩
    apply hsep x (hV.mem_toFinset.mpr hxV)
    simpa only [a, Fin.lastCases_last] using hxa (Fin.last (m + 1))

private theorem exists_low_degree_point_separator_of_dimension_zero
    {K : Type*} [Field K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (d : ℕ) (hdim : (filteredHilbertPolynomial I).natDegree = 0)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff = d)
    (z : Fin n → K) (hz : ¬ ∀ f ∈ I, eval z f = 0) :
    ∃ g : MvPolynomial (Fin n) K, g ∈ I ∧ g.totalDegree ≤ d ∧ eval z g ≠ 0 := by
  classical
  let V := {x : Fin n → K | x ∈ idealZeroLocus I}
  have hbound (s : Finset (Fin n → K)) (hs : (s : Set (Fin n → K)) ⊆ V) :
      s.card ≤ d := by
    have h := zero_dimensional_affine_points_card_le I d hdim hdegree
      (fun x : s => x.val) Subtype.val_injective (fun x => hs x.property)
    simpa only [Fintype.card_coe] using h
  have hV : V.Finite := by
    by_contra h
    obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h (d + 1)
    have hh := hbound s hs
    omega
  let S := hV.toFinset
  have hScard : S.card ≤ d := hbound S (fun _ hx => hV.mem_toFinset.mp hx)
  have hj (x : S) : ∃ j : Fin n, x.val j ≠ z j := by
    apply Function.ne_iff.mp
    intro h
    exact hz (h ▸ hV.mem_toFinset.mp x.property)
  choose j hj using hj
  let g : MvPolynomial (Fin n) K := ∏ x : S, (X (j x) - C (x.val (j x)))
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) I]
    intro x hx
    have hxV : x ∈ V := by
      intro f hf
      simpa only [aeval_eq_eval] using hx f hf
    let y : S := ⟨x, hV.mem_toFinset.mpr hxV⟩
    change eval x g = 0
    simp only [g, map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ y)
    simp [y]
  · calc
      g.totalDegree ≤ ∑ _x : S, 1 := by
        apply (totalDegree_finsetProd _ _).trans
        apply Finset.sum_le_sum
        intro x _
        exact (totalDegree_sub _ _).trans (by simp)
      _ = S.card := by simp
      _ ≤ d := hScard
  · simp only [g, map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro x _
    simpa only [eval_sub, eval_X, eval_C, sub_ne_zero] using (hj x).symm

/-- Every point outside an affine prime variety over an algebraically closed
characteristic-zero field is detected by an equation of degree at most the
Hilbert multiplicity. -/
private theorem exists_low_degree_point_separator
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial)
    (z : Fin n → K) (hz : ¬ ∀ f ∈ I, eval z f = 0) :
    ∃ g : MvPolynomial (Fin n) K, g ∈ I ∧ g.totalDegree ≤ d ∧ eval z g ≠ 0 := by
  by_cases hdim : (filteredHilbertPolynomial I).natDegree = 0
  · exact exists_low_degree_point_separator_of_dimension_zero I d hdim
      (by simpa only [hdim, Nat.factorial_zero, Nat.cast_one, div_one] using hdegree) z hz
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hdim
    exact exists_low_degree_point_separator_of_pos_dimension I d
      ⟨hm, by simpa only [hm] using hdegree⟩ z hz

/-- In particular, noncontainment of prime varieties is witnessed in degree
at most the multiplicity of the ideal providing the equation. -/
theorem exists_low_degree_ideal_separator
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [J.IsPrime] (d : ℕ)
    (hdegree : (filteredHilbertPolynomial I).leadingCoeff =
      (d : ℚ) / (filteredHilbertPolynomial I).natDegree.factorial)
    (hIJ : ¬ I ≤ J) :
    ∃ g : MvPolynomial (Fin n) K, g ∈ I ∧ g.totalDegree ≤ d ∧ g ∉ J := by
  classical
  obtain ⟨p, hpI, hpJ⟩ := IsConcreteLE.not_le_iff_exists.mp hIJ
  have hpoint : ∃ z : Fin n → K, z ∈ idealZeroLocus J ∧ eval z p ≠ 0 := by
    by_contra! h
    apply hpJ
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) J]
    intro z hz
    exact h z (fun f hf => by simpa only [aeval_eq_eval] using hz f hf)
  obtain ⟨z, hzJ, hzp⟩ := hpoint
  obtain ⟨g, hgI, hgd, hzg⟩ := exists_low_degree_point_separator I d hdegree z
    (fun h => hzp (h p hpI))
  exact ⟨g, hgI, hgd, fun hgJ => hzg (hzJ g hgJ)⟩

end
end CCDN
