/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hilbert.FilteredPrimeDecomposition
public import CCDN.Surface.SurfaceCurve
import CCDN.Hilbert.FilteredComponentDegreeBudget
import CCDN.Hilbert.FilteredLinearGrowth
import CCDN.Hilbert.PrimeComponentTranscendence
/-! A finite decomposition of a proper affine surface section into
rational prime curves, with a proved additive degree budget. Components with
no rational points are discarded before requiring positive curve degrees. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Every minimal-prime component has an eventual affine Hilbert
degree. The slope is allowed to be zero until a rational point is exhibited. -/
theorem polynomialSection_minimalPrime_degrees_exist
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    ∃ d : minimalPrimeComponents (polynomialSectionIdeal f g) → ℕ,
      (∀ P, HasAffineCurveDegree P.val (d P)) ∧
        ∑ P, d P ≤ f.totalDegree * g.totalDegree := by
  classical
  have hex (P : minimalPrimeComponents (polynomialSectionIdeal f g)) :
      ∃ d : ℕ, HasAffineCurveDegree P.val d := by
    obtain ⟨d, _, h⟩ := proper_intersection_eventual_linear_degree hf.prime hfg P.val
      (le_minimalPrimeComponents P.property (polynomialSectionIdeal_first_mem f g))
      (le_minimalPrimeComponents P.property (polynomialSectionIdeal_second_mem f g))
    exact ⟨d, h⟩
  choose d hd using hex
  exact ⟨d, hd, polynomialSection_minimalPrime_curveDegree_sum_le f g hf hfg d hd⟩

/-- A proper section in affine three-space is covered exactly by a finite
set of rational prime curves. Their positive Hilbert degrees sum to
at most the product of the two equation degrees. All components and degrees
are constructed, including the case of an empty common zero set. -/
theorem exists_completeIntersection_curve_components
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g) :
    ∃ S : Finset (Ideal (CoordinatePolynomial 3)),
      ∃ d : Ideal (CoordinatePolynomial 3) → ℕ,
        (∀ P ∈ S, IsSectionCurve f g P (d P)) ∧
        zeroLocus f ∩ zeroLocus g = ⋃ P ∈ S, idealZeroLocus P ∧
        (∑ P ∈ S, d P) ≤ f.totalDegree * g.totalDegree ∧
        (∀ P ∈ S, (polynomialSectionIdeal f g).IsMinimalPrime P) := by
  classical
  let T := minimalPrimeComponents (polynomialSectionIdeal f g)
  obtain ⟨δ, hδ, hsumδ⟩ := polynomialSection_minimalPrime_degrees_exist f g hf hfg
  let d (P : Ideal (CoordinatePolynomial 3)) := if hP : P ∈ T then δ ⟨P, hP⟩ else 0
  let S := T.filter (fun P => (idealZeroLocus P).Nonempty)
  have hd (P : T) : d P.val = δ P := by
    simp only [d, dite_eq_left P.property]
    rfl
  have hTP (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      (polynomialSectionIdeal f g).IsMinimalPrime P := mem_minimalPrimeComponents.mp hP
  have hcurve (P : Ideal (CoordinatePolynomial 3)) (hP : P ∈ T) :
      HasAffineCurveDegree P (d P) := by
    rw [hd ⟨P, hP⟩]
    exact hδ ⟨P, hP⟩
  refine ⟨S, d, ?_, ?_, ?_, ?_⟩
  · intro P hP
    obtain ⟨hPT, z, hz⟩ := Finset.mem_filter.mp hP
    have hminimal := hTP P hPT
    have : P.IsPrime := hminimal.isPrime
    have hheight : P.height = 2 := minimalPrime_pair_height_two hf.prime hfg hminimal
    have hdeg := hcurve P hPT
    exact ⟨⟨hminimal.isPrime, hheight, hminimal.le (polynomialSectionIdeal_first_mem f g), hdeg⟩,
      hminimal.le (polynomialSectionIdeal_second_mem f g),
      height_two_eventual_slope_pos_of_point P hheight z hz hdeg⟩
  · ext x
    constructor
    · intro hx
      have hxi : x ∈ idealZeroLocus (polynomialSectionIdeal f g) := by
        rw [idealZeroLocus_polynomialSectionIdeal]
        exact hx
      rw [idealZeroLocus_eq_union_minimalPrimeComponents] at hxi
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxi
      obtain ⟨hPT, hxP⟩ := Set.mem_iUnion.mp hxP
      exact Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr
        ⟨Finset.mem_filter.mpr ⟨hPT, ⟨x, hxP⟩⟩, hxP⟩⟩
    · intro hx
      obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hPS, hxP⟩ := Set.mem_iUnion.mp hxP
      have hminimal := hTP P (Finset.mem_filter.mp hPS).1
      exact ⟨hxP f (hminimal.le (polynomialSectionIdeal_first_mem f g)),
        hxP g (hminimal.le (polynomialSectionIdeal_second_mem f g))⟩
  · have hsumT : (∑ P ∈ T, d P) = ∑ P, δ P := by
      rw [← Finset.sum_coe_sort T d]
      exact Finset.sum_congr rfl (fun P _ => hd P)
    calc
      _ ≤ ∑ P ∈ T, d P :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by intros; omega)
      _ = _ := hsumT
      _ ≤ _ := hsumδ
  · intro P hPS
    exact hTP P (Finset.mem_filter.mp hPS).1

end
end CCDN
