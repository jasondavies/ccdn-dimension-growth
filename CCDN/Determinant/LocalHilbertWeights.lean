/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Determinant.HypersurfacePointStalk
public import CCDN.Determinant.FiltrationWeights
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Determinant.WeightedSequenceEstimate
import CCDN.Determinant.InfiniteWeightEnumeration
import CCDN.Determinant.PlaneMultiplicity
import CCDN.AuxiliaryPolynomial.AffineTranslationCount
/-! The exact local weight-sequence estimate for hypersurface stalks.
The uniform error is dimension plus one. Every positive-dimensional
hypersurface has a constructed infinite enumeration of its layers;
neither the multiplicity nor an external Hilbert-function estimate is needed
in the final existence theorem. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

variable {K : Type*} [Field K]

def hypersurfacePointLayerDimension {n : ℕ}
    (f : MvPolynomial (Fin n) K) (a : Fin n → K) [Fact (eval a f = 0)] (k : ℕ) : ℕ :=
  Module.finrank K (Ideal.powerLayer K (A := HypersurfacePointStalk f a)
    (IsLocalRing.maximalIdeal (HypersurfacePointStalk f a)) k)

lemma hypersurfaceLayerBound_positive (n k : ℕ) {μ : ℕ} (hμ : 0 < μ) :
    0 < hypersurfaceLayerBound (n + 1) μ k := by
  obtain ⟨μ, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hμ.ne'
  cases k with
  | zero => rw [hypersurfaceLayerBound_succ_zero]; exact zero_lt_one
  | succ k =>
    rw [hypersurfaceLayerBound_succ_succ]
    exact Nat.add_pos_left (Nat.choose_pos (by omega)) _

/-- CCDN 2.3 for the first s weights of the local ring. This uses the
true hypersurface cumulative profile, so it includes dimension one without
the false arbitrary-profile extension of the printed Lemma 2.2. -/
theorem hypersurfacePointStalk_initial_weights_sum_lower_bound {n μ s : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K) (a : Fin (n + 2) → K)
    [Fact (eval a f = 0)] (hpos : 0 < μ)
    (hf : affineTranslation K a f ∈ idealOfVars (Fin (n + 2)) K ^ μ)
    (hμ : homogeneousComponent μ (affineTranslation K a f) ≠ 0)
    (w : Fin s → ℕ) (hw : IsInitialWeightSegment (hypersurfacePointLayerDimension f a) w) :
    (((n + 1).factorial : ℝ) / μ) ^ (1 / (n + 1 : ℝ)) * (n + 1) / (n + 2) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) - (n + 2 : ℝ) * s ≤ ∑ i, (w i : ℝ) := by
  have hcap (k : ℕ) : (Finset.univ.filter fun i => w i ≤ k).card ≤
      μ * (n + 1 + k).choose (n + 1) := by
    rw [hw k]
    apply (Nat.min_le_right _ _).trans
    have hc := originLayer_cumulative_le (affineTranslation K a f) hf hμ k
    rw [Fin.sum_univ_eq_sum_range
      (fun j => Module.finrank K (originLayer (affineTranslation K a f) j))] at hc
    simpa only [weightProfileCumulative, hypersurfacePointLayerDimension,
      hypersurfacePointStalkLayer_finrank, Nat.add_assoc, Nat.add_comm k 1] using hc
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
    weights_sum_lower_bound_of_cumulative w (n + 1) μ (by omega) hpos hcap

/-- CCDN 2.3 for the first `s` terms of a monotone enumeration of the weights whose level
counts are the local layer dimensions. -/
theorem hypersurfacePointStalk_enumerated_weights_sum_lower_bound {n μ s : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K) (a : Fin (n + 2) → K)
    [Fact (eval a f = 0)] (hpos : 0 < μ)
    (hf : affineTranslation K a f ∈ idealOfVars (Fin (n + 2)) K ^ μ)
    (hμ : homogeneousComponent μ (affineTranslation K a f) ≠ 0)
    (w : ℕ → ℕ) (hw : Monotone w)
    (hfinite : ∀ k, {i | w i = k}.Finite)
    (hcount : ∀ k, {i | w i = k}.ncard = hypersurfacePointLayerDimension f a k) :
    (((n + 1).factorial : ℝ) / μ) ^ (1 / (n + 1 : ℝ)) * (n + 1) / (n + 2) *
      (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) - (n + 2 : ℝ) * s ≤
        ∑ i : Fin s, (w i.val : ℝ) :=
  hypersurfacePointStalk_initial_weights_sum_lower_bound f a hpos hf hμ _
    (monotone_enumeration_isInitialWeightSegment w _ hw hfinite hcount s)

/-- Construct the multiplicity, the exact Hilbert profile and its infinite
weight enumeration directly from a nonzero equation through the point. -/
theorem exists_hypersurfacePointStalk_hilbert_weights {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) K) (a : Fin (n + 2) → K)
    [Fact (eval a f = 0)] (hf0 : f ≠ 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      (∀ k, hypersurfacePointLayerDimension f a k = hypersurfaceLayerBound (n + 1) μ k) ∧
      ∃ w : ℕ → ℕ, Monotone w ∧
        (∀ k, {i | w i = k}.Finite) ∧
        (∀ k, {i | w i = k}.ncard = hypersurfacePointLayerDimension f a k) ∧
        ∀ s : ℕ,
          (((n + 1).factorial : ℝ) / μ) ^ (1 / (n + 1 : ℝ)) * (n + 1) / (n + 2) *
            (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) - (n + 2 : ℝ) * s ≤
              ∑ i : Fin s, (w i.val : ℝ) := by
  have hT0 : affineTranslation K a f ≠ 0 :=
    (affineTranslation K a).injective.ne (by simpa using hf0)
  have hTzero : eval (0 : Fin (n + 2) → K) (affineTranslation K a f) = 0 := by
    rw [eval_zero, constantCoeff_eq, affineTranslation_constantCoeff]
    exact Fact.out
  obtain ⟨μ, hpos, hdeg, hf, hμ⟩ :=
    exists_origin_multiplicity (affineTranslation K a f) hT0 hTzero
  rw [affineTranslation_totalDegree] at hdeg
  have hprofile (k) : hypersurfacePointLayerDimension f a k =
      hypersurfaceLayerBound (n + 1) μ k :=
    hypersurfacePointStalk_hilbert_eq f a hf hμ
  have hpositive (k) : 0 < hypersurfacePointLayerDimension f a k := by
    rw [hprofile]
    exact hypersurfaceLayerBound_positive n k hpos
  obtain ⟨w, hw, hfinite, hcount, _⟩ :=
    exists_positive_profile_enumeration (hypersurfacePointLayerDimension f a) hpositive
  exact ⟨μ, hpos, hdeg, hprofile, w, hw, hfinite, hcount,
    fun _ => hypersurfacePointStalk_enumerated_weights_sum_lower_bound f a hpos hf hμ w hw hfinite hcount⟩

end
end CCDN
