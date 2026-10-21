/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.AffineCongruenceAuxiliary
public import CCDN.Hilbert.PrincipalStandardMonomials
import CCDN.Auxiliary.HypersurfaceRankProfile
import CCDN.Auxiliary.PlaneAuxiliaryCount
import CCDN.Surface.SurfaceMonomialWeight
/-! The full standard-monomial prefix produces a proper integer auxiliary
on the entire bounded surface congruence class, with the sharp weighted
degree in the sole remaining numerical gap. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

def affineCongruencePoints {n : ℕ} (f : MvPolynomial (Fin n) ℤ)
    (B : ℝ) (P : Finset ℕ) (a : ℕ → IntPoint n) : Finset (IntPoint n) := by
  classical
  exact (integerBox n B).filter (fun x =>
    eval x f = 0 ∧ ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j)

lemma mem_affineCongruencePoints {n : ℕ} {f : MvPolynomial (Fin n) ℤ}
    {B : ℝ} {P : Finset ℕ} {a : ℕ → IntPoint n} {x : IntPoint n} :
    x ∈ affineCongruencePoints f B P a ↔
      (∀ j, |(x j : ℝ)| ≤ B) ∧ eval x f = 0 ∧
        ∀ p ∈ P, ∀ j, (p : ℤ) ∣ x j - a p j := by
  classical
  simp only [affineCongruencePoints, mem_filter, mem_integerBox]

def surfaceCongruenceRank (f : MvPolynomial (Fin 3) ℤ) (M : ℕ) : ℕ :=
  (standardMonomialPrefix (Ideal.span {map (Int.castRingHom ℚ) f})
    MonomialOrder.degLex M).card

def surfaceWeightedDeterminantUpper (d s : ℕ) (B : ℝ) : ℝ :=
  Real.log (s.factorial : ℝ) +
    ((2 / 3 : ℝ) * s * Real.sqrt (2 * s / (d : ℝ)) + (2 * d + 2) * s) * Real.log B

theorem surface_congruence_rank_power_bounds
    (f : MvPolynomial (Fin 3) ℤ) (hf : f ≠ 0) {M : ℕ}
    (hM : f.totalDegree ≤ M) :
    (f.totalDegree : ℝ) * ((M : ℝ) - f.totalDegree + 1) ^ 2 / 2 ≤
      surfaceCongruenceRank f M ∧
    (surfaceCongruenceRank f M : ℝ) ≤
      (f.totalDegree : ℝ) * ((M : ℝ) + 2) ^ 2 / 2 := by
  have hdegree : (map (Int.castRingHom ℚ) f).totalDegree = f.totalDegree :=
    rational_map_totalDegree f
  have hfQ : map (Int.castRingHom ℚ) f ≠ 0 := by
    intro h
    exact hf ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa using h))
  have hr := principal_standard_prefix_rank (map (Int.castRingHom ℚ) f)
    hfQ (hdegree ▸ hM)
  rw [hdegree] at hr
  have hb := hypersurface_rank_power_bounds hM hr
  norm_num at hb
  exact hb

/-- All bounded integer zeros in specified smooth residue classes lie on
a proper auxiliary. The degree criterion is entirely numerical. -/
theorem exists_surface_congruence_auxiliary_of_gap
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom (AlgebraicClosure ℚ)) f))
    (hd : 0 < f.totalDegree) (H : ℝ) (hH : 1 ≤ H)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    {M : ℕ} (hM : f.totalDegree ≤ M)
    {B : ℝ} (hB : 1 ≤ B)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → IntPoint 3)
    (ha : ∀ p ∈ P, eval₂ (Int.castRingHom (ZMod p)) (fun j => (a p j : ZMod p)) f = 0)
    (hsmooth : ∀ p ∈ P, ∃ j, eval (fun i => (a p i : ZMod p))
      (pderiv j (map (Int.castRingHom (ZMod p)) f)) ≠ 0)
    (hgap : surfaceWeightedDeterminantUpper f.totalDegree (surfaceCongruenceRank f M) B <
      affineCongruenceDeterminantLower 1 f.totalDegree (surfaceCongruenceRank f M)
        H (∑ p ∈ P, Real.log p)) :
    ∃ g : MvPolynomial (Fin 3) ℤ, g ≠ 0 ∧
      ¬ map (Int.castRingHom ℚ) f ∣ map (Int.castRingHom ℚ) g ∧
      g.totalDegree ≤ M ∧ ∀ x ∈ affineCongruencePoints f B P a, eval x g = 0 := by
  classical
  let fQ := map (Int.castRingHom ℚ) f
  let S := standardMonomialPrefix (Ideal.span {fQ}) MonomialOrder.degLex M
  let e := (Fintype.equivFin S).symm
  let mon : Fin (Fintype.card S) → (Fin 3 →₀ ℕ) := fun j => (e j).val
  have hc : Fintype.card S = surfaceCongruenceRank f M := Fintype.card_coe S
  have hdegree : fQ.totalDegree = f.totalDegree :=
    rational_map_totalDegree f
  have hf : f ≠ 0 := by intro h; exact hir.ne_zero (by rw [h, map_zero])
  have hfQ : fQ ≠ 0 := by
    intro h
    exact hf ((map_injective (Int.castRingHom ℚ) Int.cast_injective) (by simpa [fQ] using h))
  have hN : 0 < Fintype.card S := by
    rw [hc]
    have hb := (surface_congruence_rank_power_bounds f hf hM).1
    have hdR : (0 : ℝ) < f.totalDegree := by exact_mod_cast hd
    have hMR : (f.totalDegree : ℝ) ≤ M := by exact_mod_cast hM
    have hbase : 0 < ((M : ℝ) - f.totalDegree + 1) ^ 2 := by positivity
    have hpos : (0 : ℝ) < surfaceCongruenceRank f M := lt_of_lt_of_le
      (by positivity : (0 : ℝ) < (f.totalDegree : ℝ) *
        ((M : ℝ) - f.totalDegree + 1) ^ 2 / 2) hb
    exact_mod_cast hpos
  have hmon : Function.Injective mon := Subtype.val_injective.comp e.injective
  have hstd (j) : mon j ∈ Ideal.standardExponents (Ideal.span {fQ}) MonomialOrder.degLex :=
    (mem_standardMonomialPrefix _ _ _ _).mp (e j).property |>.1
  have hdeg (j) : Finsupp.degree (mon j) ≤ M :=
    (mem_standardMonomialPrefix _ _ _ _).mp (e j).property |>.2
  have hweight : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) ≤
      (2 / 3 : ℝ) * Fintype.card S *
        Real.sqrt (2 * Fintype.card S / (f.totalDegree : ℝ)) +
          (2 * f.totalDegree + 2) * Fintype.card S := by
    have hw := surface_standard_monomial_weight fQ hfQ (hdegree ▸ hd) (hdegree ▸ hM)
    change (∑ j ∈ S, ((Finsupp.degree j : ℕ) : ℝ)) ≤ _ at hw
    have hsum : (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) =
        ∑ j ∈ S, ((Finsupp.degree j : ℕ) : ℝ) := by
      rw [← Finset.sum_coe_sort S]
      exact e.sum_comp (fun j : S => ((Finsupp.degree j.val : ℕ) : ℝ))
    rw [hsum, Fintype.card_coe, ← hdegree]
    exact hw
  have hgap' : Real.log ((Fintype.card S).factorial : ℝ) +
      (∑ j, ((Finsupp.degree (mon j) : ℕ) : ℝ)) * Real.log B <
      affineCongruenceDeterminantLower 1 f.totalDegree (Fintype.card S)
        H (∑ p ∈ P, Real.log p) := by
    apply lt_of_le_of_lt (add_le_add_right
      (mul_le_mul_of_nonneg_right hweight (Real.log_nonneg hB)) _)
    simpa only [hc, surfaceWeightedDeterminantUpper] using hgap
  let X := affineCongruencePoints f B P a
  let ex := (Fintype.equivFin X).symm
  let x : Fin (Fintype.card X) → IntPoint 3 := fun i => (ex i).val
  have hx (i) := mem_affineCongruencePoints.mp (ex i).property
  obtain ⟨g, hg0, hgnd, hgdeg, hgz⟩ :=
    exists_affine_congruence_auxiliary_of_gap hN f hir hd H hH hcoeff mon hmon hstd hdeg
      ⟨hB, fun i => (hx i).2.1, fun i j => (hx i).1 j⟩ P a
      ⟨hP, ha, hsmooth, fun p hp i j => (hx i).2.2 p hp j⟩ hgap'
  refine ⟨g, hg0, hgnd, hgdeg, ?_⟩
  intro y hy
  obtain ⟨i, hi⟩ := ex.surjective ⟨y, hy⟩
  have hh := hgz i
  change eval (ex i).val g = 0 at hh
  simpa only [hi] using hh

end
end CCDN
