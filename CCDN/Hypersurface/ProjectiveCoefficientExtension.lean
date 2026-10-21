/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Hypersurface.NonRationalProjectiveCount
/-! Rational projective points embed injectively after a coefficient-field
extension. Homogeneous ideal equations remain zero on every representative. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def coefficientExtensionVector (k K σ : Type*) [Field k] [Field K] [Algebra k K] :
    (σ → k) →ₛₗ[algebraMap k K] (σ → K) where
  toFun v := algebraMap k K ∘ v
  map_add' v w := by funext i; simp
  map_smul' a v := by funext i; simp

lemma coefficientExtensionVector_injective
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] :
    Function.Injective (coefficientExtensionVector k K σ) := by
  intro v w h
  funext i
  exact (algebraMap k K).injective (congrFun h i)

def projectiveCoefficientExtension
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] :
    Projectivization k (σ → k) → Projectivization K (σ → K) :=
  Projectivization.map (coefficientExtensionVector k K σ)
    (coefficientExtensionVector_injective k K σ)

theorem projectiveCoefficientExtension_injective
    (k K σ : Type*) [Field k] [Field K] [Algebra k K] :
    Function.Injective (projectiveCoefficientExtension k K σ) := by
  intro x y h
  induction x using Projectivization.ind with
  | h v hv =>
    induction y using Projectivization.ind with
    | h w hw =>
      change Projectivization.map _ _ _ = Projectivization.map _ _ _ at h
      rw [Projectivization.map_mk, Projectivization.map_mk,
        Projectivization.mk_eq_mk_iff'] at h
      obtain ⟨a, ha⟩ := h
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hw
      change w j ≠ 0 at hj
      have hwj : algebraMap k K (w j) ≠ 0 := by
        simpa only [map_zero] using (algebraMap k K).injective.ne hj
      have hc : algebraMap k K (v j / w j) = a := by
        rw [map_div₀]
        apply (div_eq_iff hwj).mpr
        exact (congrFun ha j).symm
      apply (Projectivization.mk_eq_mk_iff' k v w hv hw).mpr
      refine ⟨v j / w j, ?_⟩
      funext i
      apply (algebraMap k K).injective
      change algebraMap k K (v j / w j * w i) = algebraMap k K (v i)
      rw [map_mul, hc]
      exact congrFun ha i

theorem projectiveCoefficientExtension_mem_ideal
    {K : Type*} [Field K] [Algebra ℚ K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin (n + 1)) K))
    (hI : IsHomogeneousIdeal I)
    (x : ProjectivePoint n) (hx : x ∈ rationalProjectiveIdealZeroLocusOver I) :
    projectiveCoefficientExtension ℚ K (Fin (n + 1)) x ∈ projectiveIdealZeroLocus I := by
  intro v hv he f hf
  have hw0 : coefficientExtensionVector ℚ K (Fin (n + 1)) x.rep ≠ 0 := by
    intro h
    apply x.rep_nonzero
    apply coefficientExtensionVector_injective ℚ K (Fin (n + 1))
    simpa only [map_zero] using h
  have he' : Projectivization.mk K v hv =
      Projectivization.mk K (coefficientExtensionVector ℚ K (Fin (n + 1)) x.rep)
        hw0 := by
    rw [he]
    conv_lhs => rw [← x.mk_rep]
    rfl
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K _ _ _ _).mp he'
  rw [← ha]
  exact homogeneous_ideal_eval_smul I hI _ (hx x.rep x.rep_nonzero x.mk_rep) a f hf

end
end CCDN
