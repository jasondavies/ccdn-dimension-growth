module

public import CCDN.HypersurfaceMultiplicityEstimate
public import CCDN.PlaneMultiplicity

/-! Singular local determinant bounds at a residue point in arbitrary
dimension. Multiplicity is obtained from the first nonzero translated homogeneous
component. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma eval_originShift {R σ : Type*} [CommRing R] (a x : σ → R)
    (f : MvPolynomial σ R) :
    eval x (originShift a f) = eval (fun j => x j + a j) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [originShift]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f j hf =>
    simp only [map_mul]
    rw [hf]
    simp [originShift]

lemma eval_sub_originShift {R σ : Type*} [CommRing R] (a x : σ → R)
    (f : MvPolynomial σ R) :
    eval (fun j => x j - a j) (originShift a f) = eval x f := by
  rw [eval_originShift]
  simp only [sub_add_cancel]

/-- A reduced hypersurface point determines a positive, degree-bounded
multiplicity in every ambient dimension. -/
theorem exists_hypersurface_reduction_multiplicity {p : ℕ} [Fact p.Prime] {σ : Type*}
    (f : MvPolynomial σ ℤ) (a : σ → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) f ≠ 0)
    (ha : eval₂ (Int.castRingHom (ZMod p)) (fun j => (a j : ZMod p)) f = 0) :
    ∃ μ : ℕ, 0 < μ ∧ μ ≤ f.totalDegree ∧
      map (Int.castRingHom (ZMod p)) (originShift a f) ∈ idealOfVars σ (ZMod p) ^ μ ∧
      homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0 := by
  let φ := Int.castRingHom (ZMod p)
  have hshift := originShift_map φ a f
  have hn : map φ (originShift a f) ≠ 0 := by
    rw [hshift]
    exact originShift_ne_zero _ hf
  have hz : eval (0 : σ → ZMod p) (map φ (originShift a f)) = 0 := by
    rw [hshift, eval_zero_originShift, eval_map]
    exact ha
  have he : map φ (originShift a f) =
      eval₂Hom (C.comp φ) (fun j => X j + C (φ (a j))) f := by
    rw [hshift]
    exact eval₂Hom_map_hom φ _ C f
  have hdeg : (map φ (originShift a f)).totalDegree ≤ f.totalDegree := by
    rw [he]
    apply linear_eval₂_totalDegree_le
    intro j
    exact (totalDegree_add _ _).trans
      (max_le (le_of_eq (totalDegree_X _)) (by rw [totalDegree_C]; omega))
  obtain ⟨μ, hpos, hμdeg, hpow, hμ⟩ := exists_origin_multiplicity _ hn hz
  exact ⟨μ, hpos, hμdeg.trans hdeg, hpow, hμ⟩

/-- Translation carries the finite-precision determinant theorem to any
residue class. Its divisor and its precision use the same explicit exponent. -/
theorem hypersurface_residue_pow_dvd_det_mod {p n μ s : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 2)) ℤ) (a : Fin (n + 2) → ℤ)
    (hf : map (Int.castRingHom (ZMod p)) (originShift a f) ∈
      idealOfVars (Fin (n + 2)) (ZMod p) ^ μ)
    (hμ : homogeneousComponent μ (map (Int.castRingHom (ZMod p)) (originShift a f)) ≠ 0)
    (x : Fin s → Fin (n + 2) → ℤ) (hx : ∀ i j, (p : ℤ) ∣ x i j - a j)
    (hfx : ∀ i, (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣ eval (x i) f)
    (F : Fin s → MvPolynomial (Fin (n + 2)) ℤ) :
    (p : ℤ) ^ hypersurfaceMultiplicityExponent (n + 1) μ s ∣
      (Matrix.of fun i j => eval (x i) (F j)).det := by
  have h := hypersurface_pow_dvd_det_mod (originShift a f) hf hμ
    (fun i j => x i j - a j) hx
    (fun i => by simpa only [eval_sub_originShift] using hfx i)
    (fun j => originShift a (F j))
  simpa only [eval_sub_originShift] using h

end
end CCDN
