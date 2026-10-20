module

public import CCDN.GridTopFormConstruction
public import CCDN.GridAffineLowerBound
public import CCDN.GridProjectiveLowerBound
public import CCDN.PolynomialPredicates

/-! Integer hypersurfaces with absolutely irreducible top forms and
large affine and projective point counts. These constructions apply to the
hypotheses of CCDN Theorem 4 as well as to projective dimension growth. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma exists_integer_topform_grid_equation (s : Finset ℤ) (d n : ℕ)
    (hd : 1 ≤ d) (hn : 3 ≤ n) (hs : s.card ≤ d - 1) :
    ∃ f : MvPolynomial (Fin n) ℤ,
      f.totalDegree = d ∧
        HasAbsIrreducibleTopForm f ∧
        ∀ z : IntPoint n, (∀ j, z j ∈ s) → eval z f = 0 := by
  let i : Fin 3 → Fin n := Fin.castLE hn
  have hi : Function.Injective i := Fin.castLE_injective hn
  let r := Function.invFun i
  have hr : Function.LeftInverse r i := Function.leftInverse_invFun hi
  let g := gridTopFormEquation s d
  have hgdeg : g.totalDegree = d := gridTopFormEquation_totalDegree s hd hs
  refine ⟨rename i g, ?_, ?_, ?_⟩
  · rw [totalDegree_rename_of_leftInverse i r hr, hgdeg]
  · dsimp only [HasAbsIrreducibleTopForm]
    rw [totalDegree_rename_of_leftInverse i r hr, ← rename_homogeneousComponent, map_rename]
    exact irreducible_rename_of_injective i hi _ (gridTopFormEquation_absolute_top s hd hs)
  · intro z hz
    rw [eval_rename]
    exact gridTopFormEquation_eval_zero s d (z ∘ i) (hz (i 1)) (hz (i 2))

lemma integer_absolute_top_rational_model {n d : ℕ}
    (f : MvPolynomial (Fin n) ℤ) (hd : f.totalDegree = d)
    (htop : HasAbsIrreducibleTopForm f) :
    (map (Int.castRingHom ℚ) f).totalDegree = d ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) f)) := by
  refine ⟨?_, ?_⟩
  · unfold totalDegree
    rw [support_map_of_injective _ Int.cast_injective]
    exact hd
  · have h := (map_degree_and_irreducible_of_top_irreducible
      (Int.castRingHom (AlgebraicClosure ℚ)) f htop).2
    rw [map_map]
    have he : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (Int.castRingHom ℚ) =
        Int.castRingHom (AlgebraicClosure ℚ) := by ext; simp
    rwa [he]

lemma grid_box_power_lower_bounds {d n B : ℕ} (hn : 2 ≤ n) (hB : 1 ≤ B) (hdB : d ≤ 8 * B) :
    ((d : ℝ) ^ 2 / 64) * (B : ℝ) ^ (n - 2) ≤ ((2 * B + 1 : ℕ) : ℝ) ^ n ∧
      ((d : ℝ) / 8) * (B : ℝ) ^ (n - 1) ≤ ((2 * B + 1 : ℕ) : ℝ) ^ n := by
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hdR : (d : ℝ) ≤ 8 * (B : ℝ) := by exact_mod_cast hdB
  have hsq : (d : ℝ) ^ 2 / 64 ≤ (B : ℝ) ^ 2 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg d) hdR 2
    nlinarith
  have hlarge : (B : ℝ) ^ n ≤ ((2 * B + 1 : ℕ) : ℝ) ^ n := by
    apply pow_le_pow_left₀ hB0
    exact_mod_cast (show B ≤ 2 * B + 1 by omega)
  constructor
  · calc
      _ ≤ (B : ℝ) ^ 2 * (B : ℝ) ^ (n - 2) :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = (B : ℝ) ^ n := by rw [← pow_add]; congr 1; omega
      _ ≤ _ := hlarge
  · calc
      _ ≤ (B : ℝ) * (B : ℝ) ^ (n - 1) :=
        mul_le_mul_of_nonneg_right (by linarith : (d : ℝ) / 8 ≤ B) (by positivity)
      _ = (B : ℝ) ^ n := by rw [← pow_succ']; congr 1; omega
      _ ≤ _ := hlarge

/-- For d≥4 and n≥3, an integer equation satisfying the absolute top-form
hypothesis has at least d²B^(n−2)/64 affine points. Its homogeneous
closure simultaneously has at least dB^(n−1)/8 projective points. -/
theorem exists_topform_hypersurface_lower_bounds (d n : ℕ) (hd : 4 ≤ d) (hn : 3 ≤ n) :
    ∃ f : MvPolynomial (Fin n) ℤ, ∃ B : ℕ,
      1 ≤ B ∧ B ≤ d ∧ d ≤ 8 * B ∧ f.totalDegree = d ∧
      HasAbsIrreducibleTopForm f ∧
      Irreducible (map (algebraMap ℚ (AlgebraicClosure ℚ)) (map (Int.castRingHom ℚ) f)) ∧
      ((d : ℝ) ^ 2 / 64) * (B : ℝ) ^ (n - 2) ≤
        (count (zeroLocus (map (Int.castRingHom ℚ) f)) B : ℝ) ∧
      ((d : ℝ) / 8) * (B : ℝ) ^ (n - 1) ≤
        (projectiveCount (projectiveZeroLocus
          (boundedHomogenize d (map (Int.castRingHom ℚ) f))) B : ℝ) := by
  classical
  let B := d / 4
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBd : B ≤ d := by dsimp [B]; omega
  have hdB : d ≤ 8 * B := by dsimp [B]; omega
  let s : Finset ℤ := Finset.Icc (-(B : ℤ)) (B : ℤ)
  have hs : s.card = 2 * B + 1 := by rw [Int.card_Icc]; omega
  have hsd : s.card ≤ d - 1 := by rw [hs]; dsimp [B]; omega
  obtain ⟨f, hfdeg, hftop, hfzero⟩ := exists_integer_topform_grid_equation s d n (by omega) hn hsd
  obtain ⟨hQdeg, hQir⟩ := integer_absolute_top_rational_model f hfdeg hftop
  have hsbound : ∀ a ∈ s, |(a : ℝ)| ≤ (B : ℝ) := by
    intro a ha
    have h := abs_le.mpr (Finset.mem_Icc.mp ha)
    exact_mod_cast h
  have hzeroQ : ∀ z : IntPoint n, (∀ j, z j ∈ s) →
      eval (rationalPoint z) (map (Int.castRingHom ℚ) f) = 0 := by
    intro z hz
    have hh := congrArg (Int.castRingHom ℚ) (hfzero z hz)
    rw [map_eval, map_zero] at hh
    exact hh
  have hca := integer_grid_le_affine_count (map (Int.castRingHom ℚ) f) s hsbound hzeroQ
  have hcp := integer_grid_le_projective_count (map (Int.castRingHom ℚ) f) hQdeg.le s
    (by exact_mod_cast hB) hsbound hzeroQ
  rw [hs] at hca hcp
  obtain ⟨ha, hp⟩ := grid_box_power_lower_bounds (d := d) (n := n) (by omega) hB hdB
  refine ⟨f, B, hB, hBd, hdB, hfdeg, hftop, hQir, ?_, ?_⟩
  · exact ha.trans (by exact_mod_cast hca)
  · exact hp.trans (by exact_mod_cast hcp)

end
end CCDN
