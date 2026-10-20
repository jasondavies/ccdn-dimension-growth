module

public import AffineCurveCounting.ProjectiveMultiplicity

/-! Sharp prime-power and global prime-sum bounds for projective plane
evaluation matrices. All local geometry and finite-field estimates are
proved; the remaining excluded-prime set is explicit. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial Finset

theorem projectivePlaneTotalMultiplicity_sharp {p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : 27 * (d : ℝ) ^ 4 < p) :
    (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      p + 165 * (d : ℝ) ^ 2 * Real.sqrt p := by
  have hp : 27 * d ^ 4 < p := by exact_mod_cast hsize
  have hchar : d < p := by
    have h1 := Nat.le_mul_self d
    have h2 := Nat.le_mul_self (d * d)
    nlinarith only [hp, h1, h2]
  have hmass := projectivePlaneTotalMultiplicity_le_card_add_correction f hf hd hir hchar
  have hmassR : (projectivePlaneTotalMultiplicity f hf hir.ne_zero : ℝ) ≤
      Fintype.card (ProjectivePlaneResidue f p) + (3 * d ^ 2 * (d - 1) : ℕ) := by
    exact_mod_cast hmass
  have hc := projective_plane_finite_field_card_bound f hf hd hir hsize
  have hcorr := singular_correction_absorb (show 0 < d by omega)
    (L := 27 * (d : ℝ) ^ 4)
    (show (d : ℝ) ^ 4 ≤ 27 * (d : ℝ) ^ 4 by nlinarith [sq_nonneg ((d : ℝ) ^ 2)])
    hsize
  push_cast at hmassR hcorr
  nlinarith

/-- A uniform local exponent with no caller-supplied point-count bound. -/
theorem projective_reduction_minorGcd_sharp {s N p d M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (hir : Irreducible (map (Int.castRingHom (ZMod p)) f))
    (hsize : 27 * (d : ℝ) ^ 4 < p)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0) :
    ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * (p + 165 * (d : ℝ) ^ 2 * Real.sqrt p)) - s ≤ e ∧
      (p : ℤ) ^ e ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  obtain ⟨hpos, e, _, he, hdiv⟩ := projective_reduction_minorGcd hs f hf hir.ne_zero
    F hF z hprim hz
  have hm := projectivePlaneTotalMultiplicity_sharp f hf hd hir hsize
  refine ⟨e, ?_, hdiv⟩
  apply le_trans (sub_le_sub_right ?_ (s : ℝ)) he
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  exact mul_le_mul_of_nonneg_left hm (by norm_num)

/-- The fourth-power cutoff costs only four logarithms of the degree and
an absolute constant, even with singular projective residue classes. -/
theorem projective_determinant_log_lower_degree_four {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    {x : ℝ} (hx : 1 ≤ x) (bad : Finset ℕ)
    (hred : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad,
      27 * (d : ℝ) ^ 4 < p → Irreducible (map (Int.castRingHom (ZMod p)) f)) :
    (s : ℝ) ^ 2 / 2 * (Real.log x - 4 * Real.log d - Real.log 27 - 2 * mertensError -
      (∑ p ∈ bad, Real.log p / p) - 330 * primeBlockMass) -
      s * ((Real.log 4 + 4) * x) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  classical
  let L : ℝ := 27 * (d : ℝ) ^ 4
  let S := (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ bad).filter (fun p : ℕ => L < p)
  let D := Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))
  let mass : ℕ → ℝ := fun p => p + 165 * (d : ℝ) ^ 2 * Real.sqrt p
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hL : 1 ≤ L := by
    dsimp [L]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hd1 4
    norm_num at hh
    linarith
  have hp (p : ℕ) (h : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp h).1).1).2
  have hlocal (p : ℕ) (h : p ∈ S) :
      ∃ e : ℕ, (s : ℝ) ^ 2 / (2 * mass p) - s ≤ e ∧ (p : ℤ) ^ e ∣ D := by
    let : Fact p.Prime := ⟨hp p h⟩
    exact projective_reduction_minorGcd_sharp hs f hf hd
      (hred p (mem_filter.mp h).1 (mem_filter.mp h).2) (mem_filter.mp h).2 F hF z hprim hz
  let e : ℕ → ℕ := fun p => if h : p ∈ S then (hlocal p h).choose else 0
  have hh := determinant_log_lower_cutoff hx hL
    (show 0 ≤ 165 * (d : ℝ) ^ 2 by positivity) bad mass s e
    (D := D) (lt_of_lt_of_le (by norm_num) (Int.Matrix.one_le_minorGcd hrows)) ?_ ?_ ?_ ?_
  · have hsqrt : (d : ℝ) ^ 2 ≤ Real.sqrt L := by
      apply Real.le_sqrt_of_sq_le
      dsimp [L]
      nlinarith [sq_nonneg ((d : ℝ) ^ 2)]
    have htail : 165 * (d : ℝ) ^ 2 * (2 * primeBlockMass / Real.sqrt L) ≤
        330 * primeBlockMass := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
      have h := mul_le_mul_of_nonneg_left hsqrt
        (show 0 ≤ 330 * primeBlockMass from mul_nonneg (by norm_num) primeBlockMass_pos.le)
      nlinarith
    have hlog : Real.log L = Real.log 27 + 4 * Real.log d := by
      dsimp only [L]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    rw [hlog] at hh
    have hmul := mul_le_mul_of_nonneg_left htail (show 0 ≤ (s : ℝ) ^ 2 / 2 by positivity)
    dsimp only [D] at hh
    nlinarith
  · intro p hp hcut
    have hprime := (mem_filter.mp (mem_sdiff.mp hp).1).2
    have hpos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    dsimp [mass]
    positivity
  · intro p _ _
    exact le_rfl
  · intro p hp hcut
    have hmem : p ∈ S := mem_filter.mpr ⟨hp, hcut⟩
    rw [show e p = (hlocal p hmem).choose from dite_eq_left hmem]
    exact (hlocal p hmem).choose_spec.1
  · intro p hp hcut
    have hmem : p ∈ S := mem_filter.mpr ⟨hp, hcut⟩
    rw [show e p = (hlocal p hmem).choose from dite_eq_left hmem]
    exact (hlocal p hmem).choose_spec.2

theorem projective_determinant_log_lower_at_rank {s N d M : ℕ} (hs : 0 < s)
    (f : MvPolynomial (Fin 3) ℤ) (hf : f.IsHomogeneous d) (hd : 2 ≤ d)
    (F : Fin N → MvPolynomial (Fin 3) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint 3) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (hrows : LinearIndependent ℚ
      ((Matrix.of fun i j => eval (z i) (F j)).map ((↑) : ℤ → ℚ)).row)
    (bad : Finset ℕ)
    (hred : ∀ p ∈ ((Ioc 0 s).filter Nat.Prime) \ bad,
      27 * (d : ℝ) ^ 4 < p → Irreducible (map (Int.castRingHom (ZMod p)) f)) :
    (s : ℝ) ^ 2 / 2 * (Real.log s - 4 * Real.log d -
      (∑ p ∈ bad, Real.log p / p) - degreeFourDeterminantError 164) ≤
        Real.log (Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j))) := by
  have h := projective_determinant_log_lower_degree_four hs f hf hd F hF z hprim hz hrows
    (x := (s : ℝ)) (by exact_mod_cast hs) bad
    (by simpa only [Nat.floor_natCast] using hred)
  convert h using 1
  dsimp only [degreeFourDeterminantError]
  ring

end
end AffineCurveCounting
