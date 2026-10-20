module

public import AffineCurveCounting.SharpHypersurfaceDeterminant
public import AffineCurveCounting.InitialFormMultiplication

/-! Sharp determinant divisibility on an open part of a reduced hypersurface.
A factor supported outside all supplied residue points does not contribute
residue classes. In particular, components at infinity created by a degree
loss in an affine reduction need not be declared bad. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma initial_form_mul_constant_nonzero {K σ : Type*} [Field K]
    {g h : MvPolynomial σ K} {μ : ℕ}
    (hg : g ∈ idealOfVars σ K ^ μ) (hμ : homogeneousComponent μ g ≠ 0)
    (hh : h.constantCoeff ≠ 0) :
    g * h ∈ idealOfVars σ K ^ μ ∧ homogeneousComponent μ (g * h) ≠ 0 := by
  refine ⟨(idealOfVars σ K ^ μ).mul_mem_right h hg, ?_⟩
  have hzero : h ∈ idealOfVars σ K ^ 0 := by simp
  have he := first_homogeneousComponent_mul hg hzero
  simp only [Nat.add_zero] at he
  rw [he]
  apply mul_ne_zero hμ
  rw [homogeneousComponent_zero]
  exact fun he => hh (by simpa only [constantCoeff_eq, C_eq_zero] using he)

lemma primitiveProjectiveReduction_eval_zero_mod {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    (z : IntPoint (n + 1)) (hz : Finset.univ.gcd z = 1)
    (hzero : eval (fun i => (z i : ZMod p)) (map (Int.castRingHom (ZMod p)) f) = 0) :
    eval (primitiveProjectiveReduction (p := p) z hz).rep
      (map (Int.castRingHom (ZMod p)) f) = 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep
    (ZMod p) (fun i => (z i : ZMod p)) (primitive_mod_ne_zero z hz)
  change eval (Projectivization.mk (ZMod p) _ _).rep _ = 0
  rw [← hu]
  change eval ((u : ZMod p) • (fun i => (z i : ZMod p))) _ = 0
  rw [homogeneous_eval_smul (hf.map _), hzero, mul_zero]

lemma primitiveProjectiveReduction_eval_ne_zero_mod {n p d : ℕ} [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 1)) ℤ) (hf : f.IsHomogeneous d)
    (z : IntPoint (n + 1)) (hz : Finset.univ.gcd z = 1)
    (hzero : eval (fun i => (z i : ZMod p)) (map (Int.castRingHom (ZMod p)) f) ≠ 0) :
    eval (primitiveProjectiveReduction (p := p) z hz).rep
      (map (Int.castRingHom (ZMod p)) f) ≠ 0 := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep
    (ZMod p) (fun i => (z i : ZMod p)) (primitive_mod_ne_zero z hz)
  change eval (Projectivization.mk (ZMod p) _ _).rep _ ≠ 0
  rw [← hu]
  change eval ((u : ZMod p) • (fun i => (z i : ZMod p))) _ ≠ 0
  rw [homogeneous_eval_smul (hf.map _)]
  exact mul_ne_zero (pow_ne_zero _ u.ne_zero) hzero

lemma hypersurfaceResidueChartLift_nonzero {n p d : ℕ} [Fact p.Prime]
    (h : MvPolynomial (Fin (n + 3)) ℤ) (hh : h.IsHomogeneous d)
    (r : ProjectiveResidueSpace (n + 2) p)
    (hr : eval r.rep (map (Int.castRingHom (ZMod p)) h) ≠ 0) :
    eval₂ (Int.castRingHom (ZMod p))
      (fun j => (hypersurfaceResidueChartLift r j : ZMod p))
      (projectiveHypersurfaceChart (hypersurfaceResiduePivot r) h) ≠ 0 := by
  let k := hypersurfaceResiduePivot r
  let a : Fin (n + 2) → ZMod p := fun j => (hypersurfaceResidueChartLift r j : ZMod p)
  have hv : Fin.cons 1 a = (r.rep k)⁻¹ • (r.rep ∘ Equiv.swap 0 k) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j
    · simp [hypersurfaceResiduePivot_ne_zero, k]
    · simp [a, cast_hypersurfaceResidueChartLift, div_eq_mul_inv, mul_comm, k]
  have hv' : (Fin.cons 1 a) ∘ Equiv.swap 0 k = (r.rep k)⁻¹ • r.rep := by
    rw [hv]
    funext j
    simp
  change eval₂ (Int.castRingHom (ZMod p)) a
    (affineChart (n + 2) (rename (Equiv.swap 0 k) h)) ≠ 0
  rw [eval₂_hypersurfaceAffineChart, eval₂_rename, hv', ← eval_map,
    homogeneous_eval_smul (hh.map _)]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (hypersurfaceResiduePivot_ne_zero r))) hr

lemma originShift_projectiveChart_reduction_mul {n p : ℕ}
    (f g h : MvPolynomial (Fin (n + 3)) ℤ)
    (he : map (Int.castRingHom (ZMod p)) f =
      map (Int.castRingHom (ZMod p)) g * map (Int.castRingHom (ZMod p)) h)
    (k : Fin (n + 3)) (a : Fin (n + 2) → ℤ) :
    map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k f)) =
      map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k g)) *
        map (Int.castRingHom (ZMod p)) (originShift a (projectiveHypersurfaceChart k h)) := by
  simp only [projectiveHypersurfaceChart, originShift_map, ← affineChart_map, map_rename]
  rw [he, map_mul, map_mul, map_mul]

/-- Local data are needed only for residue classes containing a supplied point.
Empty blocks contribute exponent zero. -/
theorem projective_hypersurface_residue_minorGcd_nonempty {p n c s N d M : ℕ}
    [Fact p.Prime]
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hfhom : f.IsHomogeneous d)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → Fin (n + 3) → ℤ) (label : Fin s → Fin c)
    (k : Fin c → Fin (n + 3)) (a : Fin c → Fin (n + 2) → ℤ) (μ : Fin c → ℕ)
    (hlocal : ∀ i, (∃ j, label j = i) →
      map (Int.castRingHom (ZMod p)) (originShift (a i) (projectiveHypersurfaceChart (k i) f)) ∈
        idealOfVars (Fin (n + 2)) (ZMod p) ^ μ i ∧
      homogeneousComponent (μ i) (map (Int.castRingHom (ZMod p))
        (originShift (a i) (projectiveHypersurfaceChart (k i) f))) ≠ 0)
    (hunit : ∀ i, IsCoprime (p : ℤ) (z i (k (label i))))
    (hres : ∀ i j, (p : ℤ) ∣ z i (Equiv.swap 0 (k (label i)) j.succ) -
      a (label i) j * z i (k (label i)))
    (hz : ∀ i, eval (z i) f = 0) :
    (p : ℤ) ^ (∑ i : Fin c, hypersurfaceMultiplicityExponent (n + 1) (μ i)
      (Fintype.card {j : Fin s // label j = i})) ∣
      Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  apply residue_prime_powers_dvd_minorGcd _ label
  intro i cols
  by_cases hi : ∃ j, label j = i
  · obtain ⟨hf, hμ⟩ := hlocal i hi
    apply projective_hypersurface_local_det_divisibility f hfhom
      (fun j => F (cols j)) (fun j => hF (cols j))
      (fun j => z (residueRows label i j)) (k i) (a i) hf hμ
    · intro j
      simpa only [residueRows_label] using hunit (residueRows label i j)
    · intro j l
      simpa only [residueRows_label] using hres (residueRows label i j) l
    · intro j
      exact hz _
  · have he : Fintype.card {j : Fin s // label j = i} = 0 := by
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun j => hi ⟨j.val, j.property⟩⟩
    simp [he, hypersurfaceMultiplicityExponent]

/-- A reduced factor which never vanishes at the supplied points may be
removed from the residue-space count. The local equation is still the
original integer equation, so its exact integer zeros are retained. -/
theorem projective_hypersurface_reduced_factor_minorGcd
    {n s N p d e t M : ℕ} [Fact p.Prime] (hs : 0 < s)
    (f g h : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hh : h.IsHomogeneous t)
    (hg0 : map (Int.castRingHom (ZMod p)) g ≠ 0)
    (hfactor : map (Int.castRingHom (ZMod p)) f =
      map (Int.castRingHom (ZMod p)) g * map (Int.castRingHom (ZMod p)) h)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (havoid : ∀ i, eval (fun j => (z i j : ZMod p)) (map (Int.castRingHom (ZMod p)) h) ≠ 0) :
    0 < projectiveHypersurfaceTotalMultiplicity g hg hg0 ∧ ∃ a : ℕ,
      (∀ K : ℕ, s * K ≤ a + projectiveHypersurfaceTotalMultiplicity g hg hg0 *
        (n + 1 + K).choose (n + 2)) ∧
      (p : ℤ) ^ a ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  classical
  have hzmod (i : Fin s) :
      eval (fun j => (z i j : ZMod p)) (map (Int.castRingHom (ZMod p)) g) = 0 := by
    have he := congrArg (Int.castRingHom (ZMod p)) (hz i)
    rw [map_eval, map_zero, hfactor, map_mul] at he
    exact (mul_eq_zero.mp he).resolve_right (havoid i)
  let red : Fin s → ProjectiveHypersurfaceResidue g p := fun i =>
    ⟨primitiveProjectiveReduction (z i) (hprim i),
      primitiveProjectiveReduction_eval_zero_mod g hg (z i) (hprim i) (hzmod i)⟩
  let c := Fintype.card (ProjectiveHypersurfaceResidue g p)
  let E := Fintype.equivFin (ProjectiveHypersurfaceResidue g p)
  let label : Fin s → Fin c := fun i => E (red i)
  let k : Fin c → Fin (n + 3) := fun i => hypersurfaceResiduePivot (E.symm i).val
  let a : Fin c → Fin (n + 2) → ℤ := fun i => hypersurfaceResidueChartLift (E.symm i).val
  let μ : Fin c → ℕ := fun i => projectiveHypersurfaceResidueMultiplicity g hg hg0 (E.symm i)
  let sizes : Fin c → ℕ := fun i => Fintype.card {j : Fin s // label j = i}
  let exponent := ∑ i : Fin c, hypersurfaceMultiplicityExponent (n + 1) (μ i) (sizes i)
  have hμ (i : Fin c) := projectiveHypersurfaceResidueMultiplicity_spec g hg hg0 (E.symm i)
  have hsum : ∑ i : Fin c, μ i = projectiveHypersurfaceTotalMultiplicity g hg hg0 :=
    E.symm.sum_comp (projectiveHypersurfaceResidueMultiplicity g hg hg0)
  have hsize : ∑ i : Fin c, sizes i = s := sum_residue_class_sizes label
  have hc : 0 < c := Fintype.card_pos_iff.mpr ⟨red ⟨0, hs⟩⟩
  have hpos : 0 < projectiveHypersurfaceTotalMultiplicity g hg hg0 :=
    hc.trans_le (projectiveHypersurfaceTotalMultiplicity_bounds g hg hg0).1
  refine ⟨hpos, exponent, ?_, ?_⟩
  · intro K
    have hbound := aggregate_hypersurface_exponents_cutoff (n + 1) (by omega) sizes μ
      (fun i => (hμ i).1) K
    simpa only [hsum, hsize] using hbound
  · apply projective_hypersurface_residue_minorGcd_nonempty f hf F hF z label k a μ
    · intro i hi
      obtain ⟨j, hj⟩ := hi
      have he : E.symm i = red j := by rw [← hj]; exact E.symm_apply_apply _
      have hav : eval (E.symm i).val.rep (map (Int.castRingHom (ZMod p)) h) ≠ 0 := by
        rw [he]
        exact primitiveProjectiveReduction_eval_ne_zero_mod h hh (z j) (hprim j) (havoid j)
      have hconst : (map (Int.castRingHom (ZMod p))
          (originShift (a i) (projectiveHypersurfaceChart (k i) h))).constantCoeff ≠ 0 := by
        rw [originShift_map, ← eval_zero, eval_zero_originShift, eval_map]
        exact hypersurfaceResidueChartLift_nonzero h hh (E.symm i).val hav
      rw [originShift_projectiveChart_reduction_mul f g h hfactor]
      exact initial_form_mul_constant_nonzero (hμ i).2.2.1 (hμ i).2.2.2 hconst
    · intro i
      have hunit := (primitiveProjectiveReduction_hypersurface_chart
        (z i) (hprim i) (red i).val rfl).1
      simpa only [k, label, E.symm_apply_apply] using hunit
    · intro i j
      have hres := (primitiveProjectiveReduction_hypersurface_chart
        (z i) (hprim i) (red i).val rfl).2 j
      simpa only [k, a, label, E.symm_apply_apply] using hres
    · exact hz

/-- The sharp single-prime determinant bound remains valid if the reduction
has extra homogeneous factors which are nonzero at every supplied point.
The geometrically irreducible factor may have any positive degree at most d. -/
theorem projective_hypersurface_minorGcd_sharp_open
    {n s N p d e t M : ℕ} [Fact p.Prime]
    (f g h : MvPolynomial (Fin (n + 3)) ℤ)
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hh : h.IsHomogeneous t)
    (he : 0 < e) (hed : e ≤ d)
    (hg0 : map (Int.castRingHom (ZMod p)) g ≠ 0)
    (hir : Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
      (map (Int.castRingHom (ZMod p)) g)))
    (hfactor : map (Int.castRingHom (ZMod p)) f =
      map (Int.castRingHom (ZMod p)) g * map (Int.castRingHom (ZMod p)) h)
    (hsize : 27 * (d : ℝ) ^ 4 < p)
    (F : Fin N → MvPolynomial (Fin (n + 3)) ℤ) (hF : ∀ j, (F j).IsHomogeneous M)
    (z : Fin s → IntPoint (n + 3)) (hprim : ∀ i, Finset.univ.gcd (z i) = 1)
    (hz : ∀ i, eval (z i) f = 0)
    (havoid : ∀ i, eval (fun j => (z i j : ZMod p)) (map (Int.castRingHom (ZMod p)) h) ≠ 0) :
    ∃ a : ℕ,
      ((n + 1).factorial : ℝ) ^ (1 / (n + 1 : ℝ)) /
        (p + hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) *
        (n + 1 : ℝ) / (n + 2 : ℝ) * (s : ℝ) ^ (1 + 1 / (n + 1 : ℝ)) -
        (n + 2 : ℝ) * s ≤ a ∧
      (p : ℤ) ^ a ∣ Int.Matrix.minorGcd (Matrix.of fun i j => eval (z i) (F j)) := by
  by_cases hs : 0 < s
  · obtain ⟨hpos, a, hcut, hdiv⟩ := projective_hypersurface_reduced_factor_minorGcd hs
      f g h hf hg hh hg0 hfactor F hF z hprim hz havoid
    have hedR : (e : ℝ) ≤ d := by exact_mod_cast hed
    have hsize' : 27 * (e : ℝ) ^ 4 < p :=
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg e) hedR 4)
        (by norm_num)).trans_lt hsize
    have hcount := projective_hypersurface_totalMultiplicity_bound g hg he hg0 hir hsize'
    have hsq : (e : ℝ) ^ 2 ≤ (d : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg e) hedR 2
    have hmajor : (projectiveHypersurfaceTotalMultiplicity g hg hg0 : ℝ) ≤
        (p : ℝ) ^ (n + 1) +
          (hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p) * (p : ℝ) ^ n := by
      calc
        _ ≤ (p : ℝ) ^ (n + 1) +
            (330 + ((n + 3) * (n + 4) ^ n : ℕ)) * (d : ℝ) ^ 2 * (p : ℝ) ^ n * Real.sqrt p := by
          apply hcount.trans
          gcongr
        _ = _ := by unfold hypersurfaceCountConstant; ring
    have hroot := hypersurface_count_root_bound (n + 1) (by omega) (Nat.cast_nonneg p)
      (show 0 ≤ hypersurfaceCountConstant n * (d : ℝ) ^ 2 * Real.sqrt p from
        mul_nonneg (mul_nonneg (hypersurfaceCountConstant_nonneg n) (sq_nonneg _))
          (Real.sqrt_nonneg _))
      (Nat.cast_nonneg (projectiveHypersurfaceTotalMultiplicity g hg hg0))
      (by simpa only [Nat.add_sub_cancel] using hmajor)
    refine ⟨a, ?_, hdiv⟩
    simpa only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] using
      local_exponent_sharp_of_root_bound (n + 1) s a (by omega) hpos hroot hcut
  · have hs0 : s = 0 := by omega
    refine ⟨0, ?_, by simp⟩
    simp only [hs0, Nat.cast_zero,
      Real.zero_rpow (by positivity : (1 : ℝ) + 1 / (n + 1 : ℝ) ≠ 0), mul_zero, sub_zero, le_refl]

end
end AffineCurveCounting
