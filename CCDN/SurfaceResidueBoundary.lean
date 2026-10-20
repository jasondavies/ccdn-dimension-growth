module

public import CCDN.SurfaceCongruenceFamily
public import CCDN.SmoothPrimeWindow
public import CCDN.ResidueSubsetBoundary
public import CCDN.SurfaceCurveCrossing

/-! A nonsingular point on a large-degree initial curve must cross a
proper auxiliary section along a one-prime deletion edge. This constructs
the residual cover from smooth reductions and auxiliaries. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset

def surfaceResidueLogBudget (B L : ℝ) : ℝ :=
  1 + Real.log B + (Real.log 4 + 4) * scalingPrimeRatio * L

lemma exp_sum_log_primes (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Real.exp (∑ p ∈ P, Real.log p) = ∏ p ∈ P, (p : ℝ) := by
  rw [Real.exp_sum]
  apply prod_congr rfl
  intro p hp
  exact Real.exp_log (by exact_mod_cast (hP p hp).pos)

lemma SurfaceCongruenceFamily.terminal_degree_le
    {f : MvPolynomial (Fin 3) ℤ} {B A L X : ℝ}
    (F : SurfaceCongruenceFamily f B A) (hB : 1 ≤ B) (hA : 0 ≤ A) (hL : 1 ≤ L)
    (P : Finset ℕ) (hPW : P ⊆ congruencePrimeWindow L)
    (hP : ∀ p ∈ P, p.Prime) (r : SmoothAffineResidueFamily f P)
    (hX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hprod : X ≤ ∏ p ∈ P, (p : ℝ)) :
    ((F.auxiliary P hP r).totalDegree : ℝ) ≤ 2 * A * surfaceResidueLogBudget B L := by
  have hQ : 0 ≤ ∑ p ∈ P, Real.log p := sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have hlogB := Real.log_nonneg hB
  have hlog : (∑ p ∈ P, Real.log p) ≤
      (Real.log 4 + 4) * scalingPrimeRatio * L :=
    (sum_le_sum_of_subset_of_nonneg hPW (fun p _ _ => Real.log_natCast_nonneg p)).trans
      (congruencePrimeWindow_log_upper hL)
  have hden : 0 < ∏ p ∈ P, (p : ℝ) := prod_pos (fun p hp => by exact_mod_cast (hP p hp).pos)
  have hratio : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
      Real.exp (∑ p ∈ P, Real.log p) ≤ 1 := by
    rw [exp_sum_log_primes P hP]
    exact (div_le_one hden).mpr (hX.trans hprod)
  have hT : 0 ≤ surfaceResidueLogBudget B L := by
    unfold surfaceResidueLogBudget
    have hlogB := Real.log_nonneg hB
    linarith
  have hd := F.degree_le P hP r
  calc
    _ ≤ A * (B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) /
        Real.exp (∑ p ∈ P, Real.log p) + 1) *
        (1 + Real.log B + ∑ p ∈ P, Real.log p) := hd
    _ ≤ A * 2 * surfaceResidueLogBudget B L := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (by linarith) hA
      · dsimp only [surfaceResidueLogBudget]
        linarith
      · positivity
      · positivity
    _ = _ := by ring

lemma surface_prime_curve_degree_le
    (f g : CoordinatePolynomial 3) (hf : Irreducible f) (hfg : ¬ f ∣ g)
    (I : Ideal (CoordinatePolynomial 3)) (hI : I.IsPrime) (hheight : I.height = 2)
    (hfI : f ∈ I) (hgI : g ∈ I) {d : ℕ} (hdegree : HasAffineCurveDegree I d) :
    d ≤ f.totalDegree * g.totalDegree := by
  have hh := surface_prime_curve_degree_sum_le f g hf hfg {I} (fun _ => d)
    (fun P hP => by
      have he : P = I := mem_singleton.mp hP
      subst P
      exact ⟨hI, hheight, hfI, hgI, hdegree⟩)
  simpa only [sum_singleton] using hh

/-- A point on an initial prime curve above the terminal degree cutoff
lies in a proper section across a bounded-modulus residue edge. -/
theorem surface_residue_boundary_of_large_curve
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : Irreducible (map (Int.castRingHom ℚ) f))
    {A B H L X : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hH : 1 ≤ H) (hL : 1 ≤ L)
    (hcoeff : ∀ e, |(f.coeff e : ℝ)| ≤ H)
    (hheight : 4 * Real.log ((f.totalDegree : ℝ) + 1) +
      Real.log H + f.totalDegree * Real.log B ≤ L)
    (hX : 1 < X) (hBX : B ^ (1 / Real.sqrt (f.totalDegree : ℝ)) ≤ X)
    (hXL : X ≤ Real.exp L) (F : SurfaceCongruenceFamily f B A)
    (I : Ideal (CoordinatePolynomial 3)) (hI : I.IsPrime) (hIheight : I.height = 2)
    (hfI : map (Int.castRingHom ℚ) f ∈ I)
    (hinitI : map (Int.castRingHom ℚ) F.initial ∈ I)
    {d : ℕ} (hdegree : HasAffineCurveDegree I d)
    (hlarge : 2 * f.totalDegree * A * surfaceResidueLogBudget B L < d)
    (x : IntPoint 3) (hx : ∀ j, |(x j : ℝ)| ≤ B) (hxf : eval x f = 0)
    (hsmooth : ∃ j, eval x (pderiv j f) ≠ 0) :
    ∃ R : Finset ℕ, ∃ hR : ∀ p ∈ R, p.Prime,
      ∃ p ∈ R, ∃ r : SmoothAffineResidueFamily f R,
        R ⊆ congruencePrimeWindow L ∧
        (∏ q ∈ R, (q : ℝ)) < scalingPrimeRatio * L * X ∧
        (∏ q ∈ R.erase p, (q : ℝ)) < X ∧
        map (Int.castRingHom ℚ)
          (F.auxiliary (R.erase p) (fun q hq => hR q (mem_of_mem_erase hq))
            (r.restrict (erase_subset p R))) ∈ I ∧
        map (Int.castRingHom ℚ) (F.auxiliary R hR r) ∉ I ∧
        eval x (F.auxiliary R hR r) = 0 := by
  classical
  obtain ⟨P, hPW, hPprod, hPsmooth⟩ := exists_smooth_prime_window_subset f hH hB hL
    hcoeff (by norm_num; exact hheight) x hx hsmooth
  have hPprime (p : ℕ) (hp : p ∈ P) : p.Prime :=
    ((mem_congruencePrimeWindow hL).mp (hPW hp)).1
  obtain ⟨R₀, hR₀P, _, hR₀prod, hR₀proper, hR₀upper⟩ :=
    exists_minimal_product_subset P hX
      (fun p hp => by exact_mod_cast (hPprime p hp).pos)
      (fun p hp => ((mem_congruencePrimeWindow hL).mp (hPW hp)).2.2)
      (hXL.trans hPprod)
  have hR₀W : R₀ ⊆ congruencePrimeWindow L := hR₀P.trans hPW
  have hR₀prime (q : ℕ) (hq : q ∈ R₀) : q.Prime := hPprime q (hR₀P hq)
  have hR₀smooth (q : ℕ) (hq : q ∈ R₀) := hPsmooth q (hR₀P hq)
  let aux (T : Finset ℕ) : MvPolynomial (Fin 3) ℤ :=
    if hT : T ⊆ R₀ then F.auxiliary T (fun q hq => hR₀prime q (hT hq))
      (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) else 1
  have haux (T : Finset ℕ) (hT : T ⊆ R₀) :
      aux T = F.auxiliary T (fun q hq => hR₀prime q (hT hq))
        (smoothResidueFamilyOfPoint x hxf T (fun q hq => hR₀smooth q (hT hq))) := by
    simp only [aux, dite_eq_left hT]
  have hterminal : map (Int.castRingHom ℚ) (aux R₀) ∉ I := by
    intro hmem
    rw [haux R₀ (Subset.refl _)] at hmem
    have hdeg := F.terminal_degree_le hB hA hL R₀ hR₀W hR₀prime
      (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth) hBX hR₀prod
    have hcurve := surface_prime_curve_degree_le (map (Int.castRingHom ℚ) f)
      (map (Int.castRingHom ℚ) (F.auxiliary R₀ hR₀prime
        (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth))) hir (F.proper _ _ _)
      I hI hIheight hfI hmem hdegree
    rw [rational_map_totalDegree, rational_map_totalDegree] at hcurve
    have hcurveR : (d : ℝ) ≤ (f.totalDegree : ℝ) *
        (F.auxiliary R₀ hR₀prime
          (smoothResidueFamilyOfPoint x hxf R₀ hR₀smooth)).totalDegree := by exact_mod_cast hcurve
    have hh := mul_le_mul_of_nonneg_left hdeg (Nat.cast_nonneg (α := ℝ) f.totalDegree)
    nlinarith
  have hempty : ¬ (map (Int.castRingHom ℚ) (aux ∅) ∉ I) := by
    rw [haux ∅ (empty_subset _), F.initial_eq]
    exact not_not.mpr hinitI
  obtain ⟨R, hRR₀, p, hp, hchild, hparent⟩ := exists_subset_erase_boundary R₀
    (fun T => map (Int.castRingHom ℚ) (aux T) ∉ I) hempty hterminal
  have hRprime (q : ℕ) (hq : q ∈ R) : q.Prime := hR₀prime q (hRR₀ hq)
  have hRsmooth (q : ℕ) (hq : q ∈ R) := hR₀smooth q (hRR₀ hq)
  let r := smoothResidueFamilyOfPoint x hxf R hRsmooth
  have hparentSub : R.erase p ⊆ R₀ := (erase_subset p R).trans hRR₀
  have hparentEq : aux (R.erase p) =
      F.auxiliary (R.erase p) (fun q hq => hRprime q (mem_of_mem_erase hq))
        (r.restrict (erase_subset p R)) := by
    rw [haux (R.erase p) hparentSub]
    rfl
  have hchildEq : aux R = F.auxiliary R hRprime r := haux R hRR₀
  refine ⟨R, hRprime, p, hp, r, hRR₀.trans hR₀W, ?_, ?_, ?_, ?_, ?_⟩
  · have hm : (∏ q ∈ R, (q : ℝ)) ≤ ∏ q ∈ R₀, (q : ℝ) :=
      prod_le_prod_of_subset_of_one_le₀ hRR₀ (fun _ _ => Nat.cast_nonneg _)
        (fun q hq _ => by exact_mod_cast (hR₀prime q hq).one_le)
    exact hm.trans_lt hR₀upper
  · exact hR₀proper _ ((erase_ssubset hp).trans_le hRR₀)
  · rw [← hparentEq]
    exact not_not.mp hparent
  · rwa [← hchildEq]
  · exact F.point_vanishes x hx hxf R hRprime hRsmooth

end
end CCDN
