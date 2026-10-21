/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Auxiliary.AbsoluteAuxiliary
public import CCDN.Auxiliary.LiteralAffineBadPrimes
public import CCDN.Auxiliary.ScaledHomogenization
public import CCDN.Algebra.PolynomialPredicates
import CCDN.Algebra.ScaledHypersurfaceModel
import CCDN.Auxiliary.AffineChartAbsoluteAuxiliary
import CCDN.Auxiliary.LiteralAffineScaling
import CCDN.Auxiliary.ScaledAuxiliaryCount
import CCDN.Auxiliary.UnscaledHypersurfaceAuxiliary
import CCDN.Determinant.AffineCongruenceDeterminant
import CCDN.ForMathlib.MvPolynomial
/-! Auxiliary polynomials for prime-scaled and ordinary homogeneous
models with the literal affine bad-prime factor. The finite excluded-prime
set, geometric good reductions, primitive point family and affine pullback
are constructed from the original equation.
Here "literal" means the paper's Definition 3.2.1 applied verbatim to the affine
polynomial (`literalAffineBadPrimeFactor`, see `LiteralAffineBadPrimes`), as opposed to
`hypersurfaceBadPrimeFactor`, which also counts primes at which the degree drops. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def literalScalingPrimeCharge (h : ℕ) : ℝ :=
  primeSetFactor h.primeFactors

lemma literalScalingPrimeCharge_one : literalScalingPrimeCharge 1 = 1 := by
  simp [literalScalingPrimeCharge, primeSetFactor]

lemma literalScalingPrimeCharge_prime_le {p : ℕ} (hp : p.Prime) :
    literalScalingPrimeCharge p ≤ Real.exp 1 := by
  unfold literalScalingPrimeCharge primeSetFactor
  rw [hp.primeFactors, Finset.sum_singleton]
  apply Real.exp_le_exp.mpr
  apply (div_le_one (by exact_mod_cast hp.pos : (0 : ℝ) < p)).mpr
  exact (Real.log_le_sub_one_of_pos (by exact_mod_cast hp.pos)).trans (by linarith)

lemma hypersurfaceAuxiliaryDegreeBound_mono_b (n d : ℕ) {B b b' H : ℝ}
    (hb : b ≤ b') (hB : 0 ≤ B) (hH : 0 ≤ H) :
    hypersurfaceAuxiliaryDegreeBound n d B b H ≤ hypersurfaceAuxiliaryDegreeBound n d B b' H := by
  have hC := (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold hypersurfaceAuxiliaryDegreeBound auxDegreeBound auxMainTerm
  gcongr

/-- A homogeneous auxiliary for all original affine integer points, with a
finite prime charge coming only from the scale and literal bad reductions. -/
theorem literal_scaled_homogeneous_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) (h : ℕ) (hh : 0 < h)
    (hprimitive : ∀ x : IntPoint (n + 2), eval x f = 0 →
      Finset.univ.gcd (Fin.cons (h : ℤ) x) = 1)
    {B : ℝ} (hB : 1 ≤ B) (hhB : (h : ℝ) ≤ B) :
    ∃ M : ℕ, (M : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (literalScalingPrimeCharge h * literalAffineBadPrimeFactor f)
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (h : ℤ) f) : ℝ) ∧
      ∃ G : MvPolynomial (Fin (n + 3)) ℤ, G ≠ 0 ∧ G.IsHomogeneous M ∧
        (∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 →
          eval (Fin.cons (h : ℤ) x) G = 0) ∧
        ¬ scaledHomogenize f.totalDegree (h : ℤ) f ∣ G := by
  classical
  let F := scaledHomogenize f.totalDegree (h : ℤ) f
  let S := (integerBox (n + 2) B).filter (fun x => eval x f = 0)
  let E := (Fintype.equivFin S).symm
  let z : Fin (Fintype.card S) → IntPoint (n + 3) := fun i => Fin.cons (h : ℤ) (E i).val
  have hprim (i) : Finset.univ.gcd (z i) = 1 :=
    hprimitive _ (Finset.mem_filter.mp (E i).property).2
  have hz (i) : eval (z i) F = 0 := by
    rw [scaledHomogenize_eval _ _ le_rfl, (Finset.mem_filter.mp (E i).property).2, mul_zero]
  have hbox (i j) : |(z i j : ℝ)| ≤ B := by
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [z, Fin.cons_zero, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) h)] using hhB
    · exact mem_integerBox.mp (Finset.mem_filter.mp (E i).property).1 k
  have hFhom : F.IsHomogeneous f.totalDegree := scaledHomogenize_homogeneous _ _ le_rfl
  have hFabs : AbsolutelyIrreducible F := by
    rw [AbsolutelyIrreducible, show F = scaledHomogenize f.totalDegree (h : ℤ) f from rfl,
      scaledHomogenize_map]
    rw [← totalDegree_map_of_injective (Int.castRingHom (AlgebraicClosure ℚ)).injective_int f]
    exact scaledHomogenize_irreducible _ hir
      (by simpa using (show (h : AlgebraicClosure ℚ) ≠ 0 by exact_mod_cast hh.ne'))
  let bad := (finite_literal_affine_bad_primes f hir).toFinset
  have hbad (p) : p ∈ bad ↔ stepanovThreshold f.totalDegree < p ∧
      LiteralAffineBadReduction f p := by
    simp only [bad, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have hgood : ∀ (p : ℕ) [Fact p.Prime], p ∉ bad ∪ h.primeFactors →
      stepanovThreshold (f.totalDegree : ℝ) < p →
      Irreducible (map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))
        (map (Int.castRingHom (ZMod p)) (affineChart (n + 2) F))) ∧
      ∀ i, IsCoprime (p : ℤ) (z i 0) := by
    intro p hp hpnot hcut
    have hpnot' := Finset.notMem_union.mp hpnot
    have hph : ¬p ∣ h := fun hdiv => hpnot'.2 (Nat.mem_primeFactors.mpr ⟨hp.out, hdiv, hh.ne'⟩)
    have hphZ : ¬(p : ℤ) ∣ (h : ℤ) := by exact_mod_cast hph
    constructor
    · have hhK : (h : AlgebraicClosure (ZMod p)) ≠ 0 := by
        rw [Ne, CharP.cast_eq_zero_iff _ p]
        exact hph
      have he : (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).comp (Int.castRingHom (ZMod p)) =
          Int.castRingHom (AlgebraicClosure (ZMod p)) := by ext; simp
      rw [map_map, he]
      apply (affineChart_scaledHomogenize_map_irreducible _ (h : ℤ) (by simpa using hhK) f).mpr
      by_contra hbadp
      exact hpnot'.1 ((hbad p).mpr ⟨by exact_mod_cast hcut, hp.out, hbadp⟩)
    · intro i
      exact (Nat.prime_iff_prime_int.mp hp.out).irreducible.coprime_iff_not_dvd.mpr hphZ
  obtain ⟨M, hM, G, hG0, hGhom, hGzero, hGnd⟩ := affine_chart_absolute_auxiliary_degree
    F hFhom hd hFabs z hprim hz (bad ∪ h.primeFactors) hgood hB hbox
  have hcharge : primeSetFactor (bad ∪ h.primeFactors) ≤
      literalScalingPrimeCharge h * literalAffineBadPrimeFactor f := by
    rw [literalAffineBadPrimeFactor_eq_exp f hir rfl bad hbad, literalScalingPrimeCharge]
    unfold primeSetFactor
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [add_comm]
    have he := Finset.sum_union_inter (s₁ := bad) (s₂ := h.primeFactors)
      (f := fun p : ℕ => Real.log p / p)
    have hn : 0 ≤ ∑ p ∈ bad ∩ h.primeFactors, Real.log p / p :=
      Finset.sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    linarith
  refine ⟨M, hM.trans (hypersurfaceAuxiliaryDegreeBound_mono_b n f.totalDegree hcharge
    (by linarith) (by positivity)), G, hG0, hGhom, ?_, hGnd⟩
  intro x hx hxf
  let xS : S := ⟨x, Finset.mem_filter.mpr ⟨mem_integerBox.mpr hx, hxf⟩⟩
  obtain ⟨i, hi⟩ := E.surjective xS
  have hhzero := hGzero i
  simpa only [z, hi] using hhzero

/-- The literal-factor auxiliary for a prime-scaled model, with the single
scaling prime charged by at most exp(1). -/
theorem literal_prime_scaled_affine_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {p : ℕ} (hp : p.Prime) (hp0 : ¬(p : ℤ) ∣ f.coeff 0)
    {B : ℝ} (hB : 1 ≤ B) (hpB : (p : ℝ) ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬ f ∣ g ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (Real.exp 1 * literalAffineBadPrimeFactor f)
        (integerCoefficientHeight (scaledHomogenize f.totalDegree (p : ℤ) f) : ℝ) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ := literal_scaled_homogeneous_auxiliary
    f hir hd p hp.pos (prime_scaled_zero_primitive f hp hp0) hB hpB
  let g := homogeneousSlice (n + 2) (p : ℤ) G
  have hgndQ := scaled_auxiliary_rational_not_dvd f hf0 hprim hp hp0 G hGhom hGnd
  have hgnd : ¬f ∣ g := fun h => hgndQ (map_dvd (map (Int.castRingHom ℚ)) h)
  refine ⟨g, fun h => hgnd (by rw [h]; exact dvd_zero _), hgnd, ?_, ?_⟩
  · have hgM : (g.totalDegree : ℝ) ≤ M := by exact_mod_cast homogeneousSlice_degree_le (p : ℤ) hGhom
    exact hgM.trans (hM.trans (hypersurfaceAuxiliaryDegreeBound_mono_b n f.totalDegree
      (mul_le_mul_of_nonneg_right (literalScalingPrimeCharge_prime_le hp)
        (literalAffineBadPrimeFactor_nonneg f)) (by linarith) (by positivity)))
  · intro x hx hxf
    rw [homogeneousSlice_eval]
    exact hGzero x hx hxf

/-- The ordinary homogeneous model also admits the literal-factor auxiliary,
with no extra prime and no restriction on the constant coefficient. -/
theorem literal_unscaled_affine_auxiliary {n : ℕ}
    (f : MvPolynomial (Fin (n + 2)) ℤ) (hprim : PrimitiveIntegerPolynomial f)
    (hir : AbsolutelyIrreducible f)
    (hd : 0 < f.totalDegree) {B : ℝ} (hB : 1 ≤ B) :
    ∃ g : MvPolynomial (Fin (n + 2)) ℤ, g ≠ 0 ∧ ¬f ∣ g ∧
      (g.totalDegree : ℝ) ≤ hypersurfaceAuxiliaryDegreeBound n f.totalDegree B
        (literalAffineBadPrimeFactor f) (integerCoefficientHeight f : ℝ) ∧
      ∀ x : IntPoint (n + 2), (∀ j, |(x j : ℝ)| ≤ B) → eval x f = 0 → eval x g = 0 := by
  have hf0 : f ≠ 0 := ne_zero_of_irreducible_map hir
  obtain ⟨M, hM, G, _, hGhom, hGzero, hGnd⟩ := literal_scaled_homogeneous_auxiliary
    f hir hd 1 (by omega) (fun x _ => primitive_affine_integer_coordinates x) hB (by simpa using hB)
  let g := homogeneousSlice (n + 2) 1 G
  have hgnd : ¬f ∣ g := unscaled_auxiliary_not_dvd f hf0 hprim G hGhom hGnd
  refine ⟨g, fun h => hgnd (by rw [h]; exact dvd_zero _), hgnd, ?_, ?_⟩
  · have hgM : (g.totalDegree : ℝ) ≤ M := by exact_mod_cast homogeneousSlice_degree_le (1 : ℤ) hGhom
    simpa only [Nat.cast_one, literalScalingPrimeCharge_one, one_mul,
      integerCoefficientHeight_scaledHomogenize_one] using hgM.trans hM
  · intro x hx hxf
    rw [homogeneousSlice_eval]
    exact hGzero x hx hxf

end
end CCDN
