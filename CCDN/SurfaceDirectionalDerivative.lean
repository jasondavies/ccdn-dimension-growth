module

public import CCDN.BinaryHomogeneousIrreducibility
public import CCDN.AffinePlaneRestriction
public import CCDN.HomogeneousTranslation
public import CCDN.PlaneSingularities
public import CCDN.AffineLineLeading
public import CCDN.TopFormIrreducibility
public import CCDN.SurfaceLineDirections
public import CCDN.PolynomialPredicates

/-! Directional derivatives of surfaces with absolutely irreducible top form. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

def directionalDerivative {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (f : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ i, C (v i) * pderiv i f

lemma directionalDerivative_totalDegree_le {K σ : Type*} [Field K] [Fintype σ]
    (v : σ → K) (f : MvPolynomial σ K) :
    (directionalDerivative v f).totalDegree ≤ f.totalDegree - 1 := by
  classical
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simpa using pderiv_totalDegree_le f i)

lemma directionalDerivative_map {R S σ : Type*} [CommRing R] [CommRing S] [Fintype σ]
    (φ : R →+* S) (v : σ → R) (f : MvPolynomial σ R) :
    directionalDerivative (fun i => φ (v i)) (map φ f) = map φ (directionalDerivative v f) := by
  classical
  simp [directionalDerivative, pderiv_map]

lemma pderiv_homogeneousComponent {R σ : Type*} [CommRing R]
    (i : σ) (f : MvPolynomial σ R) {d : ℕ} (hd : 0 < d) :
    pderiv i (homogeneousComponent d f) = homogeneousComponent (d - 1) (pderiv i f) := by
  classical
  ext m
  rw [coeff_pderiv, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_pderiv]
  have he : (m + Finsupp.single i 1).degree = m.degree + 1 := by
    change (m + Finsupp.single i 1).sum (fun _ e => e) = m.sum (fun _ e => e) + 1
    rw [Finsupp.sum_add_index (by simp) (by intros; rfl)]
    simp
  rw [he]
  by_cases hm : m.degree = d - 1
  · simp [hm, Nat.sub_add_cancel hd]
  · have hn : m.degree + 1 ≠ d := by omega
    simp [hm, hn]

lemma directionalDerivative_homogeneousComponent {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (f : MvPolynomial σ R) {d : ℕ} (hd : 0 < d) :
    directionalDerivative v (homogeneousComponent d f) =
      homogeneousComponent (d - 1) (directionalDerivative v f) := by
  classical
  simp only [directionalDerivative, map_sum, homogeneousComponent_C_mul,
    pderiv_homogeneousComponent _ _ hd]

lemma notMem_vars_of_pderiv_eq_zero {K σ : Type*} [Field K] [CharZero K]
    (f : MvPolynomial σ K) (i : σ) (hz : pderiv i f = 0) : i ∉ f.vars := by
  classical
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hpos : 0 < m i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmi)
  let u := m - Finsupp.single i 1
  have hui : u i + 1 = m i := by
    simp only [u, Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hu : u + Finsupp.single i 1 = m := by
    apply tsub_add_cancel_of_le
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Finsupp.single_eq_same]
      omega
    · simp [Finsupp.single_eq_of_ne hji]
  have hc := congrArg (fun g : MvPolynomial σ K => g.coeff u) hz
  rw [coeff_pderiv, hu] at hc
  have he : (u i : K) + 1 = (m i : K) := by
    exact_mod_cast hui
  change f.coeff m * ((u i : K) + 1) = 0 at hc
  rw [he] at hc
  exact (mul_ne_zero (mem_support_iff.mp hm) (Nat.cast_ne_zero.mpr (by omega))) hc

lemma irreducible_of_rename_succ {K : Type*} [Field K] {n : ℕ}
    (f : MvPolynomial (Fin n) K) (hf : Irreducible (rename Fin.succ f)) :
    Irreducible f := by
  have he (g : MvPolynomial (Fin n) K) :
      eval₂Hom C (Fin.cons 0 X) (rename Fin.succ g) = g := by
    rw [eval₂Hom_rename]
    have hh : Fin.cons (0 : MvPolynomial (Fin n) K) X ∘ Fin.succ = X := by
      funext i
      simp
    rw [hh]
    simp
  refine ⟨fun h => hf.not_isUnit (h.map (rename Fin.succ)), ?_⟩
  intro a b hab
  have h := hf.isUnit_or_isUnit (by rw [hab, map_mul])
  rcases h with ha | hb
  · exact Or.inl (by simpa only [he] using ha.map (eval₂Hom C (Fin.cons 0 X)))
  · exact Or.inr (by simpa only [he] using hb.map (eval₂Hom C (Fin.cons 0 X)))

lemma ternary_homogeneous_irreducible_pderiv_zero_ne_zero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous d) (hir : Irreducible f)
    (hd : 2 ≤ d) : pderiv 0 f ≠ 0 := by
  intro hz
  have hv := notMem_vars_of_pderiv_eq_zero f 0 hz
  have hs : ↑f.vars ⊆ Set.range (Fin.succ : Fin 2 → Fin 3) := by
    intro i hi
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fun hi => False.elim (hv hi)
    · exact fun _ => ⟨j, rfl⟩
  obtain ⟨g, hg⟩ := exists_rename_eq_of_vars_subset_range f Fin.succ (Fin.succ_injective 2) hs
  have hgh : g.IsHomogeneous d :=
    (IsHomogeneous.rename_isHomogeneous_iff (Fin.succ_injective 2)).mp (hg ▸ hf)
  have hgi : Irreducible g := irreducible_of_rename_succ g (hg ▸ hir)
  have := binary_homogeneous_irreducible_degree_le_one g hgh hgi
  omega

lemma homogeneousTranslation_directionalDerivative {K : Type*} [Field K] {n : ℕ}
    (v : Fin (n + 1) → K) (hv : v 0 ≠ 0) (f : MvPolynomial (Fin (n + 1)) K) :
    C (v 0) * pderiv 0 (homogeneousTranslation K (fun j => v j.succ / v 0) f) =
      homogeneousTranslation K (fun j => v j.succ / v 0) (directionalDerivative v f) := by
  classical
  let e := homogeneousTranslation K (fun j => v j.succ / v 0)
  have hX (i : Fin (n + 1)) : C (v 0) * pderiv 0 (e (X i)) = C (v i) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [e, homogeneousTranslation, homogeneousTranslationHom]
    · simp only [e, homogeneousTranslation, homogeneousTranslationHom, AlgEquiv.ofAlgHom_apply,
        aeval_X, Fin.cons_succ, map_add, pderiv_mul, pderiv_X_of_ne (Fin.succ_ne_zero j), pderiv_C, zero_mul,
        pderiv_X_self, mul_one, zero_add]
      rw [← C_mul]
      congr 1
      field_simp
  change C (v 0) * pderiv 0 (e f) = e (directionalDerivative v f)
  have hchain := pderiv_algHom_chain e.toAlgHom f 0
  change pderiv 0 (e f) = ∑ i, e (pderiv i f) * pderiv 0 (e (X i)) at hchain
  rw [hchain, Finset.mul_sum]
  simp only [directionalDerivative, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hC : e (C (v i)) = C (v i) := e.commutes _
  rw [hC]
  calc
    C (v 0) * (e (pderiv i f) * pderiv 0 (e (X i))) =
        (C (v 0) * pderiv 0 (e (X i))) * e (pderiv i f) := by ring
    _ = _ := by rw [hX]

lemma directionalDerivative_renameEquiv {K σ : Type*} [CommRing K] [Fintype σ]
    (e : σ ≃ σ) (v : σ → K) (f : MvPolynomial σ K) :
    directionalDerivative (fun i => v (e.symm i)) (rename e f) =
      rename e (directionalDerivative v f) := by
  classical
  unfold directionalDerivative
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply, pderiv_rename e.injective, map_sum, map_mul, rename_C]

lemma homogeneous_surface_directionalDerivative_ne_zero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {d : ℕ}
    (f : MvPolynomial (Fin 3) K) (hf : f.IsHomogeneous d) (hir : Irreducible f)
    (hd : 2 ≤ d) (v : Fin 3 → K) (hv : v ≠ 0) : directionalDerivative v f ≠ 0 := by
  classical
  have hex : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨j, hj⟩ := hex
  let e : Fin 3 ≃ Fin 3 := Equiv.swap j 0
  let w : Fin 3 → K := fun i => v (e.symm i)
  have hw : w 0 ≠ 0 := by simpa [w, e] using hj
  let F := rename e f
  have hF : F.IsHomogeneous d := hf.rename_isHomogeneous
  have hiF : Irreducible F :=
    (MulEquiv.irreducible_iff (f := (renameEquiv K e).toMulEquiv)).mpr hir
  let a : Fin 2 → K := fun i => w i.succ / w 0
  have hG : (homogeneousTranslation K a F).IsHomogeneous d :=
    homogeneousTranslation_homogeneous a hF
  have hiG : Irreducible (homogeneousTranslation K a F) :=
    (MulEquiv.irreducible_iff (f := (homogeneousTranslation K a).toMulEquiv)).mpr hiF
  intro hz
  have hzw : directionalDerivative w F = 0 := by
    change directionalDerivative (fun i => v (e.symm i)) (rename e f) = 0
    rw [directionalDerivative_renameEquiv, hz, map_zero]
  have h := homogeneousTranslation_directionalDerivative w hw F
  rw [hzw, map_zero] at h
  exact (ternary_homogeneous_irreducible_pderiv_zero_ne_zero _ hG hiG hd)
    ((mul_eq_zero.mp h).resolve_left (by simpa using hw))

theorem top_irreducible_directionalDerivative_ne_zero
    {K L : Type*} [Field K] [Field L] [CharZero L] [IsAlgClosed L]
    (φ : K →+* L) (f : MvPolynomial (Fin 3) K) {d : ℕ}
    (hir : Irreducible (map φ (homogeneousComponent d f))) (hd : 2 ≤ d)
    (v : Fin 3 → K) (hv : v ≠ 0) : directionalDerivative v f ≠ 0 := by
  have hhom : (map φ (homogeneousComponent d f)).IsHomogeneous d := by
    rw [map_homogeneousComponent]
    exact homogeneousComponent_isHomogeneous _ _
  have hvm : (fun i => φ (v i)) ≠ 0 := by
    intro hh
    apply hv
    funext i
    apply φ.injective
    simpa using congrFun hh i
  intro hz
  have hh := homogeneous_surface_directionalDerivative_ne_zero _ hhom hir hd
    (fun i => φ (v i)) hvm
  apply hh
  rw [directionalDerivative_map, directionalDerivative_homogeneousComponent v f (by omega),
    hz, map_zero, map_zero]

theorem surface_directionalDerivative_ne_zero
    (f : MvPolynomial (Fin 3) ℤ)
    (hir : HasAbsIrreducibleTopForm f) (hd : 2 ≤ f.totalDegree)
    (v : Fin 3 → ℚ) (hv : v ≠ 0) :
    directionalDerivative v (map (Int.castRingHom ℚ) f) ≠ 0 := by
  apply top_irreducible_directionalDerivative_ne_zero (algebraMap ℚ (AlgebraicClosure ℚ))
    (map (Int.castRingHom ℚ) f) (d := f.totalDegree) _ hd v hv
  rw [← map_homogeneousComponent, map_map]
  convert hir using 1
  congr 1

@[simp] lemma directionalDerivative_C {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (a : R) : directionalDerivative v (C a) = 0 := by
  simp [directionalDerivative]

@[simp] lemma directionalDerivative_X {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (j : σ) : directionalDerivative v (X j) = C (v j) := by
  classical
  simp [directionalDerivative, pderiv_X, Pi.single_apply]

lemma directionalDerivative_add {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (f g : MvPolynomial σ R) :
    directionalDerivative v (f + g) = directionalDerivative v f + directionalDerivative v g := by
  simp [directionalDerivative, mul_add, Finset.sum_add_distrib]

lemma directionalDerivative_mul {R σ : Type*} [CommRing R] [Fintype σ]
    (v : σ → R) (f g : MvPolynomial σ R) :
    directionalDerivative v (f * g) = directionalDerivative v f * g + f * directionalDerivative v g := by
  classical
  simp only [directionalDerivative, pderiv_mul, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

lemma derivative_affineLinePolynomial {R σ : Type*} [CommRing R] [Fintype σ]
    (a v : σ → R) (f : MvPolynomial σ R) :
    Polynomial.derivative (affineLinePolynomial a v f) =
      affineLinePolynomial a v (directionalDerivative v f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C r => simp [affineLinePolynomial]
  | add f g hf hg => simp only [map_add, directionalDerivative_add, hf, hg]
  | mul_X f j hf =>
    rw [map_mul, Polynomial.derivative_mul, hf, directionalDerivative_mul,
      map_add, map_mul, map_mul, directionalDerivative_X]
    simp [affineLinePolynomial, Polynomial.derivative_add, Polynomial.derivative_mul]

theorem directionalDerivative_zero_on_line {K σ : Type*} [Field K] [Infinite K] [Fintype σ]
    (a v : σ → K) (f : MvPolynomial σ K)
    (hline : ∀ t : K, eval (a + t • v) f = 0) :
    ∀ t : K, eval (a + t • v) (directionalDerivative v f) = 0 := by
  have hpoly : affineLinePolynomial a v f = 0 := by
    apply Polynomial.zero_of_eval_zero
    intro t
    rw [eval_affineLinePolynomial]
    exact hline t
  have hder := derivative_affineLinePolynomial a v f
  rw [hpoly, Polynomial.derivative_zero] at hder
  intro t
  rw [← eval_affineLinePolynomial, ← hder]
  simp

theorem rationalAffineLine_contained_directionalDerivative {n : ℕ}
    (a v : RatPoint n) (f : CoordinatePolynomial n)
    (hline : rationalAffineLine a v ⊆ zeroLocus f) :
    rationalAffineLine a v ⊆ zeroLocus (directionalDerivative v f) := by
  rintro z ⟨t, rfl⟩
  exact directionalDerivative_zero_on_line a v f (fun t => hline ⟨t, rfl⟩) t

end
end CCDN
