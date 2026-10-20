module

public import CCDN.CoprimeNewtonEdge
public import CCDN.PrimitiveNormalization
public import CCDN.HypersurfaceBadPrimeFactor

/-! Support and coefficient conditions for a coprime Newton edge.
They imply full degree and geometric irreducibility over every field in
which both endpoint coefficients remain nonzero. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial Finset Classical

structure HasCoprimeNewtonEdge {R : Type*} [CommSemiring R]
    (f : MvPolynomial (Fin 2) R) (d e : ℕ) : Prop where
  degree_gt : e < d
  lower_pos : 0 < e
  coprime : d.Coprime e
  x_coeff : f.coeff (Finsupp.single 0 d) ≠ 0
  y_coeff : f.coeff (Finsupp.single 1 e) ≠ 0
  weight_le : ∀ m ∈ f.support, e * m 0 + d * m 1 ≤ d * e

lemma HasCoprimeNewtonEdge.ne_zero {R : Type*} [CommSemiring R]
    {f : MvPolynomial (Fin 2) R} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) : f ≠ 0 := by
  intro hz
  simpa only [hz, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, ne_eq, not_true_eq_false] using h.x_coeff

lemma HasCoprimeNewtonEdge.weightedTotalDegree {R : Type*} [CommSemiring R]
    {f : MvPolynomial (Fin 2) R} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) :
    f.weightedTotalDegree (coprimeEdgeWeight d e) = d * e := by
  apply le_antisymm
  · apply Finset.sup_le
    intro m hm
    rw [coprimeEdgeWeight_apply]
    exact h.weight_le m hm
  · have hh := le_weightedTotalDegree (coprimeEdgeWeight d e) (mem_support_iff.mpr h.x_coeff)
    simpa [coprimeEdgeWeight_apply, mul_comm] using hh

lemma HasCoprimeNewtonEdge.totalDegree {R : Type*} [CommSemiring R]
    {f : MvPolynomial (Fin 2) R} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) :
    f.totalDegree = d := by
  apply le_antisymm
  · apply Finset.sup_le
    intro m hm
    have hh := h.weight_le m hm
    have he := h.lower_pos
    have hed := h.degree_gt
    have hsum : m 0 + m 1 ≤ d := by nlinarith
    simpa [Finsupp.degree, Finsupp.sum_fintype, Fin.sum_univ_two] using hsum
  · have hh := le_totalDegree (mem_support_iff.mpr h.x_coeff)
    simpa using hh

lemma HasCoprimeNewtonEdge.irreducible {K : Type*} [Field K]
    {f : MvPolynomial (Fin 2) K} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e) : Irreducible f :=
  coprime_newton_edge_irreducible f (by have := h.lower_pos; have := h.degree_gt; omega)
    h.lower_pos h.coprime h.weightedTotalDegree h.x_coeff h.y_coeff

lemma HasCoprimeNewtonEdge.map {R K : Type*} [CommSemiring R] [CommSemiring K]
    {f : MvPolynomial (Fin 2) R} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e)
    (φ : R →+* K)
    (hx : φ (f.coeff (Finsupp.single 0 d)) ≠ 0)
    (hy : φ (f.coeff (Finsupp.single 1 e)) ≠ 0) :
    HasCoprimeNewtonEdge (MvPolynomial.map φ f) d e where
  degree_gt := h.degree_gt
  lower_pos := h.lower_pos
  coprime := h.coprime
  x_coeff := by simpa only [coeff_map] using hx
  y_coeff := by simpa only [coeff_map] using hy
  weight_le m hm := h.weight_le m (support_map_subset φ f hm)

lemma HasCoprimeNewtonEdge.map_of_injective {R K : Type*} [CommSemiring R] [CommSemiring K]
    {f : MvPolynomial (Fin 2) R} {d e : ℕ} (h : HasCoprimeNewtonEdge f d e)
    (φ : R →+* K) (hφ : Function.Injective φ) :
    HasCoprimeNewtonEdge (MvPolynomial.map φ f) d e :=
  h.map φ (fun hz => h.x_coeff (hφ (hz.trans φ.map_zero.symm)))
    (fun hz => h.y_coeff (hφ (hz.trans φ.map_zero.symm)))

lemma HasCoprimeNewtonEdge.integer_scalar_factor
    {f g : MvPolynomial (Fin 2) ℤ} {d e : ℕ} {c : ℤ}
    (h : HasCoprimeNewtonEdge f d e) (hc : c ≠ 0) (heq : f = C c * g) :
    HasCoprimeNewtonEdge g d e where
  degree_gt := h.degree_gt
  lower_pos := h.lower_pos
  coprime := h.coprime
  x_coeff := by
    intro hz
    have hh := h.x_coeff
    rw [heq, coeff_C_mul, hz, mul_zero] at hh
    exact hh rfl
  y_coeff := by
    intro hz
    have hh := h.y_coeff
    rw [heq, coeff_C_mul, hz, mul_zero] at hh
    exact hh rfl
  weight_le m hm := by
    apply h.weight_le
    rw [mem_support_iff, heq, coeff_C_mul]
    exact mul_ne_zero hc (mem_support_iff.mp hm)

/-- All primes outside the endpoint coefficients preserve both the degree
and geometric irreducibility; this includes the degree-loss clause in the
repository's bad-reduction predicate. -/
theorem coprime_newton_edge_bad_reduction_dvd
    (f : MvPolynomial (Fin 2) ℤ) {d e : ℕ} (h : HasCoprimeNewtonEdge f d e)
    (p : ℕ) (hbad : HypersurfaceBadReduction f p) :
    (p : ℤ) ∣ f.coeff (Finsupp.single 0 d) * f.coeff (Finsupp.single 1 e) := by
  let : Fact p.Prime := ⟨hbad.1⟩
  by_contra hn
  have hx : ¬ (p : ℤ) ∣ f.coeff (Finsupp.single 0 d) := fun hh => hn (dvd_mul_of_dvd_left hh _)
  have hy : ¬ (p : ℤ) ∣ f.coeff (Finsupp.single 1 e) := fun hh => hn (dvd_mul_of_dvd_right hh _)
  have hxmod : (f.coeff (Finsupp.single 0 d) : ZMod p) ≠ 0 := by
    intro hz
    exact hx ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  have hymod : (f.coeff (Finsupp.single 1 e) : ZMod p) ≠ 0 := by
    intro hz
    exact hy ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  have hxK : (f.coeff (Finsupp.single 0 d) : AlgebraicClosure (ZMod p)) ≠ 0 := by
    simpa only [map_intCast] using (map_ne_zero (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).mpr hxmod
  have hyK : (f.coeff (Finsupp.single 1 e) : AlgebraicClosure (ZMod p)) ≠ 0 := by
    simpa only [map_intCast] using (map_ne_zero (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).mpr hymod
  have hmap := h.map (Int.castRingHom (AlgebraicClosure (ZMod p))) hxK hyK
  exact hbad.2.elim (fun hh => hh (hmap.totalDegree.trans h.totalDegree.symm))
    (fun hh => hh hmap.irreducible)

end
end CCDN
