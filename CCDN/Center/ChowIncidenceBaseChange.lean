module

public import CCDN.Center.ChowIncidenceIdeal
public import CCDN.Center.PolynomialCoefficientDescent
/-! Exact field base change for the Chow incidence ideal. Lift the
incidence substitution before taking the coordinate quotient, then test
membership coefficientwise and descend by linear coefficient functionals. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- The incidence substitution before quotienting by the source ideal. -/
def chowIncidencePolynomialMap {K : Type*} [Field K] {n : ℕ} (r : ℕ) :
    MvPolynomial (Fin r × Fin (n + 1)) K →ₐ[K]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin n) K) :=
  aeval (fun q => Fin.cases
    (-(∑ j, X (q.1,j) * C (X j))) (fun j => X (q.1,j)) q.2)

lemma chowIncidencePolynomialMap_quotient {K : Type*} [Field K] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) :
    map (Ideal.Quotient.mk I) (chowIncidencePolynomialMap r f) = chowIncidenceMap r I f := by
  have he : (map (Ideal.Quotient.mk I)).comp (chowIncidencePolynomialMap r).toRingHom =
      (chowIncidenceMap r I).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chowIncidencePolynomialMap, chowIncidenceMap]
      rfl
    · rintro ⟨i,j⟩
      refine Fin.cases ?_ (fun k => ?_) j <;>
        simp [chowIncidencePolynomialMap, chowIncidenceMap]
  exact RingHom.congr_fun he f

lemma mem_chowIncidenceIdeal_iff_coeff {K : Type*} [Field K] {n r : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) :
    f ∈ chowIncidenceIdeal r I ↔
      ∀ e, (chowIncidencePolynomialMap r f).coeff e ∈ I := by
  change chowIncidenceMap r I f = 0 ↔ _
  rw [← chowIncidencePolynomialMap_quotient, MvPolynomial.ext_iff]
  simp only [coeff_map, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply,
    Ideal.Quotient.eq_zero_iff_mem]

lemma chowIncidencePolynomialMap_map {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ} (r : ℕ)
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) :
    map (map (algebraMap K L)) (chowIncidencePolynomialMap r f) =
      chowIncidencePolynomialMap r (map (algebraMap K L) f) := by
  have he : (map (map (algebraMap K L))).comp
      (chowIncidencePolynomialMap (K := K) (n := n) r).toRingHom =
      (chowIncidencePolynomialMap (K := L) (n := n) r).toRingHom.comp
        (map (algebraMap K L)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chowIncidencePolynomialMap]
    · rintro ⟨i,j⟩
      refine Fin.cases ?_ (fun k => ?_) j <;> simp [chowIncidencePolynomialMap]
  exact RingHom.congr_fun he f

/-- Linear descent commutes with the nested incidence substitution. -/
lemma chowIncidencePolynomialMap_coefficientLinear {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (r : ℕ) (φ : L →ₗ[K] K)
    (f : MvPolynomial (Fin r × Fin (n + 1)) L) :
    polynomialCoefficientLinear (polynomialCoefficientLinear φ)
        (chowIncidencePolynomialMap r f) =
      chowIncidencePolynomialMap r (polynomialCoefficientLinear φ f) := by
  have hmul (g : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin n) L))
      (h : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin n) K)) :
      polynomialCoefficientLinear (polynomialCoefficientLinear φ)
          (g * map (map (algebraMap K L)) h) =
        polynomialCoefficientLinear (polynomialCoefficientLinear φ) g * h :=
    polynomialCoefficientLinear_mul_compatible _ _
      (fun a b => polynomialCoefficientLinear_mul_map φ a b) g h
  induction f using MvPolynomial.induction_on with
  | C c => simp [chowIncidencePolynomialMap, polynomialCoefficientLinear_C]
  | add f g hf hg => simp only [map_add, hf, hg]
  | mul_X f q hf =>
      have hX : (X q : MvPolynomial (Fin r × Fin (n + 1)) L) =
          map (algebraMap K L) (X q) := by simp
      rw [map_mul, hX, ← chowIncidencePolynomialMap_map, hmul, hf,
        polynomialCoefficientLinear_mul_map, map_mul]

/-- Field extension commutes with the constructed incidence ideal, for
arbitrary source ideals. -/
theorem chowIncidenceIdeal_scalar_extension {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) :
    (chowIncidenceIdeal r I).map (map (algebraMap K L)) =
      chowIncidenceIdeal r (I.map (map (algebraMap K L))) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, mem_chowIncidenceIdeal_iff_coeff]
    intro e
    rw [← chowIncidencePolynomialMap_map, coeff_map]
    exact Ideal.mem_map_of_mem _ ((mem_chowIncidenceIdeal_iff_coeff I f).mp hf e)
  · intro f hf
    apply (mem_scalar_extension_iff_polynomialCoefficientLinear _ f).mpr
    intro φ
    rw [mem_chowIncidenceIdeal_iff_coeff]
    intro e
    rw [← chowIncidencePolynomialMap_coefficientLinear, polynomialCoefficientLinear_coeff]
    exact polynomialCoefficientLinear_mem_scalar_extension I _
      ((mem_chowIncidenceIdeal_iff_coeff _ f).mp hf e) φ

/-- Geometric primeness of the source implies geometric primeness of its
incidence ideal. The scalar extension is identified before using
primality of the target polynomial ring. -/
theorem chowIncidenceIdeal_geometrically_prime {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime] :
    ((chowIncidenceIdeal r I).map (map (algebraMap K L))).IsPrime := by
  rw [chowIncidenceIdeal_scalar_extension]
  infer_instance

/-- Consequently a nonzero principal incidence equation stays
irreducible after every field extension over which the source remains prime. -/
theorem chow_incidence_equation_irreducible_map {K L : Type*}
    [Field K] [Field L] [Algebra K L] {n : ℕ}
    (r : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    [(I.map (map (algebraMap K L))).IsPrime]
    (f : MvPolynomial (Fin r × Fin (n + 1)) K) (hf : f ≠ 0)
    (hprincipal : chowIncidenceIdeal r I = Ideal.span {f}) :
    Irreducible (map (algebraMap K L) f) := by
  have hp := chowIncidenceIdeal_geometrically_prime (L := L) r I
  rw [hprincipal, Ideal.map_span, Set.image_singleton] at hp
  have hne : map (algebraMap K L) f ≠ 0 :=
    (map_ne_zero_iff _ (map_injective _ (algebraMap K L).injective)).mpr hf
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

end
end CCDN
