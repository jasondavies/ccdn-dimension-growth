module

public import CCDN.FormalBranchBaseChange
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! A smooth rational point on an irreducible plane curve implies geometric
irreducibility. The proof uses the faithful formal branch, extends its
coordinate algebra to every field, and identifies the resulting prime ideal
in the polynomial ring over that field. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped TensorProduct

/-- An irreducible plane equation with a smooth rational point remains
irreducible over every extension field. No perfectness assumption is needed. -/
theorem irreducible_map_of_smooth_plane_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    Irreducible (MvPolynomial.map (algebraMap K L) f) := by
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  let J : Ideal (L ⊗[K] MvPolynomial (Fin 2) K) :=
    I.map Algebra.TensorProduct.includeRight
  let e := Algebra.TensorProduct.tensorQuotientEquiv (R := K) L
    (MvPolynomial (Fin 2) K) L I
  have : IsDomain (L ⊗[K] (MvPolynomial (Fin 2) K ⧸ I)) :=
    isDomain_tensor_plane_quotient_of_smooth_point f hf z j hz hj
  have : IsDomain ((L ⊗[K] MvPolynomial (Fin 2) K) ⧸ J) :=
    Function.Injective.isDomain e.symm e.symm.injective
  have : J.IsPrime := (Ideal.Quotient.isDomain_iff_prime J).mp inferInstance
  let E := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) K L
  have hmap : J.map E = Ideal.span {MvPolynomial.map (algebraMap K L) f} := by
    simp only [J, I, Ideal.map_span, Set.image_singleton]
    congr 1
    change {E (1 ⊗ₜ[K] f)} = _
    simp [E]
  have hp : (Ideal.span {MvPolynomial.map (algebraMap K L) f}).IsPrime := by
    rw [← hmap]
    infer_instance
  have hne : MvPolynomial.map (algebraMap K L) f ≠ 0 := by
    exact (map_ne_zero_iff _ (MvPolynomial.map_injective _ (algebraMap K L).injective)).mpr hf.ne_zero
  exact ((Ideal.span_singleton_prime hne).mp hp).irreducible

end
end CCDN
