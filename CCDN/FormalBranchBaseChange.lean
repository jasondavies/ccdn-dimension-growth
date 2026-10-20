module

public import CCDN.PowerSeriesBaseChange
public import CCDN.FormalBranchFaithful
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

/-! A faithful formal branch remains faithful after arbitrary field extension.
The construction is an actual embedding of the extended coordinate algebra
into power series over the extension field. -/

@[expose] public section
namespace CCDN
noncomputable section
open scoped TensorProduct

/-- Extend a power-series-valued algebra map by scalars. -/
def formalBranchBaseChange {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K) :
    L ⊗[K] A →ₐ[L] PowerSeries L :=
  AlgHom.liftEquiv K L A (PowerSeries L)
    ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp ψ)

@[simp] lemma formalBranchBaseChange_tmul
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K) (a : L) (x : A) :
    formalBranchBaseChange (L := L) ψ (a ⊗ₜ[K] x) =
      a • PowerSeries.map (algebraMap K L) (ψ x) := rfl

/-- No new algebra relation appears after extending a faithful formal branch. -/
theorem formalBranchBaseChange_injective
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K)
    (hψ : Function.Injective ψ) :
    Function.Injective (formalBranchBaseChange (L := L) ψ) := by
  let b := Module.Free.chooseBasis K A
  let φ := ((PowerSeries.mapAlgHom (Algebra.ofId K L)).comp ψ).toLinearMap
  change Function.Injective (φ.liftBaseChange L)
  rw [LinearMap.liftBaseChange_injective_iff φ b]
  exact powerSeries_linearIndependent_map_of_linearIndependent (ψ ∘ b)
    (b.linearIndependent.map' ψ.toLinearMap (LinearMap.ker_eq_bot.mpr hψ))

/-- Any algebra admitting a faithful power-series branch stays a domain under
an arbitrary extension of its coefficient field. -/
theorem isDomain_tensor_of_faithful_formal_branch
    {K L A : Type*} [Field K] [Field L] [Algebra K L]
    [CommRing A] [Algebra K A] (ψ : A →ₐ[K] PowerSeries K)
    (hψ : Function.Injective ψ) : IsDomain (L ⊗[K] A) :=
  Function.Injective.isDomain (formalBranchBaseChange (L := L) ψ)
    (formalBranchBaseChange_injective ψ hψ)

/-- The coordinate algebra of an irreducible plane curve with a smooth
rational point is a domain after every field extension. -/
theorem isDomain_tensor_plane_quotient_of_smooth_point
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : MvPolynomial (Fin 2) K) (hf : Irreducible f)
    (z : Fin 2 → K) (j : Fin 2)
    (hz : MvPolynomial.eval z f = 0)
    (hj : MvPolynomial.eval z (MvPolynomial.pderiv j f) ≠ 0) :
    IsDomain (L ⊗[K] (MvPolynomial (Fin 2) K ⧸ Ideal.span {f})) := by
  obtain ⟨ψ, _, _, hψ⟩ := exists_faithful_formal_plane_branch f hf z j hz hj
  let I : Ideal (MvPolynomial (Fin 2) K) := Ideal.span {f}
  have hkill : ∀ a ∈ I, ψ a = 0 := by
    intro a ha
    exact (hψ a).mpr (Ideal.mem_span_singleton.mp ha)
  let φ := Ideal.Quotient.liftₐ I ψ hkill
  have hφ : Function.Injective φ := by
    apply RingHom.lift_injective_of_ker_le_ideal
    intro a ha
    exact Ideal.mem_span_singleton.mpr ((hψ a).mp ha)
  exact isDomain_tensor_of_faithful_formal_branch φ hφ

end
end CCDN
