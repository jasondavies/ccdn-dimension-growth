module

public import CCDN.FilteredDeterminant
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-! Weighted generators from ideal-adic layers of a Noetherian ring.

The layer is the image of `I^k` in `A/I^(k+1)`, hence is a quotient
of ideals. If `A/I` is finite,
Noetherianity makes every truncation finite. Bases of these layers
therefore give generators with exactly the layer dimensions. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- The degree-`k` ideal-adic layer, realized in the next truncation. -/
def idealPowerLayer (K : Type*) [Field K] {A : Type*} [CommRing A] [Algebra K A]
    (I : Ideal A) (k : ℕ) : Submodule K (A ⧸ I ^ (k + 1)) :=
  ((I ^ k).restrictScalars K).map (Ideal.Quotient.mkₐ K (I ^ (k + 1))).toLinearMap

instance idealPowerLayer_finite (I : Ideal A) [IsNoetherianRing A]
    [Finite (A ⧸ I)] (k : ℕ) : Module.Finite K (idealPowerLayer K I k) := by
  let : Finite (A ⧸ I ^ (k + 1)) :=
    Ideal.finite_quotient_pow (IsNoetherian.noetherian I) (k + 1)
  infer_instance

/-- Basis vectors lift to members of `I^k`. Their images are a basis,
so they reduce every element of `I^k` modulo `I^(k+1)`. -/
theorem exists_idealPowerLayer_generators (I : Ideal A) [IsNoetherianRing A]
    [Finite (A ⧸ I)] (k : ℕ) :
    ∃ g : Fin (Module.finrank K (idealPowerLayer K I k)) → A,
      (∀ j, g j ∈ I ^ k) ∧
      ∀ u ∈ I ^ k, ∃ c : Fin (Module.finrank K (idealPowerLayer K I k)) → K,
        u - ∑ j, c j • g j ∈ I ^ (k + 1) := by
  classical
  let b := Module.finBasis K (idealPowerLayer K I k)
  let φ := (Ideal.Quotient.mkₐ K (I ^ (k + 1))).toLinearMap
  have hlift : ∀ j, ∃ g : A, g ∈ I ^ k ∧ φ g = (b j).val := by
    intro j
    exact Submodule.mem_map.mp (b j).property
  choose g hg he using hlift
  refine ⟨g, hg, ?_⟩
  intro u hu
  let ubar : idealPowerLayer K I k := ⟨φ u, Submodule.mem_map.mpr ⟨u, hu, rfl⟩⟩
  refine ⟨fun j => b.repr ubar j, ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (u - ∑ j, b.repr ubar j • g j) = 0
  rw [map_sub, map_sum]
  simp only [map_smul, he]
  apply sub_eq_zero.mpr
  have hsum := congrArg Subtype.val (b.sum_repr ubar)
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using hsum.symm

/-- Successive reductions by the layers give a spanning family for
every finite truncation. -/
lemma ideal_layers_generate_truncation (I : Ideal A) (r : ℕ → ℕ)
    (g : (k : ℕ) → Fin (r k) → A)
    (hspan : ∀ k u, u ∈ I ^ k → ∃ c : Fin (r k) → K,
      u - ∑ j, c j • g k j ∈ I ^ (k + 1))
    (N : ℕ) (u : A) :
    ∃ c : (k : Fin N) → Fin (r k.val) → K,
      u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ I ^ N := by
  classical
  induction N with
  | zero =>
    refine ⟨fun k => Fin.elim0 k, ?_⟩
    simp
  | succ N ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨b, hb⟩ := hspan N (u - ∑ k : Fin N, ∑ j, c k j • g k.val j) hc
    let c' : (k : Fin (N + 1)) → Fin (r k.val) → K := Fin.lastCases b c
    refine ⟨c', ?_⟩
    rw [Fin.sum_univ_castSucc]
    simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, Fin.val_last]
    convert hb using 1
    abel

/-- Noetherianity and a finite residue quotient construct all weighted
generators; their numbers are exactly the ideal-layer dimensions. -/
theorem exists_noetherian_truncation_generators (I : Ideal A) [IsNoetherianRing A]
    [Finite (A ⧸ I)] :
    ∃ g : (k : ℕ) → Fin (Module.finrank K (idealPowerLayer K I k)) → A,
      (∀ k j, g k j ∈ I ^ k) ∧
      ∀ N u, ∃ c : (k : Fin N) →
          Fin (Module.finrank K (idealPowerLayer K I k.val)) → K,
        u - ∑ k : Fin N, ∑ j, c k j • g k.val j ∈ I ^ N := by
  classical
  choose g hg hs using fun k => exists_idealPowerLayer_generators (K := K) I k
  exact ⟨g, hg, ideal_layers_generate_truncation I _ g hs⟩

end
end CCDN
