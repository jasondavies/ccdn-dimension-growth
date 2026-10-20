module

public import AffineCurveCounting.GridCurveConstruction
public import Mathlib.RingTheory.Polynomial.Basic

/-! Enlarging the ambient affine space preserves the irreducible grid equation. -/

@[expose] public section
namespace AffineCurveCounting
noncomputable section
open MvPolynomial

lemma irreducible_rename_of_injective {K σ τ : Type*} [Field K]
    (i : σ → τ) (hi : Function.Injective i) (f : MvPolynomial σ K)
    (hf : Irreducible f) : Irreducible (rename i f) := by
  classical
  let e : σ ≃ Set.range i := Equiv.ofInjective i hi
  have he : rename i f = rename Subtype.val (renameEquiv K e f) := by
    rw [renameEquiv_apply, rename_rename]
    rfl
  rw [he]
  apply Prime.irreducible
  apply (prime_rename_iff (Set.range i)).mpr
  apply irreducible_iff_prime.mp
  exact (MulEquiv.irreducible_iff (f := renameEquiv K e)).mpr hf

lemma totalDegree_rename_of_leftInverse {K σ τ : Type*} [CommRing K]
    (i : σ → τ) (r : τ → σ) (hr : Function.LeftInverse r i)
    (f : MvPolynomial σ K) : (rename i f).totalDegree = f.totalDegree := by
  apply le_antisymm (totalDegree_rename_le i f)
  have h := totalDegree_rename_le r (rename i f)
  have he : rename r (rename i f) = f := by
    rw [rename_rename]
    have hc : r ∘ i = id := funext hr
    simp [hc, rename_id]
  rwa [he] at h

/-- The square-grid construction in any ambient dimension at least two.
The added variables are free; irreducibility is preserved by polynomial extension. -/
theorem exists_absolutely_irreducible_grid
    {K L : Type*} [Field K] [Infinite K] [Field L] (φ : K →+* L)
    (s : Finset K) (hs : 0 < s.card) (d n : ℕ) (hn : 2 ≤ n)
    (hd : s.card + 2 ≤ d) (hsize : 2 * s.card ≤ d + 1) :
    ∃ f : MvPolynomial (Fin n) K,
      f.totalDegree = d ∧ Irreducible (map φ f) ∧
        ∀ z : Fin n → K, (∀ i, z i ∈ s) → eval z f = 0 := by
  classical
  obtain ⟨f, hfdeg, hfir, hfzero⟩ :=
    exists_absolutely_irreducible_plane_grid φ s hs d hd hsize
  let i : Fin 2 → Fin n := Fin.castLE hn
  have hi : Function.Injective i := Fin.castLE_injective hn
  let r : Fin n → Fin 2 := fun j => if j.val = 0 then 0 else 1
  have hr : Function.LeftInverse r i := by
    intro j
    fin_cases j <;> simp [r, i]
  refine ⟨rename i f, ?_, ?_, ?_⟩
  · rw [totalDegree_rename_of_leftInverse i r hr, hfdeg]
  · rw [map_rename]
    exact irreducible_rename_of_injective i hi _ hfir
  · intro z hz
    rw [eval_rename]
    exact hfzero _ (fun j => hz (i j))

end
end AffineCurveCounting
