module

public import CCDN.Plane.PlaneCurveAssembly
/-! The affine residue points of an integer plane equation are the
zeros of its reduction. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

lemma planeResidue_card_eq_zero_card (f : MvPolynomial (Fin 2) ℤ) (p : ℕ) :
    Nat.card (PlaneResidue f p) =
      Nat.card {x : Fin 2 → ZMod p // eval x (MvPolynomial.map (Int.castRingHom (ZMod p)) f) = 0} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  simp only [eval_map]

end
end CCDN
