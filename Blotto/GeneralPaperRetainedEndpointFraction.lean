import Blotto.GeneralPaperRawAffineEndpoint

/-! Recover the endpoint's constructed raw fraction from the retained
root/cell/branch tags. This reads no numerator or denominator of a rational
input and reruns no quotient, root query or proxy selection. The zero
endpoint on an unchanged branch is represented by 0/1. -/
namespace Blotto.GeneralPaperRetainedEndpointFraction
set_option autoImplicit false
set_option maxHeartbeats 3500000

def run (primitive : ℕ → ℕ) (W Q : ℕ) (hQ : 0<Q)
    (classified : GeneralPaperProxyClassifier.Result) : Farey.Fraction×ℕ :=
  if classified.choice.modify=none then (⟨0,1,by decide⟩,64*W) else
  match classified.root with
  | some f => (f,64*W)
  | none =>
    if classified.choice.modify=some .rich then
      (⟨classified.cell+1,Q,hQ⟩,64*W+
        GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) classified.cell 1)
    else (⟨classified.cell,Q,hQ⟩,64*W)

theorem selected_value (primitive : ℕ → ℕ) (W Q j : ℕ) (hQ : 0<Q) (b : ℝ)
    (root : Option Farey.Fraction) (work : ℕ) :
    (run primitive W Q hQ ⟨j,root,GeneralPaperProxySelection.select Q j hQ b root,work⟩).1.value=
      (GeneralPaperProxySelection.select Q j hQ b root).endpoint := by
  unfold GeneralPaperProxySelection.select
  split
  · simp [run,Farey.Fraction.value]
  · cases root with
    | none =>
      dsimp only
      split_ifs <;> simp [run,Farey.Fraction.value,GeneralPaperBucketGeometry.upper,
        GeneralPaperBucketGeometry.lower,Nat.cast_add,Nat.cast_one]
    | some f =>
      dsimp only
      split_ifs <;> simp [run,Farey.Fraction.value]

theorem actual_value (primitive : ℕ → ℕ) (W m k : ℕ) (b : ℝ) :
    (run primitive W (GeneralPaperProxyParameters.prepare m k).Qg (GeneralPaperProxyParameters.grid_positive m k)
      (GeneralPaperProxyClassifier.classify m k b)).1.value=
      (GeneralPaperProxyClassifier.classify m k b).choice.endpoint := by
  exact selected_value primitive W _ _ _ b _ _

theorem arithmetic_work (Q : ℕ) (hQ : 0<Q) (classified : GeneralPaperProxyClassifier.Result) :
    (run (fun _ => 1) 1 Q hQ classified).2≤66 := by
  simp only [run]
  split
  · norm_num
  · cases classified.root <;> dsimp only
    · split <;> norm_num [GeneralPaperNaturalPrimitivePrice.binary]
    · norm_num

theorem data (primitive primitive' : ℕ → ℕ) (W W' Q : ℕ) (hQ : 0<Q)
    (classified : GeneralPaperProxyClassifier.Result) :
    (run primitive W Q hQ classified).1=(run primitive' W' Q hQ classified).1 := by
  simp only [run]
  split
  · rfl
  · cases classified.root <;> dsimp only
    · split <;> rfl

end Blotto.GeneralPaperRetainedEndpointFraction
