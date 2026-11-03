import Blotto.GeneralPaperSourceBasisGridSize

/-! Actual prepared source inputs supply the size premises at any native
stage with the established invariant. This includes the actual full basis
return. All raw point-solve dot prefixes are bounded as well as final
stored products and reduced point/direction entries.
-/
namespace Blotto.GeneralPaperSourceBasisStageSize
open GeneralPaperBasisStoredProducts GeneralPaperBasisFreshRHS GeneralPaperBasisInvariant
open GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4500000

def Contract (m k j N B : ℕ) (betaN : ℤ) (initialGrid : Vector (m*((prepare m k).K-1)))
    (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1))) : Prop :=
  state.determinant.natAbs≤(prepare m k).H ∧
  (∀ a b,((state.adjugate.read a).read b).natAbs≤(prepare m k).H) ∧
  (∀ i,((rhsRun N betaN state.rows initialGrid).1.read i).natAbs≤GeneralPaperBasisFreshRHSSize.bound m (prepare m k).K N B) ∧
  (∀ i t,(GeneralPaperBasisIntegerDot.loop (fun a => (state.adjugate.read i).read a)
      (rhsRun N betaN state.rows initialGrid).1.read ((List.finRange j).take t) 0 0).value.natAbs≤
        j*(prepare m k).H*GeneralPaperBasisFreshRHSSize.bound m (prepare m k).K N B) ∧
  (∀ a,RationalHeight ((GeneralPaperBasisFreshPoint.run N betaN state.determinant state.adjugate state.rows initialGrid).point.read a)
    (binaryWordWidth N+binaryWordWidth (prepare m k).H)) ∧
  (∀ next : Fin (m*((prepare m k).K-1)),next.val=j → ∀ a,
    RationalHeight ((GeneralPaperBasisDirection.run state.determinant state.adjugate state.rows next).velocity.read a)
      (GeneralPaperBasisStageSize.velocityWidth m k j))

theorem stage {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∀ j (hj : j≤m*((prepare m k).K-1)) (state : GeneralPaperBasisState.State j (m*((prepare m k).K-1))),
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid hj state →
      Contract m k j inputs.controls.N (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) inputs.betaN inputs.initialGrid state := by
  dsimp only
  intro j hj state inv
  have hc := GeneralPaperBasisCacheSize.cache_H k hm _ _ _ _ _ _ _ hj state inv
  have hg := GeneralPaperSourceBasisGridSize.grid k Qv hm hQv weights hp hs b hb reciprocal
  have hbN := GeneralPaperSourceBasisGridSize.auxiliary (m:=m) k b hb reciprocal
  have hn := (GeneralPaperInitializerSelectedControls.positive m k hm b hb reciprocal).1
  have hr := GeneralPaperBasisFreshRHSSize.rhs hm _ _ _ _ _ _ _ hj state inv
    (GeneralPaperSourceBasisGridSize.auxiliaryBound m k) hbN hg
  refine ⟨hc.1,hc.2,hr,?_,?_,?_⟩
  · intro i t
    have hh := GeneralPaperIntegerDotSize.prefix_bound (fun a => (state.adjugate.read i).read a)
      (rhsRun _ _ state.rows _).1.read (List.finRange j) 0 0 (prepare m k).H
      (GeneralPaperBasisFreshRHSSize.bound m (prepare m k).K _ (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)) t
      (fun a _ => hc.2 i a) (fun a _ => hr a)
    simpa only [Int.natAbs_zero,Nat.zero_add,List.length_finRange] using hh
  · exact GeneralPaperBasisStageSize.point_height k hm _ _ _ _ _ hn _ _ hj state inv
  · intro next hNext a
    exact GeneralPaperBasisStageSize.direction_height k hm _ _ _ _ _ _ _ hj state inv next hNext a

theorem actual_return {m : ℕ} (k Qv : ℕ) (hm : 0<m) (hQv : 0<Qv) (weights : FixedArrayTable m ℕ)
    (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℝ) (hb : 0<b ∧ b<1) (reciprocal : Bool) :
    let prep := GeneralPaperSourceInitializer.prepared k Qv hQv weights hp hs b reciprocal
    let v := GeneralPaperNativeRationalValues.selector Qv hQv weights hp hs
    let f := (GeneralPaperProxyClassifier.classify m k b).choice.proxy
    let inputs := GeneralPaperSharedBasisInputs.prepare k prep v f.num f.den reciprocal
    ∃ state,GeneralPaperSharedBasisInputs.basis prep inputs=some state ∧
      Invariant prep.dictionary v (prepare m k).S prep.threshold inputs.controls.N inputs.betaN inputs.initialGrid (Nat.le_refl _) state ∧
      Contract m k (m*((prepare m k).K-1)) inputs.controls.N (GeneralPaperSourceBasisGridSize.auxiliaryBound m k)
        inputs.betaN inputs.initialGrid state := by
  obtain ⟨state,hr,inv⟩ := GeneralPaperSharedBasisInputs.actual_source k Qv hm hQv weights hp hs b hb reciprocal
  exact ⟨state,hr,inv,stage k Qv hm hQv weights hp hs b hb reciprocal _ _ state inv⟩

end Blotto.GeneralPaperSourceBasisStageSize
