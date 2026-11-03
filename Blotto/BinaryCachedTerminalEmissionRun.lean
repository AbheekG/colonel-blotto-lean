import Blotto.BinaryCachedTerminalPrimitiveRun
import Blotto.BinaryGroupReachedHeight
import Blotto.BinaryCachedRouteHeight

/-! Actual terminal execution now prices successful original-field emission
from retained routes. Uniform/mixed continuations and none/absolute positions
are unchanged. Reached cached fields derive every selected operand height;
metadata, fallback, original scaling/framing and physical costs are separate. -/

namespace Blotto.BinaryCachedTerminalEmissionRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryCachedTerminalPreparation BinaryCachedTerminalPromises
open BinaryCachedThreeDescriptorWork BinaryPRGResourceWork BinaryPRGTerminalWork BinaryCachedGroupInputHeight
open BinaryGroupRouteEmissionWork BinaryFactoryHeight

structure Ledger where
  continuation : ℕ
  emission : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.continuation + ledger.emission

def runPrepared {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (Option (FixedArrayTable n SignedWord) × ℕ) × Ledger :=
  match hs : prepared.pivot with
  | none =>
      let drawn := BinaryGroupRetainedPrimitiveRun.uniformRun prepared.uniform (prepared.uniform_canonical hC)
        (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hs)
        (prepared.count_bound hC hAd) K N scalar bits pos hp
      let emitted := emitOptionWithWork prepared.routes drawn.1.1
      ((emitted.1,drawn.1.2),⟨drawn.2,emitted.2⟩)
  | some selected =>
      let drawn := BinaryGroupRetainedPrimitiveRun.mixedRun prepared.mixed (prepared.mixed_canonical hC selected hs)
        (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hs)
        (prepared.count_bound hC hAd) K N outer scalar bits pos hp
      let emitted := emitMixedOptionWithWork prepared.routes selected drawn.1.1
      ((emitted.1,drawn.1.2),⟨drawn.2,emitted.2⟩)

theorem runPrepared_state {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runPrepared prepared hC hAd K N outer scalar bits pos hp).1 =
      (BinaryCachedTerminalPrimitiveRun.runPrepared prepared hC hAd K N outer scalar bits pos hp).1 := by
  unfold runPrepared BinaryCachedTerminalPrimitiveRun.runPrepared
  dsimp only
  split
  · rename_i hNone
    rw [emitOptionWithWork_state]
    split
    · rfl
    · rename_i selected hSome; cases hNone.symm.trans hSome
  · rename_i selected hSome
    rw [emitMixedOptionWithWork_state]
    split
    · rename_i hNone; cases hSome.symm.trans hNone
    · rename_i other hOther
      have he : selected = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      rfl

theorem runPrepared_continuation {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runPrepared prepared hC hAd K N outer scalar bits pos hp).2.continuation =
      (BinaryCachedTerminalPrimitiveRun.runPrepared prepared hC hAd K N outer scalar bits pos hp).2 := by
  unfold runPrepared BinaryCachedTerminalPrimitiveRun.runPrepared
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i selected hSome; cases hNone.symm.trans hSome
  · rename_i selected hSome
    split
    · rename_i hNone; cases hSome.symm.trans hNone
    · rename_i other hOther
      have he : selected = other := Option.some.inj (hSome.symm.trans hOther)
      subst other
      rfl

def groupHeight (s K : ℕ) : ℕ := expressionHeightBudget (max s (K + 2)) 72

theorem route_height_le (s K : ℕ) : expressionHeightBudget s 1 ≤ groupHeight s K := by
  have hm : expressionHeightBudget s 1 ≤ expressionHeightBudget (max s (K + 2)) 1 := by
    unfold expressionHeightBudget; gcongr; exact le_max_left _ _
  exact hm.trans (expressionHeightBudget_mono _ (by decide : 1 ≤ 72))

def emissionBound (n s K : ℕ) : ℕ := (n + 1) * opcodeBound (expressionHeightBudget (groupHeight s K) 1)

theorem uniform_emission_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (input : BinaryGroupInputs.UniformInput m) (hC : input.Canonical) (hAd : BinaryGroupSamplers.UniformAdmissible input)
    (hm : m = 2 ∨ m = 3) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hR : ∀ j, RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (hH : UniformHeights input s) (K N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (emitOptionWithWork routes (BinaryGroupRetainedPrimitiveRun.uniformRun input hC hAd hm K N scalar bits pos hp).1.1).2 ≤ emissionBound n s K := by
  have hState := BinaryGroupRetainedPrimitiveRun.uniformRun_state input hC hAd hm K N scalar bits pos hp
  have hCanon : ∀ row, (BinaryGroupRetainedPrimitiveRun.uniformRun input hC hAd hm K N scalar bits pos hp).1.1 = some row →
      ∀ g, CanonicalWord (row.read g) := by
    intro row hr
    exact BinaryGroupPartialRun.uniformRun_canonical input hC hAd hm K N scalar bits pos hp row ((congrArg Prod.fst hState).symm.trans hr)
  have hHeight : ∀ row, (BinaryGroupRetainedPrimitiveRun.uniformRun input hC hAd hm K N scalar bits pos hp).1.1 = some row →
      ∀ g, RationalHeight (value (row.read g)) (groupHeight s K) := by
    intro row hr g
    exact (BinaryGroupReachedHeight.uniform_success_height input hC hAd hm s (by omega) hH K N scalar bits pos hp row
      ((congrArg Prod.fst hState).symm.trans hr) g).mono (expressionHeightBudget_mono _ (by decide : 21 ≤ 72))
  have hd := emitOptionWithWork_bound routes _ hRoutes hCanon _ (fun j => (hR j).mono (route_height_le s K)) hHeight
  exact hd.trans (Nat.mul_le_mul (Nat.le_succ n) (opcodeBound_mono (expressionHeightBudget_ge_input _ 1)))

theorem mixed_emission_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (selected : Fin n)
    (input : BinaryGroupInputs.MixedInput m) (hC : input.Canonical) (hAd : BinaryGroupSamplers.MixedAdmissible input)
    (hm : m = 2 ∨ m = 3) (hRoutes : ∀ j, CanonicalWord (routes.read j).2)
    (s : ℕ) (hs : 3 ≤ s) (hR : ∀ j, RationalHeight (value (routes.read j).2) (expressionHeightBudget s 1))
    (hH : MixedHeights input s) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (emitMixedOptionWithWork routes selected (BinaryGroupRetainedPrimitiveRun.mixedRun input hC hAd hm K N outer scalar bits pos hp).1.1).2 ≤ emissionBound n s K := by
  have hState := BinaryGroupRetainedPrimitiveRun.mixedRun_state input hC hAd hm K N outer scalar bits pos hp
  have hCanon : ∀ row, (BinaryGroupRetainedPrimitiveRun.mixedRun input hC hAd hm K N outer scalar bits pos hp).1.1 = some row →
      ∀ g, CanonicalWord (row.read g) := by
    intro row hr
    exact BinaryGroupPartialRun.mixedRun_canonical input hC hAd hm K N outer scalar bits pos hp row ((congrArg Prod.fst hState).symm.trans hr)
  have hHeight : ∀ row, (BinaryGroupRetainedPrimitiveRun.mixedRun input hC hAd hm K N outer scalar bits pos hp).1.1 = some row →
      ∀ g, RationalHeight (value (row.read g)) (groupHeight s K) := by
    intro row hr
    exact BinaryGroupReachedHeight.mixed_success_height input hC hAd hm s (by omega) hH K N outer scalar bits pos hp row ((congrArg Prod.fst hState).symm.trans hr)
  exact emitMixedOptionWithWork_bound routes selected _ hRoutes hCanon _
    (height_three (hs.trans (le_max_left _ _))) (fun j => (hR j).mono (route_height_le s K)) hHeight

theorem runPrepared_emission_bound {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hU : UniformHeights prepared.uniform s)
    (hM : ∀ selected, prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hR : ∀ j, RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runPrepared prepared hC hAd K N outer scalar bits pos hp).2.emission ≤ emissionBound n s K := by
  unfold runPrepared
  dsimp only
  split
  · rename_i hNone
    exact uniform_emission_bound prepared.routes prepared.uniform (prepared.uniform_canonical hC)
      (BinaryCachedTerminalPromises.Prepared.uniform_admissible prepared hC hAd hNone) (prepared.count_bound hC hAd)
      (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) s hs hR hU K N scalar bits pos hp
  · rename_i selected hSome
    exact mixed_emission_bound prepared.routes selected prepared.mixed (prepared.mixed_canonical hC selected hSome)
      (BinaryCachedTerminalPromises.Prepared.mixed_admissible prepared hC hAd selected hSome) (prepared.count_bound hC hAd)
      (BinaryCachedTerminalPromises.Prepared.routes_canonical prepared hC) s hs hR (hM selected hSome) K N outer scalar bits pos hp

def bound (n s K remaining : ℕ) : ℕ := BinaryCachedTerminalPrimitiveRun.bound s K remaining + emissionBound n s K

theorem runPrepared_bound {n : ℕ} {input : BinaryTerminalGrouping.Input n} (prepared : Prepared input)
    (hC : input.Canonical) (hAd : BinaryTerminalPromises.Admissible input)
    (s : ℕ) (hs : 3 ≤ s) (hU : UniformHeights prepared.uniform s)
    (hM : ∀ selected, prepared.pivot = some selected → MixedHeights prepared.mixed s)
    (hR : ∀ j, RationalHeight (value (prepared.routes.read j).2) (expressionHeightBudget s 1))
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) (pos : ℕ) (hp : pos ≤ N) :
    (runPrepared prepared hC hAd K N outer scalar bits pos hp).2.recorded ≤ bound n s K (N - pos) := by
  have hc := BinaryCachedTerminalPrimitiveRun.runPrepared_bound prepared hC hAd s hs hU hM K N outer scalar bits pos hp
  rw [← runPrepared_continuation prepared hC hAd K N outer scalar bits pos hp] at hc
  exact Nat.add_le_add hc (runPrepared_emission_bound prepared hC hAd s hs hU hM hR K N outer scalar bits pos hp)

theorem reached_bound {n : ℕ} (request : BinaryPRGRequest.Request n) (rich : Bool) (N : ℕ) (bits : Fin N → Bool)
    (state : BinaryResourcePair.Certified (resourceInput request rich).length)
    (h : (resourceWork request rich N bits).1.1 = some state)
    (K M : ℕ) (outer scalar : Fin K → Bool) (choice : Fin M → Bool) (pos : ℕ) (hp : pos ≤ M) :
    (runPrepared (prepare (terminalInput request rich state)) (terminal_canonical request rich state)
      (terminal_admissible request rich N bits state h) K M outer scalar choice pos hp).2.recorded ≤
        bound n (BinaryCachedTerminalPrimitiveRun.requestHeight request) K (M - pos) := by
  apply runPrepared_bound _ _ _ _ (le_max_right _ _)
    (BinaryCachedTerminalPrimitiveRun.uniformHeights_mono (cached_uniform_heights request rich N bits state h) (le_max_left _ _))
    (fun selected hPivot => BinaryCachedTerminalPrimitiveRun.mixedHeights_mono (cached_mixed_heights request rich N bits state h selected hPivot) (le_max_left _ _))
    _ K M outer scalar choice pos hp
  intro j
  have hh := BinaryCachedRouteHeight.reached_route_height request rich N bits state h j
  have hm : expressionHeightBudget (inputHeight request) 1 ≤ expressionHeightBudget (BinaryCachedTerminalPrimitiveRun.requestHeight request) 1 := by
    unfold BinaryCachedTerminalPrimitiveRun.requestHeight expressionHeightBudget; gcongr; exact le_max_left _ _
  exact hh.mono hm

end Blotto.BinaryCachedTerminalEmissionRun
