import Blotto.BinaryReflectedRetainedFactoryPrepared
import Blotto.BinaryReflectedFactoryRun

/-! The reflected runner consumes one retained setup/capacity cache through
resource execution, terminal input, full factory and selected draw/emission.
Cold execution constructs/charges its prefix once. Every seed preserves the
original row/none/absolute position; original fields derive all recorded
primitive prices. Metadata/backend/physical execution remain separate. -/

namespace Blotto.BinaryReflectedRetainedFactoryRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun
abbrev Ledger := BinaryReflectedFactoryRun.Ledger

def runWithWork (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × Ledger :=
  let resource := BinaryReflectedCachedCertifiedResult.runWithCharge cached N bits
  match hReached : resource.1.1 with
  | none => ((none,resource.1.2),⟨resource.2.booleanWork,0,0,0⟩)
  | some result =>
      have hSuccess : (setupRun input hC N bits).1 = some result :=
        (congrArg Prod.fst (BinaryReflectedCachedCertifiedResult.runWithCharge_state input hC cached N bits)).symm.trans hReached
      have hPosition : resource.1.2 ≤ N := by
        have he := congrArg Prod.snd (BinaryReflectedCachedCertifiedResult.runWithCharge_state input hC cached N bits)
        rw [he]
        exact setupRun_position input hC N bits
      let terminal := BinaryReflectedRetainedFactoryPrepared.prepareTerminal input hC hAd cached N bits result hSuccess K outer
      let drawn := terminal.toPrepared.runIndexedWithWork N scalar bits resource.1.2 hPosition
      (drawn.1,⟨resource.2.booleanWork,terminal.toPrepared.inputWork,terminal.factoryWork,drawn.2⟩)

theorem draw_position_eq {input : BinaryFourParameters.Input} {state : BinaryThreeResourceState.State}
    {K : ℕ} {outer : Fin K → Bool} (prepared : BinaryReflectedPreparedDraw.Prepared input state K outer)
    (N : ℕ) (scalar : Fin K → Bool) (bits : Fin N → Bool) (pos next : ℕ) (hp : pos ≤ N) (hn : next ≤ N) (h : pos = next) :
    prepared.runIndexedWithWork N scalar bits pos hp = prepared.runIndexedWithWork N scalar bits next hn := by
  cases h
  rfl

theorem runWithWork_base (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (runWithWork input hC hAd cached K N outer scalar bits).1 = (BinaryReflectedFactoryRun.run input hC hAd K N outer scalar bits).1 := by
  have hEq := (BinaryReflectedCachedCertifiedResult.runWithCharge_state input hC cached N bits).trans
    (BinaryReflectedResourceWork.runWithCharge_state input hC N bits).symm
  have hState := congrArg Prod.fst hEq
  have hPosition := congrArg Prod.snd hEq
  unfold runWithWork BinaryReflectedFactoryRun.run
  dsimp only
  split
  · rename_i hNone
    rw [hNone] at hState
    split
    · exact congrArg (fun pos => (none,pos)) hPosition
    · rename_i current hSome
      rw [hSome] at hState
      cases hState
  · rename_i result hReached
    dsimp only
    rw [BinaryReflectedRetainedFactoryPrepared.prepareTerminal_base,BinaryReflectedRetainedFactoryPrepared.draw_ignores_inputWork]
    rw [hReached] at hState
    split
    · rename_i hNone
      rw [hNone] at hState
      cases hState
    · rename_i current hSome
      rw [hSome] at hState
      have hc : current = result := Option.some.inj hState.symm
      subst current
      exact congrArg Prod.fst (draw_position_eq _ N scalar bits _ _ _ _ hPosition)

theorem runWithWork_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (cached : BinaryReflectedSetupCache.Prepared input) (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (runWithWork input hC hAd cached K N outer scalar bits).1 = BinaryReflectedCachedRun.run input hC hAd K N outer scalar bits :=
  (runWithWork_base input hC hAd cached K N outer scalar bits).trans (BinaryReflectedFactoryRun.run_state input hC hAd K N outer scalar bits)

theorem runWithWork_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (cached : BinaryReflectedSetupCache.Prepared input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (runWithWork input hC hAd cached K N outer scalar bits).2.recorded ≤ BinaryReflectedFactoryRun.bound s K N := by
  have hResource := BinaryReflectedCachedCertifiedResult.runWithCharge_bound input source hC hR hCase s hs hH cached N bits
  unfold runWithWork
  dsimp only
  split
  · dsimp only [BinaryReflectedFactoryRun.Ledger.recorded]
    unfold BinaryReflectedFactoryRun.bound BinaryReflectedMeasuredRun.bound
    omega
  · rename_i result he
    have hSuccess : (setupRun input hC N bits).1 = some result :=
      (congrArg Prod.fst (BinaryReflectedCachedCertifiedResult.runWithCharge_state input hC cached N bits)).symm.trans he
    have hPosition : (BinaryReflectedCachedCertifiedResult.runWithCharge cached N bits).1.2 ≤ N := by
      rw [congrArg Prod.snd (BinaryReflectedCachedCertifiedResult.runWithCharge_state input hC cached N bits)]
      exact setupRun_position input hC N bits
    let terminal := BinaryReflectedRetainedFactoryPrepared.prepareTerminal input hC hAd cached N bits result hSuccess K outer
    have hInput := BinaryReflectedRetainedFactoryPrepared.prepareTerminal_inputWork_bound input source hC hR hCase hAd cached s hs hH N bits result hSuccess K outer
    have hFactory := BinaryReflectedRetainedFactoryPrepared.prepareTerminal_factoryWork_bound input source hC hR hCase hAd cached s hs hH N bits result hSuccess K outer
    have hDraw := BinaryReflectedPreparedDraw.Prepared.runIndexedWithWork_bound input source hC hR hCase s hs hH N bits result hSuccess
      K outer scalar terminal.toPrepared (BinaryReflectedCachedCertifiedResult.runWithCharge cached N bits).1.2 hPosition
    have hDrawN := hDraw.trans (BinaryReflectedMeasuredRun.draw_bound_mono s K (Nat.sub_le _ _))
    change terminal.toPrepared.inputWork ≤ _ at hInput
    change terminal.factoryWork ≤ _ at hFactory
    dsimp only [BinaryReflectedFactoryRun.Ledger.recorded]
    change (BinaryReflectedCachedCertifiedResult.runWithCharge cached N bits).2.booleanWork + terminal.toPrepared.inputWork + terminal.factoryWork +
      (terminal.toPrepared.runIndexedWithWork N scalar bits (BinaryReflectedCachedCertifiedResult.runWithCharge cached N bits).1.2 hPosition).2 ≤ _
    unfold BinaryReflectedFactoryRun.bound BinaryReflectedMeasuredRun.bound
    omega

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : (Option (FixedArrayTable 4 SignedWord) × ℕ) × ℕ :=
  let cached := BinaryReflectedSetupCache.prepareCache input hC
  let result := runWithWork input hC hAd cached K N outer scalar bits
  (result.1,cached.prefixWork + result.2.recorded)

theorem run_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).1 = BinaryReflectedCachedRun.run input hC hAd K N outer scalar bits :=
  runWithWork_state input hC hAd _ K N outer scalar bits

def bound (s K N : ℕ) : ℕ := BinaryReflectedSetupCache.bound s + BinaryReflectedFactoryRun.bound s K N

theorem run_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) : (run input hC hAd K N outer scalar bits).2 ≤ bound s K N :=
  Nat.add_le_add (BinaryReflectedSetupCache.prepareCache_bound input source hC hR hCase s hs hH)
    (runWithWork_bound input source hC hR hCase hAd _ s hs hH K N outer scalar bits)

end Blotto.BinaryReflectedRetainedFactoryRun
