import Blotto.BinaryReflectedFactoryPrepared
import Blotto.BinaryReflectedMeasuredRun

/-! Reflected execution now records resource, terminal input, the actual full
nested factory, and reuse of its table for draw/emission. Every seed retains the
old row/none/absolute-position semantics. Original source heights bound the
complete recorded primitive ledger. Setup before this resource prefix and
metadata/backend/physical-space costs remain separate obligations. -/

namespace Blotto.BinaryReflectedFactoryRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun

structure Ledger where
  resource : ℕ
  terminalInput : ℕ
  factory : ℕ
  draw : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.resource + ledger.terminalInput + ledger.factory + ledger.draw

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × Ledger :=
  let resource := BinaryReflectedResourceWork.runWithCharge input hC N bits
  match hReached : resource.1.1 with
  | none => ((none,resource.1.2),⟨resource.2.booleanWork,0,0,0⟩)
  | some result =>
      have hSuccess : (setupRun input hC N bits).1 = some result :=
        (congrArg Prod.fst (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)).symm.trans hReached
      have hPosition : resource.1.2 ≤ N := by
        have he : resource.1.2 = (setupRun input hC N bits).2 :=
          congrArg Prod.snd (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)
        rw [he]
        exact setupRun_position input hC N bits
      let terminal := BinaryReflectedFactoryPrepared.prepareTerminal input hC hAd N bits result hSuccess K outer
      let drawn := terminal.toPrepared.runIndexedWithWork N scalar bits resource.1.2 hPosition
      (drawn.1,⟨resource.2.booleanWork,terminal.toPrepared.inputWork,terminal.factoryWork,drawn.2⟩)

theorem run_base (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).1 =
      (BinaryReflectedMeasuredRun.run input hC hAd K N outer scalar bits).1 := by
  unfold run BinaryReflectedMeasuredRun.run
  dsimp only
  split
  · rename_i hNone
    split
    · rfl
    · rename_i current hSome
      rw [hNone] at hSome
      cases hSome
  · rename_i result hReached
    dsimp only
    rw [BinaryReflectedFactoryPrepared.prepareTerminal_base]
    split
    · rename_i hNone
      rw [hReached] at hNone
      cases hNone
    · rename_i current hSome
      have hc : current = result := Option.some.inj (hSome.symm.trans hReached)
      subst current
      rfl

theorem run_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).1 = BinaryReflectedCachedRun.run input hC hAd K N outer scalar bits :=
  (run_base input hC hAd K N outer scalar bits).trans
    (BinaryReflectedMeasuredRun.run_state input hC hAd K N outer scalar bits)

def bound (s K N : ℕ) : ℕ := BinaryReflectedMeasuredRun.bound s K N + BinaryReflectedFactoryPrepared.bound s K

theorem run_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).2.recorded ≤ bound s K N := by
  have hResource := BinaryReflectedResourceWork.runWithCharge_bound input source hC hR hCase s hs hH N bits
  unfold run
  dsimp only
  split
  · dsimp only [Ledger.recorded]
    unfold bound BinaryReflectedMeasuredRun.bound
    omega
  · rename_i result he
    dsimp only [Ledger.recorded]
    have hSuccess : (setupRun input hC N bits).1 = some result :=
      (congrArg Prod.fst (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)).symm.trans he
    have hPosition : (BinaryReflectedResourceWork.runWithCharge input hC N bits).1.2 ≤ N := by
      have hp := congrArg Prod.snd (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)
      rw [hp]
      exact setupRun_position input hC N bits
    let terminal := BinaryReflectedFactoryPrepared.prepareTerminal input hC hAd N bits result hSuccess K outer
    have hInput : terminal.toPrepared.inputWork ≤ BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) := by
      rw [BinaryReflectedFactoryPrepared.prepareTerminal_base]
      exact BinaryReflectedPreparedDraw.prepareTerminal_inputWork_bound input source hC hR hCase hAd s hs hH N bits result hSuccess K outer
    have hFactory := BinaryReflectedFactoryPrepared.prepareTerminal_factoryWork_bound input source hC hR hCase hAd s hs hH N bits result hSuccess K outer
    have hDraw := BinaryReflectedPreparedDraw.Prepared.runIndexedWithWork_bound input source hC hR hCase s hs hH N bits
      result hSuccess K outer scalar terminal.toPrepared (BinaryReflectedResourceWork.runWithCharge input hC N bits).1.2 hPosition
    have hDrawN := hDraw.trans (BinaryReflectedMeasuredRun.draw_bound_mono s K (Nat.sub_le _ _))
    unfold bound BinaryReflectedMeasuredRun.bound
    change (BinaryReflectedResourceWork.runWithCharge input hC N bits).2.booleanWork + terminal.toPrepared.inputWork +
      terminal.factoryWork + (terminal.toPrepared.runIndexedWithWork N scalar bits (BinaryReflectedResourceWork.runWithCharge input hC N bits).1.2 hPosition).2 ≤ _
    change terminal.factoryWork ≤ _ at hFactory
    omega

end Blotto.BinaryReflectedFactoryRun
