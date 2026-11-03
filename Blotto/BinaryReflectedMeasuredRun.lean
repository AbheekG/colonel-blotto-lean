import Blotto.BinaryReflectedPreparedDraw
import Blotto.BinaryReflectedResourceWork
import Blotto.BinaryReflectedCachedRun

/-! Actual reflected execution joins one measured resource prefix and one
prepared terminal table. Selection and emission reuse the table under the same
cap/reader. The ledger records resource, terminal-input and draw primitives;
the nested profile factory and whole-model costs remain separate obligations. -/

namespace Blotto.BinaryReflectedMeasuredRun
open BinaryRationalNormalization BinaryRationalEncoding BinaryReflectedFourSetup
open BinarySharedResourceRun BinaryReflectedSerialRun

structure Ledger where
  resource : ℕ
  terminalInput : ℕ
  draw : ℕ
  deriving Repr, DecidableEq

def Ledger.recorded (ledger : Ledger) : ℕ := ledger.resource + ledger.terminalInput + ledger.draw

def run (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (Option (FixedArrayTable 4 SignedWord) × ℕ) × Ledger :=
  let resource := BinaryReflectedResourceWork.runWithCharge input hC N bits
  match hReached : resource.1.1 with
  | none => ((none,resource.1.2),⟨resource.2.booleanWork,0,0⟩)
  | some result =>
      have hSuccess : (setupRun input hC N bits).1 = some result :=
        (congrArg Prod.fst (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)).symm.trans hReached
      have hPosition : resource.1.2 ≤ N := by
        have he : resource.1.2 = (setupRun input hC N bits).2 :=
          congrArg Prod.snd (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)
        rw [he]
        exact setupRun_position input hC N bits
      let terminal := BinaryReflectedPreparedDraw.prepareTerminal input hC hAd N bits result hSuccess K outer
      let drawn := terminal.runIndexedWithWork N scalar bits resource.1.2 hPosition
      (drawn.1,⟨resource.2.booleanWork,terminal.inputWork,drawn.2⟩)

theorem categorical_position_eq {α : Type*} (fallback : α) (N : ℕ) (bits : Fin N → Bool)
    (cursor : BinaryCategoricalRun.Cursor α) (pos next : ℕ) (hp : pos ≤ N) (hn : next ≤ N) (h : pos = next) :
    BinaryCategoricalRun.runIndexed fallback N bits cursor pos hp = BinaryCategoricalRun.runIndexed fallback N bits cursor next hn := by
  cases h
  rfl

theorem run_state (input : BinaryFourParameters.Input) (hC : input.Canonical) (hAd : Admissible input)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).1 = BinaryReflectedCachedRun.run input hC hAd K N outer scalar bits := by
  unfold run
  dsimp only
  split
  · rename_i hNone
    have hEq := congrArg Prod.fst (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)
    rw [hNone] at hEq
    unfold BinaryReflectedCachedRun.run BinaryReflectedCachedRun.select
    dsimp only
    split
    · simp only [Option.map_none]
      exact congrArg (fun p => (none,p)) (congrArg Prod.snd (BinaryReflectedResourceWork.runWithCharge_state input hC N bits))
    · rename_i current hSome
      rw [hSome] at hEq
      cases hEq
  · rename_i result hReached
    have hSuccess : (setupRun input hC N bits).1 = some result :=
      (congrArg Prod.fst (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)).symm.trans hReached
    have hPosition := congrArg Prod.snd (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)
    dsimp only
    rw [BinaryReflectedPreparedDraw.Prepared.runIndexedWithWork_state]
    unfold BinaryReflectedCachedRun.run BinaryReflectedCachedRun.select
    dsimp only
    split
    · rename_i hOldNone
      rw [hOldNone] at hSuccess
      cases hSuccess
    · rename_i current hSome
      have hc : current = result := Option.some.inj (hSome.symm.trans hSuccess)
      subst current
      dsimp only
      rw [BinaryReflectedPreparedDraw.Prepared.selectIndexed_state _
        (BinaryTerminalProfileCompiler.profile_canonical _ result.state (prepare_canonical input hC) result.canonical K outer)
        (profile_nonnegative input hC hAd N bits result hSuccess K outer)]
      simp only [Option.map_map,Function.comp_def]
      congr 2 <;> first | exact categorical_position_eq _ _ _ _ _ _ _ _ hPosition | exact congrArg Prod.fst (categorical_position_eq _ _ _ _ _ _ _ _ hPosition) | exact congrArg Prod.snd (categorical_position_eq _ _ _ _ _ _ _ _ hPosition) | exact hPosition | apply proof_irrel_heq

def bound (s K N : ℕ) : ℕ := BinaryReflectedResourceWork.bound s N +
  BinaryNestedTerminalPreparationWork.bound (expressionHeightBudget s 21) + BinaryReflectedPreparedDraw.bound s K N

theorem draw_bound_mono (s K : ℕ) {a b : ℕ} (h : a ≤ b) :
    BinaryReflectedPreparedDraw.bound s K a ≤ BinaryReflectedPreparedDraw.bound s K b := by
  unfold BinaryReflectedPreparedDraw.bound BinaryReflectedCategoricalWork.bound BinaryStoredSegmentChoiceWork.selectionBound
  dsimp only
  gcongr

theorem run_bound (input : BinaryFourParameters.Input) (source : RationalFourInput)
    (hC : input.Canonical) (hR : input.Refines source) (hCase : source.w < (1 - source.p) * source.ell)
    (hAd : Admissible input) (s : ℕ) (hs : 2 ≤ s) (hH : source.FieldsHeight s)
    (K N : ℕ) (outer scalar : Fin K → Bool) (bits : Fin N → Bool) :
    (run input hC hAd K N outer scalar bits).2.recorded ≤ bound s K N := by
  have hResource := BinaryReflectedResourceWork.runWithCharge_bound input source hC hR hCase s hs hH N bits
  unfold run
  dsimp only
  split
  · dsimp only [Ledger.recorded]; unfold bound; omega
  · rename_i result he
    dsimp only [Ledger.recorded]
    have hSuccess : (setupRun input hC N bits).1 = some result :=
      (congrArg Prod.fst (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)).symm.trans he
    have hPosition : (BinaryReflectedResourceWork.runWithCharge input hC N bits).1.2 ≤ N := by
      have hp := congrArg Prod.snd (BinaryReflectedResourceWork.runWithCharge_state input hC N bits)
      rw [hp]
      exact setupRun_position input hC N bits
    let terminal := BinaryReflectedPreparedDraw.prepareTerminal input hC hAd N bits result hSuccess K outer
    have hInput := BinaryReflectedPreparedDraw.prepareTerminal_inputWork_bound input source hC hR hCase hAd s hs hH N bits result hSuccess K outer
    have hDraw := BinaryReflectedPreparedDraw.Prepared.runIndexedWithWork_bound input source hC hR hCase s hs hH N bits
      result hSuccess K outer scalar terminal (BinaryReflectedResourceWork.runWithCharge input hC N bits).1.2 hPosition
    have hDrawN := hDraw.trans (draw_bound_mono s K (Nat.sub_le _ _))
    unfold bound
    change (BinaryReflectedResourceWork.runWithCharge input hC N bits).2.booleanWork + terminal.inputWork +
      (terminal.runIndexedWithWork N scalar bits (BinaryReflectedResourceWork.runWithCharge input hC N bits).1.2 hPosition).2 ≤ _
    change terminal.inputWork ≤ _ at hInput
    omega

end Blotto.BinaryReflectedMeasuredRun
