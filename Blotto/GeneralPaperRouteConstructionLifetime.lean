import Blotto.GeneralPaperRouteGroupFrames

/-! Route construction at every initial-array, group and member cursor and
at final return. One shared backing table has the proved partial-write
invariant. Group/member frames and both index-list buffers are reserved
alongside the caller and the complete returned prepared-route payload. -/
namespace Blotto.GeneralPaperRouteConstructionLifetime
open GeneralPaperEncodedScalarStorage (natBits fields)
open GeneralPaperEncodedBasisStorage (arrayFootprint)
open GeneralPaperEqualRetainedStorage (routeFoot)
open GeneralPaperRouteTableLifetime (initial Short)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

inductive Phase (n m : ℕ) where
  | initial (cursor : ℕ) (h : cursor ≤ n)
  | group (cursor : ℕ) (h : cursor ≤ m)
  | member (g : Fin m) (cursor : ℕ) (h : cursor ≤ n)
  | returned

def core {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :=
  GeneralPaperEqualRouteConstruction.groups p model A values (List.finRange i.groups.length) (initial values A).1

theorem price_shape {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) :
    (GeneralPaperEqualRouteConstruction.run p model A values).2 = (initial (m := i.groups.length) values A).2 +
      GeneralPaperEqualRouteConstruction.indicesWork A i.groups.length + (core p model A values).2 + 64 * A + 64 := by
  simp only [GeneralPaperEqualRouteConstruction.run, initial, core,
    GeneralPaperEqualRouteConstruction.indices_eq, p.groups.size]

def tableAt {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) : Phase n i.groups.length → FixedArrayTable n (GroupRoute i.groups.length)
  | .initial _ _ => (initial values A).1
  | .group cursor _ => (GeneralPaperEqualRouteConstruction.groups p model A values
      ((List.finRange i.groups.length).take cursor) (initial values A).1).1
  | .member g cursor _ =>
      let before := GeneralPaperEqualRouteConstruction.groups p model A values
        ((List.finRange i.groups.length).take g.val) (initial values A).1
      (GeneralPaperEqualRouteMembers.run model A values g (p.groups.read g).2 ((p.groups.read g).1.take cursor) before.1).1
  | .returned => (GeneralPaperEqualRouteConstruction.run p model A values).1

theorem table_short {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (hs : 2 ≤ s)
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : ∀ g, RationalHeight (p.groups.read g).2 s) (phase : Phase n i.groups.length) :
    Short s (tableAt p model A values phase) := by
  have hInitial := GeneralPaperRouteTableLifetime.initial_short (m := i.groups.length) values A hs
  cases phase with
  | initial cursor h => exact hInitial
  | group cursor h => exact GeneralPaperRouteTableLifetime.groups_short p model A values _ _ hv ht hInitial
  | member g cursor h =>
    exact GeneralPaperRouteTableLifetime.member_short model A values g (p.groups.read g).2 _ _ hv (ht g)
      (GeneralPaperRouteTableLifetime.groups_short p model A values _ _ hv ht hInitial)
  | returned =>
    change Short s (GeneralPaperEqualRouteConstruction.run p model A values).1
    unfold GeneralPaperEqualRouteConstruction.run
    dsimp only
    exact GeneralPaperRouteTableLifetime.groups_short p model A values _ _ hv ht hInitial

def phaseControls {n m : ℕ} : Phase n m → List ℕ
  | .initial cursor _ => [cursor]
  | .group cursor _ => [cursor]
  | .member g cursor _ => [g.val, cursor]
  | .returned => []

theorem phase_controls_bound (A n m : ℕ) (phase : Phase n m) :
    fields A (phaseControls phase) ≤ 2 * (natBits (n + m + 1) + A) + 32 * A := by
  have hLen : (phaseControls phase).length ≤ 2 := by cases phase <;> simp only [phaseControls, List.length_cons, List.length_nil] <;> omega
  have hPoint : ∀ x ∈ phaseControls phase, x ≤ n + m := by
    cases phase with
    | initial cursor h => intro x hx; simp only [phaseControls, List.mem_singleton] at hx; subst x; omega
    | group cursor h => intro x hx; simp only [phaseControls, List.mem_singleton] at hx; subst x; omega
    | member g cursor h =>
      intro x hx
      simp only [phaseControls, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> omega
    | returned => intro x hx; simp only [phaseControls, List.not_mem_nil] at hx
  have hFields := GeneralPaperEncodedScalarStorage.fields_bound A (natBits (n + m + 1)) (phaseControls phase) (by
    intro x hx
    exact Nat.add_le_add_left (binaryWordWidth_mono ((hPoint x hx).trans (Nat.le_succ _))) 1)
  exact hFields.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hLen) _)

def controls {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  let init := initial (m := i.groups.length) values A
  let indices := GeneralPaperEqualRouteConstruction.indicesWork A i.groups.length
  let done := core p model A values
  fields A [n, i.groups.length, init.2, indices, done.2, init.2 + indices,
    (GeneralPaperEqualRouteConstruction.run p model A values).2] + 128 * A

def controlProfile (A n m F : ℕ) : ℕ := 7 * (natBits (n + m + F + A + 1) + A) + 160 * A

theorem controls_bound {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A F : ℕ) (values : FixedArrayTable n ℚ)
    (hF : (GeneralPaperEqualRouteConstruction.run p model A values).2 ≤ F) :
    controls p model A values ≤ controlProfile A n i.groups.length F := by
  have hShape := price_shape p model A values
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A (n + i.groups.length + F + A + 1)
    [n, i.groups.length, (initial (m := i.groups.length) values A).2,
      GeneralPaperEqualRouteConstruction.indicesWork A i.groups.length, (core p model A values).2,
      (initial (m := i.groups.length) values A).2 + GeneralPaperEqualRouteConstruction.indicesWork A i.groups.length,
      (GeneralPaperEqualRouteConstruction.run p model A values).2] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 7 * (natBits (n + i.groups.length + F + A + 1) + A) + 32 * A at hFields
  unfold controls controlProfile
  dsimp only
  omega

def initialWindow {n m : ℕ} (A : ℕ) (_values : FixedArrayTable n ℚ) (cursor : ℕ) (h : cursor ≤ n) : ℕ :=
  GeneralPaperIndexedArrayLifetime.window id A (fun _ : Fin n => (((none, (0 : ℚ)) : GroupRoute m), 32 * A + 32))
    (routeFoot A) cursor h 0 (32 * A + 32)

theorem initial_bound {n m : ℕ} (A F s : ℕ) (values : FixedArrayTable n ℚ) (hs : 2 ≤ s)
    (hF : (initial (m := m) values A).2 ≤ F) (cursor : ℕ) (h : cursor ≤ n) :
    initialWindow (m := m) A values cursor h ≤ GeneralPaperRouteTableLifetime.profile A n m s +
      (n + 1) * GeneralPaperIndexedArrayLifetime.frame A n F + 32 * A + 32 := by
  let callback := fun _ : Fin n => (((none, (0 : ℚ)) : GroupRoute m), 32 * A + 32)
  have hPoint : ∀ j, routeFoot A (callback j).1 ≤ 4 + binaryWordWidth m + 2 * (2 * s) + 16 * A := by
    intro j
    exact GeneralPaperEqualRetainedStorage.route_bound A _
      ((show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (by omega))
  have hWindow := GeneralPaperIndexedArrayLifetime.window_bound id A callback (routeFoot A)
    (4 + binaryWordWidth m + 2 * (2 * s) + 16 * A) (32 * A + 32) hPoint cursor h 0 (32 * A + 32) le_rfl
  have hPrice : (PaperIndexedArrayConstruction.run id A callback).2 ≤ F := by
    change (GeneralPaperSizedBitArray.run values.data.size values.size A callback).2 ≤ F at hF
    rw [GeneralPaperSizedBitArray.eq_run] at hF
    exact hF
  have hFrames := Nat.mul_le_mul_left (n + 1) (GeneralPaperIndexedArrayLifetime.frame_mono A n _ _ hPrice)
  simp only [Nat.zero_add] at hWindow
  change initialWindow (m := m) A values cursor h ≤ _ at hWindow
  unfold GeneralPaperRouteTableLifetime.profile
  omega

def window {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A : ℕ) (values : FixedArrayTable n ℚ) (borrowed returnedPayload : ℕ) (phase : Phase n i.groups.length) : ℕ :=
  borrowed + returnedPayload + 2 * GeneralPaperPackingAllocationLifetime.indicesLive A i.groups.length i.groups.length +
    GeneralPaperRouteGroupFrames.frames p model A values (List.finRange i.groups.length) (initial values A).1 +
    controls p model A values + fields A (phaseControls phase) +
    match phase with
    | .initial cursor h => initialWindow (m := i.groups.length) A values cursor h
    | _ => arrayFootprint A (routeFoot A) (tableAt p model A values phase)

def profile (A n m F s borrowed returnedPayload : ℕ) : ℕ :=
  borrowed + returnedPayload + 2 * GeneralPaperPackingAllocationLifetime.indicesProfile A m +
    GeneralPaperRouteGroupFrames.profile A n m F s + controlProfile A n m F +
    (2 * (natBits (n + m + 1) + A) + 32 * A) + GeneralPaperRouteTableLifetime.profile A n m s +
    (n + 1) * GeneralPaperIndexedArrayLifetime.frame A n F + 32 * A + 32

theorem owner_mono (A n m F s B C R S : ℕ) (hB : B ≤ C) (hR : R ≤ S) :
    profile A n m F s B R ≤ profile A n m F s C S := by unfold profile; omega

theorem all_phases {n s : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (model : RationalCostModel) (A F : ℕ) (values : FixedArrayTable n ℚ) (hs : 2 ≤ s)
    (hv : ∀ j, RationalHeight (values.read j) s) (ht : ∀ g, RationalHeight (p.groups.read g).2 s)
    (hF : (GeneralPaperEqualRouteConstruction.run p model A values).2 ≤ F)
    (borrowed returnedPayload : ℕ) (phase : Phase n i.groups.length) :
    window p model A values borrowed returnedPayload phase ≤ profile A n i.groups.length F s borrowed returnedPayload := by
  have hShape := price_shape p model A values
  have hCore : (core p model A values).2 ≤ F := by omega
  have hInitial : (initial (m := i.groups.length) values A).2 ≤ F := by omega
  have hGroups := GeneralPaperRouteGroupFrames.bounded p model A F values (List.finRange i.groups.length) (initial values A).1 ht hCore
  rw [List.length_finRange] at hGroups
  have hGroupBound : GeneralPaperRouteGroupFrames.frames p model A values (List.finRange i.groups.length) (initial values A).1 ≤
      GeneralPaperRouteGroupFrames.profile A n i.groups.length F s := by
    unfold GeneralPaperRouteGroupFrames.profile
    change (GeneralPaperEqualRouteConstruction.groups p model A values (List.finRange i.groups.length) (initial values A).1).2 ≤ F at hCore
    omega
  have hControls := controls_bound p model A F values hF
  have hPhase := phase_controls_bound A n i.groups.length phase
  have hIndices := GeneralPaperPackingAllocationLifetime.indices_bound A i.groups.length i.groups.length le_rfl
  have hTable := GeneralPaperRouteTableLifetime.table_bound A s (tableAt p model A values phase) (table_short p model A values hs hv ht phase)
  cases phase with
  | initial cursor h =>
    have hFill := initial_bound A F s values hs hInitial cursor h
    simp only [window]
    unfold profile
    omega
  | group cursor h =>
    simp only [window]
    unfold profile
    omega
  | member g cursor h =>
    simp only [window]
    unfold profile
    omega
  | returned =>
    simp only [window]
    unfold profile
    omega

end Blotto.GeneralPaperRouteConstructionLifetime
