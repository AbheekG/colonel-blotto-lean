import Blotto.RationalNestedReachedConstructionMetadata
import Blotto.RationalFourCompleteProcessing
import Blotto.RationalFourSpecCompleteProcessing

/-! Terminal factory metadata follows the reached four-controller callbacks.
The dense reflected output retains four producer allowances; the unsorted
wrapper retains four more. Parent preparation is a separate component. -/

namespace Blotto.RationalFourInput

def smallConstructionMetadataCharge (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (primitive : ℕ → ℕ) (c K : ℕ) (outerBits : Fin K → Bool) : i.SmallState hcase → ℕ :=
  binaryCallbackCharge 0 (fun _ => 0)
    (fun state => 4 * (i.reflectedResourceSystem hcase).localConstructionMetadataCharge primitive c K outerBits state)

theorem FieldsHeight.smallConstructionMetadataCharge_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (hK : K + 2 ≤ s) (outerBits : Fin K → Bool)
    (cursor : i.SmallState hcase) (hCursor : i.smallCallbackInvariant hcase s cursor) :
    i.smallConstructionMetadataCharge hcase primitive c K outerBits cursor ≤
      8 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 21) K := by
  cases cursor with
  | start => exact Nat.zero_le _
  | upper state => exact Nat.zero_le _
  | lower state =>
    have hp := (h.reflectedResourceSystem hs hcase).localConstructionMetadataCharge_bound
      (hs.trans (expressionHeightBudget_ge_input s 14)) primitive c hPrimitive K
      (hK.trans (expressionHeightBudget_ge_input s 14)) outerBits state hCursor
    rw [expressionHeightBudget_comp] at hp
    change (i.reflectedResourceSystem hcase).localConstructionMetadataCharge primitive c K outerBits state ≤
      2 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 21) K at hp
    change 4 * (i.reflectedResourceSystem hcase).localConstructionMetadataCharge primitive c K outerBits state ≤ _
    omega

def fourConstructionMetadataCharge (i : RationalFourInput) (primitive : ℕ → ℕ) (c K : ℕ)
    (outerBits : Fin K → Bool) : FourSamplingState i → ℕ
  | .gluing _ _ => 0
  | .small hcase state => i.smallConstructionMetadataCharge hcase primitive c K outerBits state

theorem FieldsHeight.fourConstructionMetadataCharge_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (hK : K + 2 ≤ s)
    (outerBits : Fin K → Bool) (cursor : FourSamplingState i) (hCursor : i.fourCallbackInvariant s cursor) :
    i.fourConstructionMetadataCharge primitive c K outerBits cursor ≤
      8 * RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget s 21) K := by
  cases cursor with
  | gluing hcase state => exact Nat.zero_le _
  | small hcase state => exact h.smallConstructionMetadataCharge_bound hs hcase primitive c hPrimitive K hK outerBits state hCursor

noncomputable def fourConstructionMetadataWork (i : RationalFourInput) (primitive : ℕ → ℕ) (c K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  (i.machine K outerBits scalarBits).cachedCallbackWork (i.fourConstructionMetadataCharge primitive c K outerBits)
    N bits (.state (i.start K outerBits scalarBits)) pos hpos

theorem FieldsHeight.fourConstructionMetadataWork_bound {i : RationalFourInput} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.fourConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos ≤
      648 * RationalTerminalResources.profileConstructionMetadataBound c
        (expressionHeightBudget (max s (K + 2)) 21) K := by
  let w := max s (K + 2)
  let price := RationalTerminalResources.profileConstructionMetadataBound c (expressionHeightBudget w 21) K
  have hW := h.mono (le_max_left s (K + 2))
  have hw := hs.trans (le_max_left s (K + 2))
  have hK := le_max_right s (K + 2)
  have hp := (i.machine K outerBits scalarBits).cachedCallbackWork_state_bound_under
    (i.fourCallbackInvariant w) (hW.fourCallback_closed hw K hK outerBits scalarBits)
    (i.fourConstructionMetadataCharge primitive c K outerBits) (8 * price)
    (fun cursor hCursor => hW.fourConstructionMetadataCharge_bound hw primitive c hPrimitive K hK outerBits cursor hCursor)
    N bits (i.start K outerBits scalarBits) (hW.fourCallback_start hw K outerBits scalarBits) pos hpos
  have hr : (i.machine K outerBits scalarBits).rank (i.start K outerBits scalarBits) + 1 ≤ 81 := by
    have hc := i.machine_rank K outerBits scalarBits
    omega
  have hp' := hp.trans (Nat.mul_le_mul_left (8 * price) hr)
  change i.fourConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos ≤ 648 * price
  exact hp'.trans_eq (by ring)

end Blotto.RationalFourInput

namespace Blotto.RationalFourSpec

noncomputable def runtimeConstructionMetadataWork (i : RationalFourSpec) (primitive : ℕ → ℕ) (c K : ℕ)
    (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  4 * i.input.fourConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.runtimeConstructionMetadataWork_bound {i : RationalFourSpec} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.runtimeConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos ≤
      2592 * RationalTerminalResources.profileConstructionMetadataBound c
        (expressionHeightBudget (max s (K + 2)) 21) K := by
  have hp := h.input.fourConstructionMetadataWork_bound hs primitive c hPrimitive K outerBits scalarBits N bits pos hpos
  unfold runtimeConstructionMetadataWork
  omega

end Blotto.RationalFourSpec
