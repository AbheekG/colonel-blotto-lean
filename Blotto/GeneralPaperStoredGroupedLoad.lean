import Blotto.GeneralPaperStoredOuterAttachment

/-! Grouped dispatch loads the outer address and marker, derives the inner
width by the priced predecessor, and re-encodes the actual loaded root at
that width. It never treats an outer-width payload as an inner-width root. -/
namespace Blotto.GeneralPaperStoredGroupedLoad
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperStoredChildRead (Child)
open GeneralPaperMixedReferenceMemory (Word)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192

theorem word_bound {I : ℕ} (word : FixedBinaryWord I) : word.value < 2 ^ I := by
  simpa only [FixedBinaryWord.value,word.size] using BinaryBorrowWord.littleValue_bounds word.bits

theorem word_injective {I : ℕ} (first second : FixedBinaryWord I) (h : first.value = second.value) : first = second := by
  cases first with
  | mk a ha =>
    cases second with
    | mk b hb =>
      have hBits : a = b := BinaryBorrowWord.littleValue_injective a b (ha.trans hb.symm) h
      subst b
      rfl

theorem reencode {I : ℕ} (word : FixedBinaryWord I) : FixedBinaryWord.ofNat I word.value = word :=
  word_injective _ _ (FixedBinaryWord.value_ofNat I word.value (word_bound word))

def load (model : RationalCostModel) (A : ℕ) (installed : Installed A) : Option Child × ℕ :=
  let address := GeneralPaperStoredOuterRead.address model A installed
  let marker := GeneralPaperStoredOuterRead.field model A installed 2
  match address.1,marker.1 with
  | some outer,some ⟨B,tag⟩ =>
    if tag.value = 1 then
      let pointer := GeneralPaperStoredOuterRead.field model A installed 0
      match pointer.1 with
      | none => (none,address.2 + marker.2 + pointer.2 + B + 128 * (A + 1))
      | some ⟨C,root⟩ =>
        let inner := GeneralPaperStoredFreshCollect.previous model A outer
        let narrowed := GeneralPaperStoredWordEncoding.word model A inner.1 root.value
        (some ⟨inner.1,GeneralPaperStoredScalarRead.atRoot installed narrowed.1⟩,
          address.2 + marker.2 + pointer.2 + inner.2 + narrowed.2 + B + C + 128 * (A + B + C + inner.1 + 1))
    else (none,address.2 + marker.2 + B + 128 * (A + 1))
  | _,_ => (none,address.2 + marker.2 + 64 * (A + 1))

theorem source (model : RationalCostModel) (I : ℕ) (installed : Installed (I + 1)) (root : FixedBinaryWord I)
    (hAddress : (GeneralPaperStoredOuterRead.address model (I + 1) installed).1 = some (I + 1))
    (hMarker : (GeneralPaperStoredOuterRead.field model (I + 1) installed 2).1 =
      some (⟨I + 1,FixedBinaryWord.ofNat (I + 1) 1⟩ : Word))
    (hRoot : (GeneralPaperStoredOuterRead.field model (I + 1) installed 0).1 =
      some (⟨I + 1,FixedBinaryWord.ofNat (I + 1) root.value⟩ : Word)) :
    (load model (I + 1) installed).1 = some (⟨I,GeneralPaperStoredScalarRead.atRoot installed root⟩ : Child) := by
  have hOne : 1 < 2 ^ (I + 1) := by have h := Nat.two_pow_pos I; rw [pow_succ]; omega
  have hFits : root.value < 2 ^ (I + 1) := (word_bound root).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ I))
  simp only [load,hAddress,hMarker,FixedBinaryWord.value_ofNat _ 1 hOne,ite_true,hRoot,
    FixedBinaryWord.value_ofNat _ root.value hFits,GeneralPaperStoredFreshCollect.previous,
    GeneralPaperStoredWordEncoding.word_data,Nat.add_sub_cancel,reencode]
  rfl

end Blotto.GeneralPaperStoredGroupedLoad
