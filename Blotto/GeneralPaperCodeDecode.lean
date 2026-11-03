import Blotto.GeneralPaperCodeSplit

/-! Literal paper decoder: grid closed/open at slots zero/one, and the
proved midpoint interior closed/open at slots two/three. Only slot zero is
valid at bucket C. Tail codes above 4*C are rejected before any division.
-/
namespace Blotto.GeneralPaperCodeDecode
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  choice : Option Choice
  work : ℕ

def decodeBucket (a : Alphabet) (response : Bool) (bucket slot : ℕ) : Result :=
  if bucket≤a.C then
    if slot=0 then ⟨some ⟨grid a bucket,false⟩,32⟩ else
    if slot=1 then
      if response=true ∧ bucket<a.C then ⟨some ⟨grid a bucket,true⟩,32⟩ else ⟨none,32⟩
    else if bucket<a.C ∧ (slot=2 ∨ (slot=3 ∧ response=true)) then
      let found := GeneralPaperMidpointQuery.lookup a.D a.C bucket a.lambda
      ⟨found.fraction.map (fun f => ⟨f,decide (slot=3)⟩),found.work+48⟩
    else ⟨none,32⟩
  else ⟨none,32⟩

def decode (a : Alphabet) (response : Bool) (code : ℕ) : Result :=
  if code≤4*a.C then
    let split := GeneralPaperCodeSplit.run code a.lambda
    let found := decodeBucket a response split.bucket split.slot
    ⟨found.choice,split.work+found.work+16⟩
  else ⟨none,16⟩

theorem at_grid (a : Alphabet) (response : Bool) (t : ℕ) (ht : t≤a.C) :
    (decodeBucket a response t 0).choice=some ⟨grid a t,false⟩ := by simp [decodeBucket,ht]

theorem at_grid_open (a : Alphabet) (t : ℕ) (ht : t<a.C) :
    (decodeBucket a true t 1).choice=some ⟨grid a t,true⟩ := by simp [decodeBucket,ht.le,ht]

theorem at_interior (a : Alphabet) (response : Bool) (t : ℕ) (ht : t<a.C) :
    (decodeBucket a response t 2).choice=(GeneralPaperMidpointQuery.lookup a.D a.C t a.lambda).fraction.map (fun f => ⟨f,false⟩) := by
  simp [decodeBucket,ht.le,ht]

theorem at_interior_open (a : Alphabet) (t : ℕ) (ht : t<a.C) :
    (decodeBucket a true t 3).choice=(GeneralPaperMidpointQuery.lookup a.D a.C t a.lambda).fraction.map (fun f => ⟨f,true⟩) := by
  simp [decodeBucket,ht.le,ht]

theorem at_endpoint (a : Alphabet) (response : Bool) (slot : ℕ) (hSlot : slot≠0) : (decodeBucket a response a.C slot).choice=none := by
  simp [decodeBucket,hSlot]

theorem tail_none (a : Alphabet) (response : Bool) (code : ℕ) (hTail : 4*a.C<code) : (decode a response code).choice=none := by
  simp only [decode,ite_eq_right (not_le.mpr hTail)]

theorem decode_at (a : Alphabet) (response : Bool) (t slot : ℕ) (hSlot : slot<4) (hCode : 4*t+slot≤4*a.C) :
    (decode a response (4*t+slot)).choice=(decodeBucket a response t slot).choice := by
  have he := GeneralPaperCodeSplit.run_pack a t slot hSlot hCode
  simp only [decode,ite_eq_left hCode,he.1,he.2]

end Blotto.GeneralPaperCodeDecode
