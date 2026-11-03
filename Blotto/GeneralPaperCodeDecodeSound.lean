import Blotto.GeneralPaperCodeDecode

/-! Literal code validity and bounded closed thresholds are derived from the
executed decoder. Candidates return only closed choices. Zero and closed one
are decoded explicitly; no external catalogue-validity predicate is supplied.
-/
namespace Blotto.GeneralPaperCodeDecodeSound
open GeneralPaperCodeAlphabet GeneralPaperCodeDecode
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem bucket_sound (a : Alphabet) (response : Bool) (t slot : ℕ) (choice : Choice)
    (hSome : (decodeBucket a response t slot).choice=some choice) :
    Denotes a response (4*t+slot) choice.threshold.value choice.opened ∧ choice.threshold.den≤a.C := by
  dsimp only [decodeBucket] at hSome
  split at hSome
  · rename_i ht
    split at hSome
    · rename_i hs
      subst slot
      have he := Option.some.inj hSome
      subst choice
      exact ⟨Or.inl ⟨t,ht,by omega,rfl,rfl⟩,le_rfl⟩
    · split at hSome
      · rename_i hs
        split at hSome
        · rename_i hMode
          subst slot
          have he := Option.some.inj hSome
          subst choice
          exact ⟨Or.inr (Or.inl ⟨hMode.1,t,hMode.2,rfl,rfl,rfl⟩),le_rfl⟩
        · cases hSome
      · split at hSome
        · rename_i hMode
          cases hQuery : (GeneralPaperMidpointQuery.lookup a.D a.C t a.lambda).fraction with
          | none => simp only [hQuery,Option.map_none,reduceCtorEq] at hSome
          | some f =>
            have he : (⟨f,decide (slot=3)⟩:Choice)=choice := by
              simpa only [hQuery,Option.map_some,Option.some.injEq] using hSome
            subst choice
            have hF := GeneralPaperMidpointQuery.lookup_sound a.D a.C t a.lambda f hQuery
            have hDen := GeneralPaperMidpointQuery.lookup_closed_denominator a.D a.C t a.lambda a.orderPositive a.separated f hQuery
            rcases hMode.2 with hs|⟨hs,hResponse⟩
            · subst slot
              exact ⟨Or.inr (Or.inr (Or.inl ⟨t,f,hMode.1,hF.1,hF.2,rfl,rfl,rfl⟩)),hDen⟩
            · subst slot
              exact ⟨Or.inr (Or.inr (Or.inr ⟨hResponse,t,f,hMode.1,hF.1,hF.2,rfl,rfl,rfl⟩)),hDen⟩
        · cases hSome
  · cases hSome

theorem decode_sound (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) :
    Denotes a response code choice.threshold.value choice.opened ∧ choice.threshold.den≤a.C := by
  dsimp only [decode] at hSome
  split at hSome
  · rename_i hCode
    have he := GeneralPaperCodeSplit.run_spec a code hCode
    have hBucket : (decodeBucket a response (GeneralPaperCodeSplit.run code a.lambda).bucket
      (GeneralPaperCodeSplit.run code a.lambda).slot).choice=some choice := hSome
    have hs := bucket_sound a response _ _ choice hBucket
    rw [←he.1] at hs
    exact hs
  · cases hSome

theorem decode_valid (a : Alphabet) (response : Bool) (code : ℕ) (choice : Choice)
    (hSome : (decode a response code).choice=some choice) : Valid a response code :=
  ⟨choice.threshold.value,choice.opened,(decode_sound a response code choice hSome).1⟩

theorem candidate_closed (a : Alphabet) (code : ℕ) (choice : Choice)
    (hSome : (decode a false code).choice=some choice) : choice.opened=false := by
  have he := (decode_sound a false code choice hSome).1
  rcases he with ⟨t,_,_,_,h⟩|⟨h,_⟩|⟨t,f,_,_,_,_,_,h⟩|⟨h,_⟩
  · exact h
  · cases h
  · exact h
  · cases h

theorem decode_grid (a : Alphabet) (response : Bool) (t : ℕ) (ht : t≤a.C) :
    (decode a response (4*t)).choice=some ⟨grid a t,false⟩ := by
  have he := decode_at a response t 0 (by decide) (by omega)
  simpa only [Nat.add_zero,at_grid a response t ht] using he

theorem decode_grid_open (a : Alphabet) (t : ℕ) (ht : t<a.C) :
    (decode a true (4*t+1)).choice=some ⟨grid a t,true⟩ := by
  rw [decode_at a true t 1 (by decide) (by omega),at_grid_open a t ht]

theorem decode_zero (a : Alphabet) (response : Bool) : (decode a response 0).choice=some ⟨grid a 0,false⟩ := by
  simpa only [Nat.mul_zero] using decode_grid a response 0 (Nat.zero_le _)

theorem decode_one (a : Alphabet) (response : Bool) : (decode a response (4*a.C)).choice=some ⟨grid a a.C,false⟩ :=
  decode_grid a response a.C le_rfl

theorem zero_tag (a : Alphabet) : (⟨grid a 0,false⟩:Choice).tag=0 := by
  unfold Choice.tag
  rw [grid_zero]
  rfl

end Blotto.GeneralPaperCodeDecodeSound
