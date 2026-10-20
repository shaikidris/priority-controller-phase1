module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/
public import Controller.Cost.ClauseProfileCounts

@[expose] public section


/-! Full coordinate dictionaries cover every channel. Their emitted positive
row has one distinct local ID per channel, independently of clause multiplicity. -/
namespace Controller.Cost.FullDictionaryProfile

open Controller.Cost Controller.Cost.ForestZeroCompile Controller.Cost.ForestZeroPositive

variable {ambient : Nat}

theorem member (dictionary : Dictionary ambient) (count label : Nat) :
    label ∈ channelLabels dictionary count ↔
      ∃ index < count, label = ForestZeroNonempty.slotAt dictionary index - 1 := by
  induction count with
  | zero => simp [channelLabels]
  | succ count ih =>
      simp only [channelLabels, List.mem_cons, ih]
      constructor
      · rintro (last | ⟨index, before, same⟩)
        · exact ⟨count, by omega, last⟩
        · exact ⟨index, by omega, same⟩
      · rintro ⟨index, before, same⟩
        by_cases last : index = count
        · subst index; exact Or.inl same
        · exact Or.inr ⟨index, by omega, same⟩

theorem nodup (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (full : ∀ coordinate : Fin ambient, dictionary.slots[coordinate.val] ≠ 0)
    (count : Nat) (within : count ≤ ambient) : (channelLabels dictionary count).Nodup := by
  induction count with
  | zero => simp [channelLabels]
  | succ count ih =>
      rw [channelLabels, List.nodup_cons]
      refine ⟨?_, ih (by omega)⟩
      intro present
      obtain ⟨index, before, equal⟩ := (member dictionary count _).mp present
      have countBound : count < ambient := by omega
      have indexBound : index < ambient := by omega
      let last : Fin ambient := ⟨count, countBound⟩
      let earlier : Fin ambient := ⟨index, indexBound⟩
      have lastPositive := full last
      have earlierPositive := full earlier
      simp only [ForestZeroNonempty.slotAt, dif_pos countBound, dif_pos indexBound] at equal
      have slots : dictionary.slots[count] = dictionary.slots[index] := by
        dsimp only [last, earlier] at lastPositive earlierPositive
        omega
      have lastEncoded : dictionary.slots[count] = dictionary.slots[count] - 1 + 1 := by
        dsimp only [last] at lastPositive
        omega
      have earlierEncoded : dictionary.slots[index] = dictionary.slots[index] - 1 + 1 := by
        dsimp only [earlier] at earlierPositive
        omega
      have lastCell := (coherent last (dictionary.slots[count] - 1)).mp lastEncoded
      have earlierCell := (coherent earlier (dictionary.slots[index] - 1)).mp earlierEncoded
      rw [slots, earlierCell] at lastCell
      have values := congrArg Fin.val (Option.some.inj lastCell)
      dsimp only [last, earlier] at values
      omega

theorem positive (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (full : ∀ coordinate : Fin ambient, dictionary.slots[coordinate.val] ≠ 0)
    (channels : Nat) (within : channels ≤ ambient) :
    (Controller.Horn.Worklist.compileClause (positiveClause dictionary channels)).positives.length =
      channels := by
  rw [positiveClause, ClauseProfileCounts.positive_clause,
    List.dedup_eq_self.mpr (nodup dictionary coherent full channels within), channelLabels_length]

theorem covered (dictionary : Dictionary ambient) (coherent : Coherent dictionary)
    (full : ∀ coordinate : Fin ambient, dictionary.slots[coordinate.val] ≠ 0)
    (channels : Nat) (within : channels ≤ ambient) :
    (ForestZeroNonempty.search dictionary (dictionary.coordinates.size + 1) channels 0).reason =
      .covered := by
  rcases ForestZeroNonempty.search_outcome dictionary coherent channels within with unused | covered
  · obtain ⟨_, channel, zero⟩ := unused
    exact False.elim (full ⟨channel.val, lt_of_lt_of_le channel.isLt within⟩ zero)
  · exact covered.1

end Controller.Cost.FullDictionaryProfile
