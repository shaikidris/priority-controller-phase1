module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Recognition.Record

@[expose] public section

/-! Producer-certificate data for the fixed 35-coordinate native core.
The record checker validates every block against the supplied source rows. -/

namespace Controller.Recognition.AcceptanceMetadataData
open Controller.CNF

def build (source : Formula (Fin 35)) (rows : source.clauses.size = 88) : ProducerMetadata.Record source where
  roots := {0, 1, 2, 3, 4}
  rank := fun index => (#[0, 0, 0, 0, 0, 4, 4, 5, 5, 2, 2, 2, 2, 3, 3, 3, 3, 6, 6, 7, 7, 7, 7, 10, 10, 10, 10, 11, 11, 11, 11, 12, 12, 13, 14] : Array Nat)[index.val]?.getD 0
  blocks := [
    { producer := { output := (9, true), gate := .and [(0, true), (2, true)] },
      origins := [⟨11, by omega⟩, ⟨12, by omega⟩, ⟨13, by omega⟩] },
    { producer := { output := (10, true), gate := .and [(1, true), (3, true)] },
      origins := [⟨14, by omega⟩, ⟨15, by omega⟩, ⟨16, by omega⟩] },
    { producer := { output := (11, true), gate := .and [(0, true), (2, true)] },
      origins := [⟨17, by omega⟩, ⟨18, by omega⟩, ⟨19, by omega⟩] },
    { producer := { output := (12, true), gate := .and [(1, true), (3, true)] },
      origins := [⟨20, by omega⟩, ⟨21, by omega⟩, ⟨22, by omega⟩] },
    { producer := { output := (13, true), gate := .not (9, true) },
      origins := [⟨23, by omega⟩, ⟨24, by omega⟩] },
    { producer := { output := (14, true), gate := .not (10, true) },
      origins := [⟨25, by omega⟩, ⟨26, by omega⟩] },
    { producer := { output := (15, true), gate := .not (11, true) },
      origins := [⟨27, by omega⟩, ⟨28, by omega⟩] },
    { producer := { output := (16, true), gate := .not (12, true) },
      origins := [⟨29, by omega⟩, ⟨30, by omega⟩] },
    { producer := { output := (5, true), gate := .and [(14, true)] },
      origins := [⟨0, by omega⟩, ⟨1, by omega⟩] },
    { producer := { output := (6, true), gate := .and [] },
      origins := [⟨2, by omega⟩] },
    { producer := { output := (7, true), gate := .and [(13, true), (5, true), (6, true)] },
      origins := [⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨6, by omega⟩] },
    { producer := { output := (8, true), gate := .and [(4, true), (5, true), (6, true)] },
      origins := [⟨7, by omega⟩, ⟨8, by omega⟩, ⟨9, by omega⟩, ⟨10, by omega⟩] },
    { producer := { output := (17, true), gate := .not (7, true) },
      origins := [⟨31, by omega⟩, ⟨32, by omega⟩] },
    { producer := { output := (18, true), gate := .not (8, true) },
      origins := [⟨33, by omega⟩, ⟨34, by omega⟩] },
    { producer := { output := (19, true), gate := .xor (17, true) (13, true) },
      origins := [⟨35, by omega⟩, ⟨36, by omega⟩, ⟨37, by omega⟩, ⟨38, by omega⟩] },
    { producer := { output := (20, true), gate := .xor (17, true) (14, true) },
      origins := [⟨39, by omega⟩, ⟨40, by omega⟩, ⟨41, by omega⟩, ⟨42, by omega⟩] },
    { producer := { output := (21, true), gate := .xor (18, true) (15, true) },
      origins := [⟨43, by omega⟩, ⟨44, by omega⟩, ⟨45, by omega⟩, ⟨46, by omega⟩] },
    { producer := { output := (22, true), gate := .xor (18, true) (16, true) },
      origins := [⟨47, by omega⟩, ⟨48, by omega⟩, ⟨49, by omega⟩, ⟨50, by omega⟩] },
    { producer := { output := (23, true), gate := .or [(17, false), (2, true)] },
      origins := [⟨51, by omega⟩, ⟨52, by omega⟩, ⟨53, by omega⟩] },
    { producer := { output := (24, true), gate := .or [(17, false), (3, true)] },
      origins := [⟨54, by omega⟩, ⟨55, by omega⟩, ⟨56, by omega⟩] },
    { producer := { output := (25, true), gate := .or [(18, false), (2, true)] },
      origins := [⟨57, by omega⟩, ⟨58, by omega⟩, ⟨59, by omega⟩] },
    { producer := { output := (26, true), gate := .or [(18, false), (3, true)] },
      origins := [⟨60, by omega⟩, ⟨61, by omega⟩, ⟨62, by omega⟩] },
    { producer := { output := (27, true), gate := .and [(0, true), (23, true)] },
      origins := [⟨63, by omega⟩, ⟨64, by omega⟩, ⟨65, by omega⟩] },
    { producer := { output := (28, true), gate := .and [(1, true), (24, true)] },
      origins := [⟨66, by omega⟩, ⟨67, by omega⟩, ⟨68, by omega⟩] },
    { producer := { output := (29, true), gate := .and [(0, true), (25, true)] },
      origins := [⟨69, by omega⟩, ⟨70, by omega⟩, ⟨71, by omega⟩] },
    { producer := { output := (30, true), gate := .and [(1, true), (26, true)] },
      origins := [⟨72, by omega⟩, ⟨73, by omega⟩, ⟨74, by omega⟩] },
    { producer := { output := (31, true), gate := .alias (28, true) },
      origins := [⟨75, by omega⟩, ⟨76, by omega⟩] },
    { producer := { output := (32, true), gate := .alias (30, true) },
      origins := [⟨77, by omega⟩, ⟨78, by omega⟩] },
    { producer := { output := (33, true), gate := .xor (31, true) (32, true) },
      origins := [⟨79, by omega⟩, ⟨80, by omega⟩, ⟨81, by omega⟩, ⟨82, by omega⟩] },
    { producer := { output := (34, true), gate := .or [(33, true)] },
      origins := [⟨83, by omega⟩, ⟨84, by omega⟩] }
  ]

end Controller.Recognition.AcceptanceMetadataData
