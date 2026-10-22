module

/- Copyright (c) 2026 Idris Ali Shaik. SPDX-License-Identifier: Apache-2.0 -/

public import Controller.Certificate.LRATAdapter

@[expose] public section

/-! Finite resolution and LRAT traces for the positive-output acceptance witness.
These are untrusted certificate data, replayed by the existing checker. -/

namespace Controller.Recognition.AcceptanceCertificates

def core : Array (Controller.Certificate.Certificate 35) := #[
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 1, right := 89, pivot := (5, true), clause := [(14, true)] }, { id := 92, left := 91, right := 90, pivot := (14, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 2, right := 89, pivot := (5, false), clause := [(14, false)] }, { id := 92, left := 91, right := 90, pivot := (14, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 89, steps := [{ id := 90, left := 3, right := 89, pivot := (6, false), clause := [] }], finalClauseId := 90 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 4, right := 89, pivot := (7, true), clause := [(13, true)] }, { id := 92, left := 91, right := 90, pivot := (13, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 5, right := 89, pivot := (7, true), clause := [(5, true)] }, { id := 92, left := 91, right := 90, pivot := (5, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 6, right := 89, pivot := (7, true), clause := [(6, true)] }, { id := 92, left := 91, right := 90, pivot := (6, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 7, right := 89, pivot := (7, false), clause := [(13, false), (5, false), (6, false)] }, { id := 94, left := 93, right := 90, pivot := (13, true), clause := [(5, false), (6, false)] }, { id := 95, left := 94, right := 91, pivot := (5, true), clause := [(6, false)] }, { id := 96, left := 95, right := 92, pivot := (6, true), clause := [] }], finalClauseId := 96 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 8, right := 89, pivot := (8, true), clause := [(4, true)] }, { id := 92, left := 91, right := 90, pivot := (4, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 9, right := 89, pivot := (8, true), clause := [(5, true)] }, { id := 92, left := 91, right := 90, pivot := (5, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 10, right := 89, pivot := (8, true), clause := [(6, true)] }, { id := 92, left := 91, right := 90, pivot := (6, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 11, right := 89, pivot := (8, false), clause := [(4, false), (5, false), (6, false)] }, { id := 94, left := 93, right := 90, pivot := (4, true), clause := [(5, false), (6, false)] }, { id := 95, left := 94, right := 91, pivot := (5, true), clause := [(6, false)] }, { id := 96, left := 95, right := 92, pivot := (6, true), clause := [] }], finalClauseId := 96 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 12, right := 89, pivot := (9, true), clause := [(0, true)] }, { id := 92, left := 91, right := 90, pivot := (0, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 13, right := 89, pivot := (9, true), clause := [(2, true)] }, { id := 92, left := 91, right := 90, pivot := (2, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 14, right := 89, pivot := (9, false), clause := [(0, false), (2, false)] }, { id := 93, left := 92, right := 90, pivot := (0, true), clause := [(2, false)] }, { id := 94, left := 93, right := 91, pivot := (2, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 15, right := 89, pivot := (10, true), clause := [(1, true)] }, { id := 92, left := 91, right := 90, pivot := (1, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 16, right := 89, pivot := (10, true), clause := [(3, true)] }, { id := 92, left := 91, right := 90, pivot := (3, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 17, right := 89, pivot := (10, false), clause := [(1, false), (3, false)] }, { id := 93, left := 92, right := 90, pivot := (1, true), clause := [(3, false)] }, { id := 94, left := 93, right := 91, pivot := (3, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 18, right := 89, pivot := (11, true), clause := [(0, true)] }, { id := 92, left := 91, right := 90, pivot := (0, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 19, right := 89, pivot := (11, true), clause := [(2, true)] }, { id := 92, left := 91, right := 90, pivot := (2, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 20, right := 89, pivot := (11, false), clause := [(0, false), (2, false)] }, { id := 93, left := 92, right := 90, pivot := (0, true), clause := [(2, false)] }, { id := 94, left := 93, right := 91, pivot := (2, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 21, right := 89, pivot := (12, true), clause := [(1, true)] }, { id := 92, left := 91, right := 90, pivot := (1, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 22, right := 89, pivot := (12, true), clause := [(3, true)] }, { id := 92, left := 91, right := 90, pivot := (3, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 23, right := 89, pivot := (12, false), clause := [(1, false), (3, false)] }, { id := 93, left := 92, right := 90, pivot := (1, true), clause := [(3, false)] }, { id := 94, left := 93, right := 91, pivot := (3, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 24, right := 89, pivot := (13, false), clause := [(9, true)] }, { id := 92, left := 91, right := 90, pivot := (9, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 25, right := 89, pivot := (13, true), clause := [(9, false)] }, { id := 92, left := 91, right := 90, pivot := (9, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 26, right := 89, pivot := (14, false), clause := [(10, true)] }, { id := 92, left := 91, right := 90, pivot := (10, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 27, right := 89, pivot := (14, true), clause := [(10, false)] }, { id := 92, left := 91, right := 90, pivot := (10, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 28, right := 89, pivot := (15, false), clause := [(11, true)] }, { id := 92, left := 91, right := 90, pivot := (11, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 29, right := 89, pivot := (15, true), clause := [(11, false)] }, { id := 92, left := 91, right := 90, pivot := (11, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 30, right := 89, pivot := (16, false), clause := [(12, true)] }, { id := 92, left := 91, right := 90, pivot := (12, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 31, right := 89, pivot := (16, true), clause := [(12, false)] }, { id := 92, left := 91, right := 90, pivot := (12, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 32, right := 89, pivot := (17, false), clause := [(7, true)] }, { id := 92, left := 91, right := 90, pivot := (7, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 33, right := 89, pivot := (17, true), clause := [(7, false)] }, { id := 92, left := 91, right := 90, pivot := (7, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 34, right := 89, pivot := (18, false), clause := [(8, true)] }, { id := 92, left := 91, right := 90, pivot := (8, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 35, right := 89, pivot := (18, true), clause := [(8, false)] }, { id := 92, left := 91, right := 90, pivot := (8, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 36, right := 89, pivot := (17, false), clause := [(13, true), (19, false)] }, { id := 93, left := 92, right := 90, pivot := (13, false), clause := [(19, false)] }, { id := 94, left := 93, right := 91, pivot := (19, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 37, right := 89, pivot := (17, true), clause := [(13, false), (19, false)] }, { id := 93, left := 92, right := 90, pivot := (13, true), clause := [(19, false)] }, { id := 94, left := 93, right := 91, pivot := (19, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 38, right := 89, pivot := (17, false), clause := [(13, false), (19, true)] }, { id := 93, left := 92, right := 90, pivot := (13, true), clause := [(19, true)] }, { id := 94, left := 93, right := 91, pivot := (19, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 39, right := 89, pivot := (17, true), clause := [(13, true), (19, true)] }, { id := 93, left := 92, right := 90, pivot := (13, false), clause := [(19, true)] }, { id := 94, left := 93, right := 91, pivot := (19, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 40, right := 89, pivot := (17, false), clause := [(14, true), (20, false)] }, { id := 93, left := 92, right := 90, pivot := (14, false), clause := [(20, false)] }, { id := 94, left := 93, right := 91, pivot := (20, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 41, right := 89, pivot := (17, true), clause := [(14, false), (20, false)] }, { id := 93, left := 92, right := 90, pivot := (14, true), clause := [(20, false)] }, { id := 94, left := 93, right := 91, pivot := (20, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 42, right := 89, pivot := (17, false), clause := [(14, false), (20, true)] }, { id := 93, left := 92, right := 90, pivot := (14, true), clause := [(20, true)] }, { id := 94, left := 93, right := 91, pivot := (20, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 43, right := 89, pivot := (17, true), clause := [(14, true), (20, true)] }, { id := 93, left := 92, right := 90, pivot := (14, false), clause := [(20, true)] }, { id := 94, left := 93, right := 91, pivot := (20, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 44, right := 89, pivot := (18, false), clause := [(15, true), (21, false)] }, { id := 93, left := 92, right := 90, pivot := (15, false), clause := [(21, false)] }, { id := 94, left := 93, right := 91, pivot := (21, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 45, right := 89, pivot := (18, true), clause := [(15, false), (21, false)] }, { id := 93, left := 92, right := 90, pivot := (15, true), clause := [(21, false)] }, { id := 94, left := 93, right := 91, pivot := (21, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 46, right := 89, pivot := (18, false), clause := [(15, false), (21, true)] }, { id := 93, left := 92, right := 90, pivot := (15, true), clause := [(21, true)] }, { id := 94, left := 93, right := 91, pivot := (21, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 47, right := 89, pivot := (18, true), clause := [(15, true), (21, true)] }, { id := 93, left := 92, right := 90, pivot := (15, false), clause := [(21, true)] }, { id := 94, left := 93, right := 91, pivot := (21, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 48, right := 89, pivot := (18, false), clause := [(16, true), (22, false)] }, { id := 93, left := 92, right := 90, pivot := (16, false), clause := [(22, false)] }, { id := 94, left := 93, right := 91, pivot := (22, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 49, right := 89, pivot := (18, true), clause := [(16, false), (22, false)] }, { id := 93, left := 92, right := 90, pivot := (16, true), clause := [(22, false)] }, { id := 94, left := 93, right := 91, pivot := (22, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 50, right := 89, pivot := (18, false), clause := [(16, false), (22, true)] }, { id := 93, left := 92, right := 90, pivot := (16, true), clause := [(22, true)] }, { id := 94, left := 93, right := 91, pivot := (22, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 51, right := 89, pivot := (18, true), clause := [(16, true), (22, true)] }, { id := 93, left := 92, right := 90, pivot := (16, false), clause := [(22, true)] }, { id := 94, left := 93, right := 91, pivot := (22, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 52, right := 89, pivot := (23, false), clause := [(17, true)] }, { id := 92, left := 91, right := 90, pivot := (17, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 53, right := 89, pivot := (23, false), clause := [(2, false)] }, { id := 92, left := 91, right := 90, pivot := (2, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 54, right := 89, pivot := (23, true), clause := [(17, false), (2, true)] }, { id := 93, left := 92, right := 90, pivot := (17, true), clause := [(2, true)] }, { id := 94, left := 93, right := 91, pivot := (2, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 55, right := 89, pivot := (24, false), clause := [(17, true)] }, { id := 92, left := 91, right := 90, pivot := (17, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 56, right := 89, pivot := (24, false), clause := [(3, false)] }, { id := 92, left := 91, right := 90, pivot := (3, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 57, right := 89, pivot := (24, true), clause := [(17, false), (3, true)] }, { id := 93, left := 92, right := 90, pivot := (17, true), clause := [(3, true)] }, { id := 94, left := 93, right := 91, pivot := (3, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 58, right := 89, pivot := (25, false), clause := [(18, true)] }, { id := 92, left := 91, right := 90, pivot := (18, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 59, right := 89, pivot := (25, false), clause := [(2, false)] }, { id := 92, left := 91, right := 90, pivot := (2, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 60, right := 89, pivot := (25, true), clause := [(18, false), (2, true)] }, { id := 93, left := 92, right := 90, pivot := (18, true), clause := [(2, true)] }, { id := 94, left := 93, right := 91, pivot := (2, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 61, right := 89, pivot := (26, false), clause := [(18, true)] }, { id := 92, left := 91, right := 90, pivot := (18, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 62, right := 89, pivot := (26, false), clause := [(3, false)] }, { id := 92, left := 91, right := 90, pivot := (3, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 63, right := 89, pivot := (26, true), clause := [(18, false), (3, true)] }, { id := 93, left := 92, right := 90, pivot := (18, true), clause := [(3, true)] }, { id := 94, left := 93, right := 91, pivot := (3, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 64, right := 89, pivot := (27, true), clause := [(0, true)] }, { id := 92, left := 91, right := 90, pivot := (0, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 65, right := 89, pivot := (27, true), clause := [(23, true)] }, { id := 92, left := 91, right := 90, pivot := (23, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 66, right := 89, pivot := (27, false), clause := [(0, false), (23, false)] }, { id := 93, left := 92, right := 90, pivot := (0, true), clause := [(23, false)] }, { id := 94, left := 93, right := 91, pivot := (23, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 67, right := 89, pivot := (28, true), clause := [(1, true)] }, { id := 92, left := 91, right := 90, pivot := (1, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 68, right := 89, pivot := (28, true), clause := [(24, true)] }, { id := 92, left := 91, right := 90, pivot := (24, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 69, right := 89, pivot := (28, false), clause := [(1, false), (24, false)] }, { id := 93, left := 92, right := 90, pivot := (1, true), clause := [(24, false)] }, { id := 94, left := 93, right := 91, pivot := (24, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 70, right := 89, pivot := (29, true), clause := [(0, true)] }, { id := 92, left := 91, right := 90, pivot := (0, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 71, right := 89, pivot := (29, true), clause := [(25, true)] }, { id := 92, left := 91, right := 90, pivot := (25, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 72, right := 89, pivot := (29, false), clause := [(0, false), (25, false)] }, { id := 93, left := 92, right := 90, pivot := (0, true), clause := [(25, false)] }, { id := 94, left := 93, right := 91, pivot := (25, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 73, right := 89, pivot := (30, true), clause := [(1, true)] }, { id := 92, left := 91, right := 90, pivot := (1, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 74, right := 89, pivot := (30, true), clause := [(26, true)] }, { id := 92, left := 91, right := 90, pivot := (26, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 75, right := 89, pivot := (30, false), clause := [(1, false), (26, false)] }, { id := 93, left := 92, right := 90, pivot := (1, true), clause := [(26, false)] }, { id := 94, left := 93, right := 91, pivot := (26, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 76, right := 89, pivot := (31, true), clause := [(28, true)] }, { id := 92, left := 91, right := 90, pivot := (28, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 77, right := 89, pivot := (31, false), clause := [(28, false)] }, { id := 92, left := 91, right := 90, pivot := (28, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 78, right := 89, pivot := (32, true), clause := [(30, true)] }, { id := 92, left := 91, right := 90, pivot := (30, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 79, right := 89, pivot := (32, false), clause := [(30, false)] }, { id := 92, left := 91, right := 90, pivot := (30, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 80, right := 89, pivot := (31, false), clause := [(32, true), (33, false)] }, { id := 93, left := 92, right := 90, pivot := (32, false), clause := [(33, false)] }, { id := 94, left := 93, right := 91, pivot := (33, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 81, right := 89, pivot := (31, true), clause := [(32, false), (33, false)] }, { id := 93, left := 92, right := 90, pivot := (32, true), clause := [(33, false)] }, { id := 94, left := 93, right := 91, pivot := (33, true), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 82, right := 89, pivot := (31, false), clause := [(32, false), (33, true)] }, { id := 93, left := 92, right := 90, pivot := (32, true), clause := [(33, true)] }, { id := 94, left := 93, right := 91, pivot := (33, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 91, steps := [{ id := 92, left := 83, right := 89, pivot := (31, true), clause := [(32, true), (33, true)] }, { id := 93, left := 92, right := 90, pivot := (32, false), clause := [(33, true)] }, { id := 94, left := 93, right := 91, pivot := (33, false), clause := [] }], finalClauseId := 94 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 84, right := 89, pivot := (34, false), clause := [(33, false)] }, { id := 92, left := 91, right := 90, pivot := (33, true), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 90, steps := [{ id := 91, left := 85, right := 89, pivot := (34, true), clause := [(33, true)] }, { id := 92, left := 91, right := 90, pivot := (33, false), clause := [] }], finalClauseId := 92 },
  .resolution { originalClauseCount := 89, steps := [{ id := 90, left := 86, right := 89, pivot := (13, true), clause := [] }], finalClauseId := 90 },
  .resolution { originalClauseCount := 89, steps := [{ id := 90, left := 87, right := 89, pivot := (5, false), clause := [] }], finalClauseId := 90 },
  .resolution { originalClauseCount := 89, steps := [{ id := 90, left := 88, right := 89, pivot := (4, false), clause := [] }], finalClauseId := 90 }
]

def source : Array (Controller.Certificate.Certificate 36) := #[
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 1, right := 92, pivot := (5, true), clause := [(14, true)] }, { id := 95, left := 94, right := 93, pivot := (14, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 2, right := 92, pivot := (5, false), clause := [(14, false)] }, { id := 95, left := 94, right := 93, pivot := (14, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 3, right := 92, pivot := (6, false), clause := [] }], finalClauseId := 93 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 4, right := 92, pivot := (7, true), clause := [(13, true)] }, { id := 95, left := 94, right := 93, pivot := (13, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 5, right := 92, pivot := (7, true), clause := [(5, true)] }, { id := 95, left := 94, right := 93, pivot := (5, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 6, right := 92, pivot := (7, true), clause := [(6, true)] }, { id := 95, left := 94, right := 93, pivot := (6, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 95, steps := [{ id := 96, left := 7, right := 92, pivot := (7, false), clause := [(13, false), (5, false), (6, false)] }, { id := 97, left := 96, right := 93, pivot := (13, true), clause := [(5, false), (6, false)] }, { id := 98, left := 97, right := 94, pivot := (5, true), clause := [(6, false)] }, { id := 99, left := 98, right := 95, pivot := (6, true), clause := [] }], finalClauseId := 99 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 8, right := 92, pivot := (8, true), clause := [(4, true)] }, { id := 95, left := 94, right := 93, pivot := (4, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 9, right := 92, pivot := (8, true), clause := [(5, true)] }, { id := 95, left := 94, right := 93, pivot := (5, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 10, right := 92, pivot := (8, true), clause := [(6, true)] }, { id := 95, left := 94, right := 93, pivot := (6, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 95, steps := [{ id := 96, left := 11, right := 92, pivot := (8, false), clause := [(4, false), (5, false), (6, false)] }, { id := 97, left := 96, right := 93, pivot := (4, true), clause := [(5, false), (6, false)] }, { id := 98, left := 97, right := 94, pivot := (5, true), clause := [(6, false)] }, { id := 99, left := 98, right := 95, pivot := (6, true), clause := [] }], finalClauseId := 99 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 12, right := 92, pivot := (9, true), clause := [(0, true)] }, { id := 95, left := 94, right := 93, pivot := (0, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 13, right := 92, pivot := (9, true), clause := [(2, true)] }, { id := 95, left := 94, right := 93, pivot := (2, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 14, right := 92, pivot := (9, false), clause := [(0, false), (2, false)] }, { id := 96, left := 95, right := 93, pivot := (0, true), clause := [(2, false)] }, { id := 97, left := 96, right := 94, pivot := (2, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 15, right := 92, pivot := (10, true), clause := [(1, true)] }, { id := 95, left := 94, right := 93, pivot := (1, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 16, right := 92, pivot := (10, true), clause := [(3, true)] }, { id := 95, left := 94, right := 93, pivot := (3, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 17, right := 92, pivot := (10, false), clause := [(1, false), (3, false)] }, { id := 96, left := 95, right := 93, pivot := (1, true), clause := [(3, false)] }, { id := 97, left := 96, right := 94, pivot := (3, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 18, right := 92, pivot := (11, true), clause := [(0, true)] }, { id := 95, left := 94, right := 93, pivot := (0, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 19, right := 92, pivot := (11, true), clause := [(2, true)] }, { id := 95, left := 94, right := 93, pivot := (2, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 20, right := 92, pivot := (11, false), clause := [(0, false), (2, false)] }, { id := 96, left := 95, right := 93, pivot := (0, true), clause := [(2, false)] }, { id := 97, left := 96, right := 94, pivot := (2, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 21, right := 92, pivot := (12, true), clause := [(1, true)] }, { id := 95, left := 94, right := 93, pivot := (1, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 22, right := 92, pivot := (12, true), clause := [(3, true)] }, { id := 95, left := 94, right := 93, pivot := (3, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 23, right := 92, pivot := (12, false), clause := [(1, false), (3, false)] }, { id := 96, left := 95, right := 93, pivot := (1, true), clause := [(3, false)] }, { id := 97, left := 96, right := 94, pivot := (3, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 24, right := 92, pivot := (13, false), clause := [(9, true)] }, { id := 95, left := 94, right := 93, pivot := (9, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 25, right := 92, pivot := (13, true), clause := [(9, false)] }, { id := 95, left := 94, right := 93, pivot := (9, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 26, right := 92, pivot := (14, false), clause := [(10, true)] }, { id := 95, left := 94, right := 93, pivot := (10, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 27, right := 92, pivot := (14, true), clause := [(10, false)] }, { id := 95, left := 94, right := 93, pivot := (10, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 28, right := 92, pivot := (15, false), clause := [(11, true)] }, { id := 95, left := 94, right := 93, pivot := (11, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 29, right := 92, pivot := (15, true), clause := [(11, false)] }, { id := 95, left := 94, right := 93, pivot := (11, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 30, right := 92, pivot := (16, false), clause := [(12, true)] }, { id := 95, left := 94, right := 93, pivot := (12, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 31, right := 92, pivot := (16, true), clause := [(12, false)] }, { id := 95, left := 94, right := 93, pivot := (12, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 32, right := 92, pivot := (17, false), clause := [(7, true)] }, { id := 95, left := 94, right := 93, pivot := (7, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 33, right := 92, pivot := (17, true), clause := [(7, false)] }, { id := 95, left := 94, right := 93, pivot := (7, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 34, right := 92, pivot := (18, false), clause := [(8, true)] }, { id := 95, left := 94, right := 93, pivot := (8, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 35, right := 92, pivot := (18, true), clause := [(8, false)] }, { id := 95, left := 94, right := 93, pivot := (8, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 36, right := 92, pivot := (17, false), clause := [(13, true), (19, false)] }, { id := 96, left := 95, right := 93, pivot := (13, false), clause := [(19, false)] }, { id := 97, left := 96, right := 94, pivot := (19, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 37, right := 92, pivot := (17, true), clause := [(13, false), (19, false)] }, { id := 96, left := 95, right := 93, pivot := (13, true), clause := [(19, false)] }, { id := 97, left := 96, right := 94, pivot := (19, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 38, right := 92, pivot := (17, false), clause := [(13, false), (19, true)] }, { id := 96, left := 95, right := 93, pivot := (13, true), clause := [(19, true)] }, { id := 97, left := 96, right := 94, pivot := (19, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 39, right := 92, pivot := (17, true), clause := [(13, true), (19, true)] }, { id := 96, left := 95, right := 93, pivot := (13, false), clause := [(19, true)] }, { id := 97, left := 96, right := 94, pivot := (19, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 40, right := 92, pivot := (17, false), clause := [(14, true), (20, false)] }, { id := 96, left := 95, right := 93, pivot := (14, false), clause := [(20, false)] }, { id := 97, left := 96, right := 94, pivot := (20, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 41, right := 92, pivot := (17, true), clause := [(14, false), (20, false)] }, { id := 96, left := 95, right := 93, pivot := (14, true), clause := [(20, false)] }, { id := 97, left := 96, right := 94, pivot := (20, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 42, right := 92, pivot := (17, false), clause := [(14, false), (20, true)] }, { id := 96, left := 95, right := 93, pivot := (14, true), clause := [(20, true)] }, { id := 97, left := 96, right := 94, pivot := (20, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 43, right := 92, pivot := (17, true), clause := [(14, true), (20, true)] }, { id := 96, left := 95, right := 93, pivot := (14, false), clause := [(20, true)] }, { id := 97, left := 96, right := 94, pivot := (20, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 44, right := 92, pivot := (18, false), clause := [(15, true), (21, false)] }, { id := 96, left := 95, right := 93, pivot := (15, false), clause := [(21, false)] }, { id := 97, left := 96, right := 94, pivot := (21, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 45, right := 92, pivot := (18, true), clause := [(15, false), (21, false)] }, { id := 96, left := 95, right := 93, pivot := (15, true), clause := [(21, false)] }, { id := 97, left := 96, right := 94, pivot := (21, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 46, right := 92, pivot := (18, false), clause := [(15, false), (21, true)] }, { id := 96, left := 95, right := 93, pivot := (15, true), clause := [(21, true)] }, { id := 97, left := 96, right := 94, pivot := (21, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 47, right := 92, pivot := (18, true), clause := [(15, true), (21, true)] }, { id := 96, left := 95, right := 93, pivot := (15, false), clause := [(21, true)] }, { id := 97, left := 96, right := 94, pivot := (21, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 48, right := 92, pivot := (18, false), clause := [(16, true), (22, false)] }, { id := 96, left := 95, right := 93, pivot := (16, false), clause := [(22, false)] }, { id := 97, left := 96, right := 94, pivot := (22, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 49, right := 92, pivot := (18, true), clause := [(16, false), (22, false)] }, { id := 96, left := 95, right := 93, pivot := (16, true), clause := [(22, false)] }, { id := 97, left := 96, right := 94, pivot := (22, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 50, right := 92, pivot := (18, false), clause := [(16, false), (22, true)] }, { id := 96, left := 95, right := 93, pivot := (16, true), clause := [(22, true)] }, { id := 97, left := 96, right := 94, pivot := (22, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 51, right := 92, pivot := (18, true), clause := [(16, true), (22, true)] }, { id := 96, left := 95, right := 93, pivot := (16, false), clause := [(22, true)] }, { id := 97, left := 96, right := 94, pivot := (22, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 52, right := 92, pivot := (23, false), clause := [(17, true)] }, { id := 95, left := 94, right := 93, pivot := (17, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 53, right := 92, pivot := (23, false), clause := [(2, false)] }, { id := 95, left := 94, right := 93, pivot := (2, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 54, right := 92, pivot := (23, true), clause := [(17, false), (2, true)] }, { id := 96, left := 95, right := 93, pivot := (17, true), clause := [(2, true)] }, { id := 97, left := 96, right := 94, pivot := (2, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 55, right := 92, pivot := (24, false), clause := [(17, true)] }, { id := 95, left := 94, right := 93, pivot := (17, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 56, right := 92, pivot := (24, false), clause := [(3, false)] }, { id := 95, left := 94, right := 93, pivot := (3, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 57, right := 92, pivot := (24, true), clause := [(17, false), (3, true)] }, { id := 96, left := 95, right := 93, pivot := (17, true), clause := [(3, true)] }, { id := 97, left := 96, right := 94, pivot := (3, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 58, right := 92, pivot := (25, false), clause := [(18, true)] }, { id := 95, left := 94, right := 93, pivot := (18, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 59, right := 92, pivot := (25, false), clause := [(2, false)] }, { id := 95, left := 94, right := 93, pivot := (2, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 60, right := 92, pivot := (25, true), clause := [(18, false), (2, true)] }, { id := 96, left := 95, right := 93, pivot := (18, true), clause := [(2, true)] }, { id := 97, left := 96, right := 94, pivot := (2, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 61, right := 92, pivot := (26, false), clause := [(18, true)] }, { id := 95, left := 94, right := 93, pivot := (18, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 62, right := 92, pivot := (26, false), clause := [(3, false)] }, { id := 95, left := 94, right := 93, pivot := (3, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 63, right := 92, pivot := (26, true), clause := [(18, false), (3, true)] }, { id := 96, left := 95, right := 93, pivot := (18, true), clause := [(3, true)] }, { id := 97, left := 96, right := 94, pivot := (3, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 64, right := 92, pivot := (27, true), clause := [(0, true)] }, { id := 95, left := 94, right := 93, pivot := (0, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 65, right := 92, pivot := (27, true), clause := [(23, true)] }, { id := 95, left := 94, right := 93, pivot := (23, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 66, right := 92, pivot := (27, false), clause := [(0, false), (23, false)] }, { id := 96, left := 95, right := 93, pivot := (0, true), clause := [(23, false)] }, { id := 97, left := 96, right := 94, pivot := (23, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 67, right := 92, pivot := (28, true), clause := [(1, true)] }, { id := 95, left := 94, right := 93, pivot := (1, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 68, right := 92, pivot := (28, true), clause := [(24, true)] }, { id := 95, left := 94, right := 93, pivot := (24, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 69, right := 92, pivot := (28, false), clause := [(1, false), (24, false)] }, { id := 96, left := 95, right := 93, pivot := (1, true), clause := [(24, false)] }, { id := 97, left := 96, right := 94, pivot := (24, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 70, right := 92, pivot := (29, true), clause := [(0, true)] }, { id := 95, left := 94, right := 93, pivot := (0, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 71, right := 92, pivot := (29, true), clause := [(25, true)] }, { id := 95, left := 94, right := 93, pivot := (25, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 72, right := 92, pivot := (29, false), clause := [(0, false), (25, false)] }, { id := 96, left := 95, right := 93, pivot := (0, true), clause := [(25, false)] }, { id := 97, left := 96, right := 94, pivot := (25, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 73, right := 92, pivot := (30, true), clause := [(1, true)] }, { id := 95, left := 94, right := 93, pivot := (1, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 74, right := 92, pivot := (30, true), clause := [(26, true)] }, { id := 95, left := 94, right := 93, pivot := (26, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 75, right := 92, pivot := (30, false), clause := [(1, false), (26, false)] }, { id := 96, left := 95, right := 93, pivot := (1, true), clause := [(26, false)] }, { id := 97, left := 96, right := 94, pivot := (26, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 76, right := 92, pivot := (31, true), clause := [(28, true)] }, { id := 95, left := 94, right := 93, pivot := (28, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 77, right := 92, pivot := (31, false), clause := [(28, false)] }, { id := 95, left := 94, right := 93, pivot := (28, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 78, right := 92, pivot := (32, true), clause := [(30, true)] }, { id := 95, left := 94, right := 93, pivot := (30, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 79, right := 92, pivot := (32, false), clause := [(30, false)] }, { id := 95, left := 94, right := 93, pivot := (30, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 80, right := 92, pivot := (31, false), clause := [(32, true), (33, false)] }, { id := 96, left := 95, right := 93, pivot := (32, false), clause := [(33, false)] }, { id := 97, left := 96, right := 94, pivot := (33, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 81, right := 92, pivot := (31, true), clause := [(32, false), (33, false)] }, { id := 96, left := 95, right := 93, pivot := (32, true), clause := [(33, false)] }, { id := 97, left := 96, right := 94, pivot := (33, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 82, right := 92, pivot := (31, false), clause := [(32, false), (33, true)] }, { id := 96, left := 95, right := 93, pivot := (32, true), clause := [(33, true)] }, { id := 97, left := 96, right := 94, pivot := (33, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 83, right := 92, pivot := (31, true), clause := [(32, true), (33, true)] }, { id := 96, left := 95, right := 93, pivot := (32, false), clause := [(33, true)] }, { id := 97, left := 96, right := 94, pivot := (33, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 84, right := 92, pivot := (34, false), clause := [(33, false)] }, { id := 95, left := 94, right := 93, pivot := (33, true), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 93, steps := [{ id := 94, left := 85, right := 92, pivot := (34, true), clause := [(33, true)] }, { id := 95, left := 94, right := 93, pivot := (33, false), clause := [] }], finalClauseId := 95 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 86, right := 92, pivot := (13, true), clause := [] }], finalClauseId := 93 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 87, right := 92, pivot := (5, false), clause := [] }], finalClauseId := 93 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 88, right := 92, pivot := (4, false), clause := [] }], finalClauseId := 93 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 89, right := 92, pivot := (35, true), clause := [(31, true), (32, true)] }, { id := 96, left := 95, right := 93, pivot := (31, false), clause := [(32, true)] }, { id := 97, left := 96, right := 94, pivot := (32, false), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 94, steps := [{ id := 95, left := 90, right := 92, pivot := (35, true), clause := [(31, false), (32, false)] }, { id := 96, left := 95, right := 93, pivot := (31, true), clause := [(32, false)] }, { id := 97, left := 96, right := 94, pivot := (32, true), clause := [] }], finalClauseId := 97 },
  .resolution { originalClauseCount := 92, steps := [{ id := 93, left := 91, right := 92, pivot := (35, false), clause := [] }], finalClauseId := 93 }
]

def guards : Array (Controller.Certificate.Certificate 36) := #[
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty 7 #[4, 5, 6, 1]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty 7 #[4, 5, 6, 2]]
]

def necessity : Controller.Certificate.Certificate 36 := .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty 5 #[4, 3]]

def orientations : Array (Controller.Certificate.Certificate 35) := #[
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addRup 93 #[1] #[3, 12, 18, 24, 28, 64, 70, 86],
  Std.Tactic.BVDecide.LRAT.Action.addEmpty
    94
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 77, 90, 79, 75, 21,
      30, 50, 80, 85]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 76, 67, 68, 78, 74, 81, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 57, 17, 23, 27, 1, 9, 31, 34, 43,
      47, 51, 59, 66, 72, 87]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addRup 91 #[1] #[3, 12, 18, 24, 28, 64, 70, 86],
  Std.Tactic.BVDecide.LRAT.Action.addEmpty
    92
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 77, 90, 79, 75, 21,
      30, 50, 80, 85]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 77, 79, 80, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61,
      75, 21, 30, 50, 90]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 76, 67, 68, 78, 74, 81, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 57, 17, 23, 27, 1, 9, 31, 34, 43,
      47, 51, 59, 66, 72, 87]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addRup 91 #[1] #[3, 12, 18, 24, 28, 64, 70, 86],
  Std.Tactic.BVDecide.LRAT.Action.addEmpty
    92
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 77, 90, 78, 73, 17,
      22, 30, 50, 57, 82, 84]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 77, 79, 80, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61,
      75, 21, 30, 50, 89]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 76, 67, 68, 78, 74, 81, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 57, 17, 23, 27, 1, 9, 31, 34, 43,
      47, 51, 59, 66, 72, 87]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    91
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 76, 67, 17, 22, 30,
      50, 57, 68]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 77, 79, 80, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61,
      75, 21, 30, 50, 89]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[91, 92, 3, 76, 67, 68, 78, 74, 81, 85, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 57, 17, 23, 27, 1, 9, 31, 34, 43,
      47, 51, 59, 66, 72, 87]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    91
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 76, 67, 17, 22, 30,
      50, 57, 68]]
]

def targetForward : Array (Controller.Certificate.Certificate 35) := #[
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addRup
    92
    #[32]
    #[3, 77, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 90, 79, 75, 21, 30,
      50, 80, 85],
  Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 77, 90, 79, 75, 21,
      30, 50, 80, 85, 92]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    92
    #[91, 3, 84, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 77, 82, 79,
      75, 21, 30, 50, 90]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    92
    #[91, 3, 84, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 76, 67, 17,
      22, 30, 50, 57, 68]],
  .lrat #[Std.Tactic.BVDecide.LRAT.Action.addEmpty
    92
    #[91, 3, 84, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 76, 67, 17,
      22, 30, 50, 57, 68]]
]

def targetNecessary : Controller.Certificate.Certificate 35 := .lrat #[Std.Tactic.BVDecide.LRAT.Action.addRup
    92
    #[32]
    #[3, 77, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 85, 80, 78, 73,
      17, 22, 30, 50, 57, 91],
  Std.Tactic.BVDecide.LRAT.Action.addEmpty
    93
    #[3, 86, 4, 24, 12, 13, 20, 29, 32, 39, 53, 59, 66, 72, 87, 1, 27, 41, 88, 11, 35, 44, 61, 89, 85, 92, 76, 67, 17,
      22, 30, 50, 57, 68]]

end Controller.Recognition.AcceptanceCertificates
