import Thrackle78Facts.N681.Top
import Thrackle78Facts.N681.FiltersT
import Thrackle78Facts.N681.Idxh12
import Thrackle78Facts.N681.Idxh54
import Thrackle78Facts.N681.Soundh12
import Thrackle78Facts.N681.Soundh54
import Thrackle78Facts.N681.G0
import Thrackle78Facts.N681.G1
import Thrackle78Facts.N681.G2
import Thrackle78Facts.N681.G3
import Thrackle78Facts.N681.G4
import Thrackle78Facts.N681.G5
import Thrackle78Facts.N681.G6
import Thrackle78Facts.N681.G7
import Thrackle78Facts.N681.G8
import Thrackle78Facts.N681.G9
import Thrackle78Facts.N681.G10
import Thrackle78Facts.N681.G11
import Thrackle78Facts.N681.G12
import Thrackle78Facts.N681.G13
import Thrackle78Facts.N681.G14
import Thrackle78Facts.N681.G15
import Thrackle78Facts.N681.G16
import Thrackle78Facts.N681.G17
import Thrackle78Facts.N681.G18
import Thrackle78Facts.N681.G19
import Thrackle78Facts.N681.G20
import Thrackle78Facts.N681.G21
import Thrackle78Facts.N681.G22
import Thrackle78Facts.N681.G23
import Thrackle78Facts.N681.G24
import Thrackle78Facts.N681.G25
import Thrackle78Facts.N681.G26
import Thrackle78Facts.N681.G27
import Thrackle78Facts.N681.G28
import Thrackle78Facts.N681.G29

/-! `CompFacts.db681`: the listing `lDB681` (as run) is not combinatorially thrackleable: symmetry-reduced native
search with the oracle family `T78Native.N681.orcF` (untrusted), family hints, and the indexed filters
h12, h54 (bucket checks; `h12` by its sharded filter tree, the others as its
images under the symmetry) restricted at the shard roots; top tree pruned with the filters `T78Native.N681.fsT`, skipping
non-canonical states and delegating the 1200 batches of shard states (30 groups of 40). -/

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem T78Native.N681.groups_ok : ∀ g < 30, ∀ j < 40, checkBFromListRX 12 lDB681.toArray T78Native.N681.fsX (T78Native.N681.orcF lDB681.toArray) (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) (T78Native.N681.batch (40 * g + j)) = true := by
  intro g hg
  interval_cases g
  exacts [T78Native.N681.group_ok_0,
      T78Native.N681.group_ok_1,
      T78Native.N681.group_ok_2,
      T78Native.N681.group_ok_3,
      T78Native.N681.group_ok_4,
      T78Native.N681.group_ok_5,
      T78Native.N681.group_ok_6,
      T78Native.N681.group_ok_7,
      T78Native.N681.group_ok_8,
      T78Native.N681.group_ok_9,
      T78Native.N681.group_ok_10,
      T78Native.N681.group_ok_11,
      T78Native.N681.group_ok_12,
      T78Native.N681.group_ok_13,
      T78Native.N681.group_ok_14,
      T78Native.N681.group_ok_15,
      T78Native.N681.group_ok_16,
      T78Native.N681.group_ok_17,
      T78Native.N681.group_ok_18,
      T78Native.N681.group_ok_19,
      T78Native.N681.group_ok_20,
      T78Native.N681.group_ok_21,
      T78Native.N681.group_ok_22,
      T78Native.N681.group_ok_23,
      T78Native.N681.group_ok_24,
      T78Native.N681.group_ok_25,
      T78Native.N681.group_ok_26,
      T78Native.N681.group_ok_27,
      T78Native.N681.group_ok_28,
      T78Native.N681.group_ok_29]

namespace Thrackle78.Facts

theorem db681 : ¬ CombThr (mkE 12 lDB681) :=
  not_combThr_mkE_of_topBSymRFX 12 lDB681 (by decide) T78Native.N681.fsT T78Native.N681.orcF T78Native.N681.filtersT_ok T78Native.N681.fsX (by
      intro φ hφ
      simp only [T78Native.N681.fsX, List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact ⟨T78Native.N681.idx_ok_h12, T78Native.N681.sound_h12.1, T78Native.N681.sound_h12.2⟩
      · exact ⟨T78Native.N681.idx_ok_h54, T78Native.N681.sound_h54.1, T78Native.N681.sound_h54.2⟩)
    (T78Native.N681.famOrcF lDB681.toArray) (T78Native.N681.adaptF lDB681.toArray) T78Native.N681.Ls T78Native.N681.look 10 R681 σ681 flip681 hR681 hσR681 hsym681
    T78Native.N681.top_ok (by
      intro L hL
      simp only [T78Native.N681.Ls, List.mem_map, List.mem_range] at hL
      obtain ⟨r, hr, rfl⟩ := hL
      have h := T78Native.N681.groups_ok (r / 40) (by omega) (r % 40) (Nat.mod_lt _ (by norm_num))
      rwa [Nat.div_add_mod] at h)

end Thrackle78.Facts
