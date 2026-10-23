import Thrackle78Facts.N681.HToph12
import Thrackle78Facts.N681.HG0
import Thrackle78Facts.N681.HG1
import Thrackle78Facts.N681.HG2
import Thrackle78Facts.N681.HG3
import Thrackle78Facts.N681.HG4
import Thrackle78Facts.N681.HG5
import Thrackle78Facts.N681.HG6
import Thrackle78Facts.N681.HG7
import Thrackle78Facts.N681.HG8
import Thrackle78Facts.N681.HG9

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem T78Native.N681.hgroups_ok : ∀ g < 10, ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * g + j)) = true := by
  intro g hg
  interval_cases g
  exacts [T78Native.N681.hgroup_ok_0,
      T78Native.N681.hgroup_ok_1,
      T78Native.N681.hgroup_ok_2,
      T78Native.N681.hgroup_ok_3,
      T78Native.N681.hgroup_ok_4,
      T78Native.N681.hgroup_ok_5,
      T78Native.N681.hgroup_ok_6,
      T78Native.N681.hgroup_ok_7,
      T78Native.N681.hgroup_ok_8,
      T78Native.N681.hgroup_ok_9]

/-- The logical filter of `h12` is sound (its sharded filter tree). -/
theorem T78Native.N681.sound_h12 : T78Native.N681.h12X.toFilt.valid lDB681.length = true ∧ FiltSound (mkE 12 lDB681) T78Native.N681.h12X.toFilt :=
  filtSoundX (matches_mkE 12 lDB681 (by decide)) T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF T78Native.N681.hLs T78Native.N681.hlook T78Native.N681.htop_ok (by
    intro L hL
    simp only [T78Native.N681.hLs, List.mem_map, List.mem_range] at hL
    obtain ⟨r, hr, rfl⟩ := hL
    have h := T78Native.N681.hgroups_ok (r / 30) (by omega) (r % 30) (Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at h)
