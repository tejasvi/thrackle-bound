import Thrackle78Facts.T337.HTopc10a
import Thrackle78Facts.T337.HG0
import Thrackle78Facts.T337.HG1
import Thrackle78Facts.T337.HG2
import Thrackle78Facts.T337.HG3
import Thrackle78Facts.T337.HG4
import Thrackle78Facts.T337.HG5
import Thrackle78Facts.T337.HG6
import Thrackle78Facts.T337.HG7
import Thrackle78Facts.T337.HG8
import Thrackle78Facts.T337.HG9
import Thrackle78Facts.T337.HG10
import Thrackle78Facts.T337.HG11
import Thrackle78Facts.T337.HG12
import Thrackle78Facts.T337.HG13
import Thrackle78Facts.T337.HG14
import Thrackle78Facts.T337.HG15
import Thrackle78Facts.T337.HG16
import Thrackle78Facts.T337.HG17
import Thrackle78Facts.T337.HG18
import Thrackle78Facts.T337.HG19

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem T78Native.T337.hgroups_ok : ∀ g < 20, ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * g + j)) = true := by
  intro g hg
  interval_cases g
  exacts [T78Native.T337.hgroup_ok_0,
      T78Native.T337.hgroup_ok_1,
      T78Native.T337.hgroup_ok_2,
      T78Native.T337.hgroup_ok_3,
      T78Native.T337.hgroup_ok_4,
      T78Native.T337.hgroup_ok_5,
      T78Native.T337.hgroup_ok_6,
      T78Native.T337.hgroup_ok_7,
      T78Native.T337.hgroup_ok_8,
      T78Native.T337.hgroup_ok_9,
      T78Native.T337.hgroup_ok_10,
      T78Native.T337.hgroup_ok_11,
      T78Native.T337.hgroup_ok_12,
      T78Native.T337.hgroup_ok_13,
      T78Native.T337.hgroup_ok_14,
      T78Native.T337.hgroup_ok_15,
      T78Native.T337.hgroup_ok_16,
      T78Native.T337.hgroup_ok_17,
      T78Native.T337.hgroup_ok_18,
      T78Native.T337.hgroup_ok_19]

/-- The logical filter of `c10a` is sound (its sharded filter tree, shards with family hints). -/
theorem T78Native.T337.sound_c10a : T78Native.T337.c10aX.toFilt.valid lTH337.length = true ∧ FiltSound (mkE 12 lTH337) T78Native.T337.c10aX.toFilt :=
  filtSoundXF (matches_mkE 12 lTH337 (by decide)) T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF T78Native.T337.hLs
    T78Native.T337.hlook T78Native.T337.htop_ok (by
    intro L hL
    simp only [T78Native.T337.hLs, List.mem_map, List.mem_range] at hL
    obtain ⟨r, hr, rfl⟩ := hL
    have h := T78Native.T337.hgroups_ok (r / 30) (by omega) (r % 30) (Nat.mod_lt _ (by norm_num))
    rwa [Nat.div_add_mod] at h)
