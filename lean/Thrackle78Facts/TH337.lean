import Thrackle78Facts.T337.Top
import Thrackle78Facts.T337.Idxc10a
import Thrackle78Facts.T337.Idxc10b
import Thrackle78Facts.T337.Soundc10a
import Thrackle78Facts.T337.Soundc10b
import Thrackle78Facts.T337.G0
import Thrackle78Facts.T337.G1
import Thrackle78Facts.T337.G2
import Thrackle78Facts.T337.G3
import Thrackle78Facts.T337.G4
import Thrackle78Facts.T337.G5
import Thrackle78Facts.T337.G6
import Thrackle78Facts.T337.G7
import Thrackle78Facts.T337.G8
import Thrackle78Facts.T337.G9
import Thrackle78Facts.T337.G10
import Thrackle78Facts.T337.G11
import Thrackle78Facts.T337.G12
import Thrackle78Facts.T337.G13
import Thrackle78Facts.T337.G14
import Thrackle78Facts.T337.G15
import Thrackle78Facts.T337.G16
import Thrackle78Facts.T337.G17
import Thrackle78Facts.T337.G18
import Thrackle78Facts.T337.G19
import Thrackle78Facts.T337.G20
import Thrackle78Facts.T337.G21
import Thrackle78Facts.T337.G22
import Thrackle78Facts.T337.G23
import Thrackle78Facts.T337.G24
import Thrackle78Facts.T337.G25
import Thrackle78Facts.T337.G26
import Thrackle78Facts.T337.G27
import Thrackle78Facts.T337.G28
import Thrackle78Facts.T337.G29

/-! `th337`: the listing `lTH337` (as run) is not combinatorially thrackleable: native search symmetry-reduced by the
edge maps `syms337` (`symSkipL`), with the oracle family `T78Native.T337.orcF` (untrusted), family hints and the indexed filters
`c10a`, `c10b` restricted at the shard roots (bucket checks; `c10a` by its sharded filter tree, `c10b` as its image under an
automorphism); top tree pruned with their bucket keys (`FiltX.topFilt 7`), skipping non-canonical states and
delegating the 1200 batches of shard states (30 groups of 40). -/

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem T78Native.T337.groups_ok : ∀ g < 30, ∀ j < 40, checkBFromListRX 12 lTH337.toArray T78Native.T337.fsX (T78Native.T337.orcF lTH337.toArray) (T78Native.T337.famOrcF lTH337.toArray) (T78Native.T337.adaptF lTH337.toArray) (T78Native.T337.batch (40 * g + j)) = true := by
  intro g hg
  interval_cases g
  exacts [T78Native.T337.group_ok_0,
      T78Native.T337.group_ok_1,
      T78Native.T337.group_ok_2,
      T78Native.T337.group_ok_3,
      T78Native.T337.group_ok_4,
      T78Native.T337.group_ok_5,
      T78Native.T337.group_ok_6,
      T78Native.T337.group_ok_7,
      T78Native.T337.group_ok_8,
      T78Native.T337.group_ok_9,
      T78Native.T337.group_ok_10,
      T78Native.T337.group_ok_11,
      T78Native.T337.group_ok_12,
      T78Native.T337.group_ok_13,
      T78Native.T337.group_ok_14,
      T78Native.T337.group_ok_15,
      T78Native.T337.group_ok_16,
      T78Native.T337.group_ok_17,
      T78Native.T337.group_ok_18,
      T78Native.T337.group_ok_19,
      T78Native.T337.group_ok_20,
      T78Native.T337.group_ok_21,
      T78Native.T337.group_ok_22,
      T78Native.T337.group_ok_23,
      T78Native.T337.group_ok_24,
      T78Native.T337.group_ok_25,
      T78Native.T337.group_ok_26,
      T78Native.T337.group_ok_27,
      T78Native.T337.group_ok_28,
      T78Native.T337.group_ok_29]

theorem T78Native.T337.soundT : ∀ φ ∈ T78Native.T337.fsT, φ.valid lTH337.length = true ∧ FiltSound (mkE 12 lTH337) φ := by
  intro φ hφ
  simp only [T78Native.T337.fsT, List.mem_cons, List.mem_nil_iff, or_false] at hφ
  rcases hφ with rfl | rfl
  · exact topFilt_sound _ T78Native.T337.idx_ok_c10a T78Native.T337.sound_c10a.1 T78Native.T337.sound_c10a.2 (by decide) (by decide)
  · exact topFilt_sound _ T78Native.T337.idx_ok_c10b T78Native.T337.sound_c10b.1 T78Native.T337.sound_c10b.2 (by decide) (by decide)

namespace Thrackle78.Facts

theorem th337 : ¬ CombThr (mkE 12 lTH337) :=
  not_combThr_mkE_of_topBSymLFX 12 lTH337 (by decide) T78Native.T337.fsT T78Native.T337.soundT (T78Native.T337.orcF lTH337.toArray) T78Native.T337.fsX (by
      intro φ hφ
      simp only [T78Native.T337.fsX, List.mem_cons, List.mem_nil_iff, or_false] at hφ
      rcases hφ with rfl | rfl
      · exact ⟨T78Native.T337.idx_ok_c10a, T78Native.T337.sound_c10a.1, T78Native.T337.sound_c10a.2⟩
      · exact ⟨T78Native.T337.idx_ok_c10b, T78Native.T337.sound_c10b.1, T78Native.T337.sound_c10b.2⟩)
    (T78Native.T337.famOrcF lTH337.toArray) (T78Native.T337.adaptF lTH337.toArray) T78Native.T337.Ls T78Native.T337.look 10 R337 syms337 hR337 hσR337 hsym337
    T78Native.T337.top_ok (by
      intro L hL
      simp only [T78Native.T337.Ls, List.mem_map, List.mem_range] at hL
      obtain ⟨r, hr, rfl⟩ := hL
      have h := T78Native.T337.groups_ok (r / 40) (by omega) (r % 40) (Nat.mod_lt _ (by norm_num))
      rwa [Nat.div_add_mod] at h)

end Thrackle78.Facts
