import Thrackle78Facts.N660.Top
import Thrackle78Facts.N660.Filters
import Thrackle78Facts.N660.B0
import Thrackle78Facts.N660.B1
import Thrackle78Facts.N660.B2
import Thrackle78Facts.N660.B3
import Thrackle78Facts.N660.B4
import Thrackle78Facts.N660.B5
import Thrackle78Facts.N660.B6
import Thrackle78Facts.N660.B7
import Thrackle78Facts.N660.B8
import Thrackle78Facts.N660.B9
import Thrackle78Facts.N660.B10
import Thrackle78Facts.N660.B11
import Thrackle78Facts.N660.B12
import Thrackle78Facts.N660.B13
import Thrackle78Facts.N660.B14
import Thrackle78Facts.N660.B15
import Thrackle78Facts.N660.B16
import Thrackle78Facts.N660.B17
import Thrackle78Facts.N660.B18
import Thrackle78Facts.N660.B19
import Thrackle78Facts.N660.B20
import Thrackle78Facts.N660.B21
import Thrackle78Facts.N660.B22
import Thrackle78Facts.N660.B23
import Thrackle78Facts.N660.B24
import Thrackle78Facts.N660.B25
import Thrackle78Facts.N660.B26
import Thrackle78Facts.N660.B27
import Thrackle78Facts.N660.B28
import Thrackle78Facts.N660.B29
import Thrackle78Facts.N660.B30
import Thrackle78Facts.N660.B31
import Thrackle78Facts.N660.B32
import Thrackle78Facts.N660.B33
import Thrackle78Facts.N660.B34
import Thrackle78Facts.N660.B35
import Thrackle78Facts.N660.B36
import Thrackle78Facts.N660.B37
import Thrackle78Facts.N660.B38
import Thrackle78Facts.N660.B39
import Thrackle78Facts.N660.B40
import Thrackle78Facts.N660.B41
import Thrackle78Facts.N660.B42
import Thrackle78Facts.N660.B43
import Thrackle78Facts.N660.B44
import Thrackle78Facts.N660.B45
import Thrackle78Facts.N660.B46
import Thrackle78Facts.N660.B47

/-! `CompFacts.db660`: the listing `lDB660` (as run) is not combinatorially thrackleable: native search with the
oracle `Thrackle78Core.BM.bmOrcKR` (untrusted) and bitset filters, top tree pruned and delegating the 48 batches of
shard states. -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem db660 : ¬ CombThr (mkE 11 lDB660) :=
  not_combThr_mkE_of_topB 11 lDB660 (by decide) T78Native.N660.fs T78Native.N660.orcF T78Native.N660.filters_ok T78Native.N660.Ls T78Native.N660.look T78Native.N660.top_ok (by
    intro L hL
    simp only [T78Native.N660.Ls, List.mem_map, List.mem_range] at hL
    obtain ⟨r, hr, rfl⟩ := hL
    interval_cases r
    exacts [T78Native.N660.batch_ok_0,
      T78Native.N660.batch_ok_1,
      T78Native.N660.batch_ok_2,
      T78Native.N660.batch_ok_3,
      T78Native.N660.batch_ok_4,
      T78Native.N660.batch_ok_5,
      T78Native.N660.batch_ok_6,
      T78Native.N660.batch_ok_7,
      T78Native.N660.batch_ok_8,
      T78Native.N660.batch_ok_9,
      T78Native.N660.batch_ok_10,
      T78Native.N660.batch_ok_11,
      T78Native.N660.batch_ok_12,
      T78Native.N660.batch_ok_13,
      T78Native.N660.batch_ok_14,
      T78Native.N660.batch_ok_15,
      T78Native.N660.batch_ok_16,
      T78Native.N660.batch_ok_17,
      T78Native.N660.batch_ok_18,
      T78Native.N660.batch_ok_19,
      T78Native.N660.batch_ok_20,
      T78Native.N660.batch_ok_21,
      T78Native.N660.batch_ok_22,
      T78Native.N660.batch_ok_23,
      T78Native.N660.batch_ok_24,
      T78Native.N660.batch_ok_25,
      T78Native.N660.batch_ok_26,
      T78Native.N660.batch_ok_27,
      T78Native.N660.batch_ok_28,
      T78Native.N660.batch_ok_29,
      T78Native.N660.batch_ok_30,
      T78Native.N660.batch_ok_31,
      T78Native.N660.batch_ok_32,
      T78Native.N660.batch_ok_33,
      T78Native.N660.batch_ok_34,
      T78Native.N660.batch_ok_35,
      T78Native.N660.batch_ok_36,
      T78Native.N660.batch_ok_37,
      T78Native.N660.batch_ok_38,
      T78Native.N660.batch_ok_39,
      T78Native.N660.batch_ok_40,
      T78Native.N660.batch_ok_41,
      T78Native.N660.batch_ok_42,
      T78Native.N660.batch_ok_43,
      T78Native.N660.batch_ok_44,
      T78Native.N660.batch_ok_45,
      T78Native.N660.batch_ok_46,
      T78Native.N660.batch_ok_47])

end Thrackle78.Facts
