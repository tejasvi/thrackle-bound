import Thrackle78Facts.N682.Top
import Thrackle78Facts.N682.Filters
import Thrackle78Facts.N682.B0
import Thrackle78Facts.N682.B1
import Thrackle78Facts.N682.B2
import Thrackle78Facts.N682.B3
import Thrackle78Facts.N682.B4
import Thrackle78Facts.N682.B5
import Thrackle78Facts.N682.B6
import Thrackle78Facts.N682.B7
import Thrackle78Facts.N682.B8
import Thrackle78Facts.N682.B9
import Thrackle78Facts.N682.B10
import Thrackle78Facts.N682.B11
import Thrackle78Facts.N682.B12
import Thrackle78Facts.N682.B13
import Thrackle78Facts.N682.B14
import Thrackle78Facts.N682.B15
import Thrackle78Facts.N682.B16
import Thrackle78Facts.N682.B17
import Thrackle78Facts.N682.B18
import Thrackle78Facts.N682.B19
import Thrackle78Facts.N682.B20
import Thrackle78Facts.N682.B21
import Thrackle78Facts.N682.B22
import Thrackle78Facts.N682.B23
import Thrackle78Facts.N682.B24
import Thrackle78Facts.N682.B25
import Thrackle78Facts.N682.B26
import Thrackle78Facts.N682.B27
import Thrackle78Facts.N682.B28
import Thrackle78Facts.N682.B29
import Thrackle78Facts.N682.B30
import Thrackle78Facts.N682.B31
import Thrackle78Facts.N682.B32
import Thrackle78Facts.N682.B33
import Thrackle78Facts.N682.B34
import Thrackle78Facts.N682.B35
import Thrackle78Facts.N682.B36
import Thrackle78Facts.N682.B37
import Thrackle78Facts.N682.B38
import Thrackle78Facts.N682.B39
import Thrackle78Facts.N682.B40
import Thrackle78Facts.N682.B41
import Thrackle78Facts.N682.B42
import Thrackle78Facts.N682.B43
import Thrackle78Facts.N682.B44
import Thrackle78Facts.N682.B45
import Thrackle78Facts.N682.B46
import Thrackle78Facts.N682.B47
import Thrackle78Facts.N682.B48
import Thrackle78Facts.N682.B49
import Thrackle78Facts.N682.B50
import Thrackle78Facts.N682.B51
import Thrackle78Facts.N682.B52
import Thrackle78Facts.N682.B53
import Thrackle78Facts.N682.B54
import Thrackle78Facts.N682.B55
import Thrackle78Facts.N682.B56
import Thrackle78Facts.N682.B57
import Thrackle78Facts.N682.B58
import Thrackle78Facts.N682.B59
import Thrackle78Facts.N682.B60
import Thrackle78Facts.N682.B61
import Thrackle78Facts.N682.B62
import Thrackle78Facts.N682.B63
import Thrackle78Facts.N682.B64
import Thrackle78Facts.N682.B65
import Thrackle78Facts.N682.B66
import Thrackle78Facts.N682.B67
import Thrackle78Facts.N682.B68
import Thrackle78Facts.N682.B69
import Thrackle78Facts.N682.B70
import Thrackle78Facts.N682.B71
import Thrackle78Facts.N682.B72
import Thrackle78Facts.N682.B73
import Thrackle78Facts.N682.B74
import Thrackle78Facts.N682.B75
import Thrackle78Facts.N682.B76
import Thrackle78Facts.N682.B77
import Thrackle78Facts.N682.B78
import Thrackle78Facts.N682.B79
import Thrackle78Facts.N682.B80
import Thrackle78Facts.N682.B81
import Thrackle78Facts.N682.B82
import Thrackle78Facts.N682.B83
import Thrackle78Facts.N682.B84
import Thrackle78Facts.N682.B85
import Thrackle78Facts.N682.B86
import Thrackle78Facts.N682.B87
import Thrackle78Facts.N682.B88
import Thrackle78Facts.N682.B89
import Thrackle78Facts.N682.B90
import Thrackle78Facts.N682.B91
import Thrackle78Facts.N682.B92
import Thrackle78Facts.N682.B93
import Thrackle78Facts.N682.B94
import Thrackle78Facts.N682.B95

/-! `CompFacts.db682`: the listing `lDB682` (as run) is not combinatorially thrackleable: native search with the
oracle `Thrackle78Core.BM.bmOrcKR` (untrusted) and bitset filters, top tree pruned and delegating the 96 batches of
shard states. -/

namespace Thrackle78.Facts

open Thrackle78 Thrackle78Core Thrackle78.Checker

theorem db682 : ¬ CombThr (mkE 11 lDB682) :=
  not_combThr_mkE_of_topB 11 lDB682 (by decide) T78Native.N682.fs T78Native.N682.orcF T78Native.N682.filters_ok T78Native.N682.Ls T78Native.N682.look T78Native.N682.top_ok (by
    intro L hL
    simp only [T78Native.N682.Ls, List.mem_map, List.mem_range] at hL
    obtain ⟨r, hr, rfl⟩ := hL
    interval_cases r
    exacts [T78Native.N682.batch_ok_0,
      T78Native.N682.batch_ok_1,
      T78Native.N682.batch_ok_2,
      T78Native.N682.batch_ok_3,
      T78Native.N682.batch_ok_4,
      T78Native.N682.batch_ok_5,
      T78Native.N682.batch_ok_6,
      T78Native.N682.batch_ok_7,
      T78Native.N682.batch_ok_8,
      T78Native.N682.batch_ok_9,
      T78Native.N682.batch_ok_10,
      T78Native.N682.batch_ok_11,
      T78Native.N682.batch_ok_12,
      T78Native.N682.batch_ok_13,
      T78Native.N682.batch_ok_14,
      T78Native.N682.batch_ok_15,
      T78Native.N682.batch_ok_16,
      T78Native.N682.batch_ok_17,
      T78Native.N682.batch_ok_18,
      T78Native.N682.batch_ok_19,
      T78Native.N682.batch_ok_20,
      T78Native.N682.batch_ok_21,
      T78Native.N682.batch_ok_22,
      T78Native.N682.batch_ok_23,
      T78Native.N682.batch_ok_24,
      T78Native.N682.batch_ok_25,
      T78Native.N682.batch_ok_26,
      T78Native.N682.batch_ok_27,
      T78Native.N682.batch_ok_28,
      T78Native.N682.batch_ok_29,
      T78Native.N682.batch_ok_30,
      T78Native.N682.batch_ok_31,
      T78Native.N682.batch_ok_32,
      T78Native.N682.batch_ok_33,
      T78Native.N682.batch_ok_34,
      T78Native.N682.batch_ok_35,
      T78Native.N682.batch_ok_36,
      T78Native.N682.batch_ok_37,
      T78Native.N682.batch_ok_38,
      T78Native.N682.batch_ok_39,
      T78Native.N682.batch_ok_40,
      T78Native.N682.batch_ok_41,
      T78Native.N682.batch_ok_42,
      T78Native.N682.batch_ok_43,
      T78Native.N682.batch_ok_44,
      T78Native.N682.batch_ok_45,
      T78Native.N682.batch_ok_46,
      T78Native.N682.batch_ok_47,
      T78Native.N682.batch_ok_48,
      T78Native.N682.batch_ok_49,
      T78Native.N682.batch_ok_50,
      T78Native.N682.batch_ok_51,
      T78Native.N682.batch_ok_52,
      T78Native.N682.batch_ok_53,
      T78Native.N682.batch_ok_54,
      T78Native.N682.batch_ok_55,
      T78Native.N682.batch_ok_56,
      T78Native.N682.batch_ok_57,
      T78Native.N682.batch_ok_58,
      T78Native.N682.batch_ok_59,
      T78Native.N682.batch_ok_60,
      T78Native.N682.batch_ok_61,
      T78Native.N682.batch_ok_62,
      T78Native.N682.batch_ok_63,
      T78Native.N682.batch_ok_64,
      T78Native.N682.batch_ok_65,
      T78Native.N682.batch_ok_66,
      T78Native.N682.batch_ok_67,
      T78Native.N682.batch_ok_68,
      T78Native.N682.batch_ok_69,
      T78Native.N682.batch_ok_70,
      T78Native.N682.batch_ok_71,
      T78Native.N682.batch_ok_72,
      T78Native.N682.batch_ok_73,
      T78Native.N682.batch_ok_74,
      T78Native.N682.batch_ok_75,
      T78Native.N682.batch_ok_76,
      T78Native.N682.batch_ok_77,
      T78Native.N682.batch_ok_78,
      T78Native.N682.batch_ok_79,
      T78Native.N682.batch_ok_80,
      T78Native.N682.batch_ok_81,
      T78Native.N682.batch_ok_82,
      T78Native.N682.batch_ok_83,
      T78Native.N682.batch_ok_84,
      T78Native.N682.batch_ok_85,
      T78Native.N682.batch_ok_86,
      T78Native.N682.batch_ok_87,
      T78Native.N682.batch_ok_88,
      T78Native.N682.batch_ok_89,
      T78Native.N682.batch_ok_90,
      T78Native.N682.batch_ok_91,
      T78Native.N682.batch_ok_92,
      T78Native.N682.batch_ok_93,
      T78Native.N682.batch_ok_94,
      T78Native.N682.batch_ok_95])

end Thrackle78.Facts
