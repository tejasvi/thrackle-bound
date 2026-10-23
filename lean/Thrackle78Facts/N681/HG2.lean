import Thrackle78Facts.N681.HS60
import Thrackle78Facts.N681.HS61
import Thrackle78Facts.N681.HS62
import Thrackle78Facts.N681.HS63
import Thrackle78Facts.N681.HS64
import Thrackle78Facts.N681.HS65
import Thrackle78Facts.N681.HS66
import Thrackle78Facts.N681.HS67
import Thrackle78Facts.N681.HS68
import Thrackle78Facts.N681.HS69
import Thrackle78Facts.N681.HS70
import Thrackle78Facts.N681.HS71
import Thrackle78Facts.N681.HS72
import Thrackle78Facts.N681.HS73
import Thrackle78Facts.N681.HS74
import Thrackle78Facts.N681.HS75
import Thrackle78Facts.N681.HS76
import Thrackle78Facts.N681.HS77
import Thrackle78Facts.N681.HS78
import Thrackle78Facts.N681.HS79
import Thrackle78Facts.N681.HS80
import Thrackle78Facts.N681.HS81
import Thrackle78Facts.N681.HS82
import Thrackle78Facts.N681.HS83
import Thrackle78Facts.N681.HS84
import Thrackle78Facts.N681.HS85
import Thrackle78Facts.N681.HS86
import Thrackle78Facts.N681.HS87
import Thrackle78Facts.N681.HS88
import Thrackle78Facts.N681.HS89

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_2 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 2 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_60,
      T78Native.N681.hshard_ok_61,
      T78Native.N681.hshard_ok_62,
      T78Native.N681.hshard_ok_63,
      T78Native.N681.hshard_ok_64,
      T78Native.N681.hshard_ok_65,
      T78Native.N681.hshard_ok_66,
      T78Native.N681.hshard_ok_67,
      T78Native.N681.hshard_ok_68,
      T78Native.N681.hshard_ok_69,
      T78Native.N681.hshard_ok_70,
      T78Native.N681.hshard_ok_71,
      T78Native.N681.hshard_ok_72,
      T78Native.N681.hshard_ok_73,
      T78Native.N681.hshard_ok_74,
      T78Native.N681.hshard_ok_75,
      T78Native.N681.hshard_ok_76,
      T78Native.N681.hshard_ok_77,
      T78Native.N681.hshard_ok_78,
      T78Native.N681.hshard_ok_79,
      T78Native.N681.hshard_ok_80,
      T78Native.N681.hshard_ok_81,
      T78Native.N681.hshard_ok_82,
      T78Native.N681.hshard_ok_83,
      T78Native.N681.hshard_ok_84,
      T78Native.N681.hshard_ok_85,
      T78Native.N681.hshard_ok_86,
      T78Native.N681.hshard_ok_87,
      T78Native.N681.hshard_ok_88,
      T78Native.N681.hshard_ok_89]
