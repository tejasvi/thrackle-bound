import Thrackle78Facts.N681.HS90
import Thrackle78Facts.N681.HS91
import Thrackle78Facts.N681.HS92
import Thrackle78Facts.N681.HS93
import Thrackle78Facts.N681.HS94
import Thrackle78Facts.N681.HS95
import Thrackle78Facts.N681.HS96
import Thrackle78Facts.N681.HS97
import Thrackle78Facts.N681.HS98
import Thrackle78Facts.N681.HS99
import Thrackle78Facts.N681.HS100
import Thrackle78Facts.N681.HS101
import Thrackle78Facts.N681.HS102
import Thrackle78Facts.N681.HS103
import Thrackle78Facts.N681.HS104
import Thrackle78Facts.N681.HS105
import Thrackle78Facts.N681.HS106
import Thrackle78Facts.N681.HS107
import Thrackle78Facts.N681.HS108
import Thrackle78Facts.N681.HS109
import Thrackle78Facts.N681.HS110
import Thrackle78Facts.N681.HS111
import Thrackle78Facts.N681.HS112
import Thrackle78Facts.N681.HS113
import Thrackle78Facts.N681.HS114
import Thrackle78Facts.N681.HS115
import Thrackle78Facts.N681.HS116
import Thrackle78Facts.N681.HS117
import Thrackle78Facts.N681.HS118
import Thrackle78Facts.N681.HS119

open Thrackle78 Thrackle78Core

theorem T78Native.N681.hgroup_ok_3 : ∀ j < 30, checkFilterXShards 12 lDB681.toArray T78Native.N681.h12X T78Native.N681.h12look T78Native.N681.orcF (T78Native.N681.hbatch (30 * 3 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.N681.hshard_ok_90,
      T78Native.N681.hshard_ok_91,
      T78Native.N681.hshard_ok_92,
      T78Native.N681.hshard_ok_93,
      T78Native.N681.hshard_ok_94,
      T78Native.N681.hshard_ok_95,
      T78Native.N681.hshard_ok_96,
      T78Native.N681.hshard_ok_97,
      T78Native.N681.hshard_ok_98,
      T78Native.N681.hshard_ok_99,
      T78Native.N681.hshard_ok_100,
      T78Native.N681.hshard_ok_101,
      T78Native.N681.hshard_ok_102,
      T78Native.N681.hshard_ok_103,
      T78Native.N681.hshard_ok_104,
      T78Native.N681.hshard_ok_105,
      T78Native.N681.hshard_ok_106,
      T78Native.N681.hshard_ok_107,
      T78Native.N681.hshard_ok_108,
      T78Native.N681.hshard_ok_109,
      T78Native.N681.hshard_ok_110,
      T78Native.N681.hshard_ok_111,
      T78Native.N681.hshard_ok_112,
      T78Native.N681.hshard_ok_113,
      T78Native.N681.hshard_ok_114,
      T78Native.N681.hshard_ok_115,
      T78Native.N681.hshard_ok_116,
      T78Native.N681.hshard_ok_117,
      T78Native.N681.hshard_ok_118,
      T78Native.N681.hshard_ok_119]
