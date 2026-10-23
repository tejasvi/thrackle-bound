import Thrackle78Facts.T337.HS90
import Thrackle78Facts.T337.HS91
import Thrackle78Facts.T337.HS92
import Thrackle78Facts.T337.HS93
import Thrackle78Facts.T337.HS94
import Thrackle78Facts.T337.HS95
import Thrackle78Facts.T337.HS96
import Thrackle78Facts.T337.HS97
import Thrackle78Facts.T337.HS98
import Thrackle78Facts.T337.HS99
import Thrackle78Facts.T337.HS100
import Thrackle78Facts.T337.HS101
import Thrackle78Facts.T337.HS102
import Thrackle78Facts.T337.HS103
import Thrackle78Facts.T337.HS104
import Thrackle78Facts.T337.HS105
import Thrackle78Facts.T337.HS106
import Thrackle78Facts.T337.HS107
import Thrackle78Facts.T337.HS108
import Thrackle78Facts.T337.HS109
import Thrackle78Facts.T337.HS110
import Thrackle78Facts.T337.HS111
import Thrackle78Facts.T337.HS112
import Thrackle78Facts.T337.HS113
import Thrackle78Facts.T337.HS114
import Thrackle78Facts.T337.HS115
import Thrackle78Facts.T337.HS116
import Thrackle78Facts.T337.HS117
import Thrackle78Facts.T337.HS118
import Thrackle78Facts.T337.HS119

open Thrackle78 Thrackle78Core

theorem T78Native.T337.hgroup_ok_3 : ∀ j < 30, checkFilterXShardsF 12 lTH337.toArray T78Native.T337.c10aX T78Native.T337.dlook T78Native.T337.orcF T78Native.T337.famOrcF T78Native.T337.adaptF (T78Native.T337.hbatch (30 * 3 + j)) = true := by
  intro j hj
  interval_cases j
  exacts [T78Native.T337.hshard_ok_90,
      T78Native.T337.hshard_ok_91,
      T78Native.T337.hshard_ok_92,
      T78Native.T337.hshard_ok_93,
      T78Native.T337.hshard_ok_94,
      T78Native.T337.hshard_ok_95,
      T78Native.T337.hshard_ok_96,
      T78Native.T337.hshard_ok_97,
      T78Native.T337.hshard_ok_98,
      T78Native.T337.hshard_ok_99,
      T78Native.T337.hshard_ok_100,
      T78Native.T337.hshard_ok_101,
      T78Native.T337.hshard_ok_102,
      T78Native.T337.hshard_ok_103,
      T78Native.T337.hshard_ok_104,
      T78Native.T337.hshard_ok_105,
      T78Native.T337.hshard_ok_106,
      T78Native.T337.hshard_ok_107,
      T78Native.T337.hshard_ok_108,
      T78Native.T337.hshard_ok_109,
      T78Native.T337.hshard_ok_110,
      T78Native.T337.hshard_ok_111,
      T78Native.T337.hshard_ok_112,
      T78Native.T337.hshard_ok_113,
      T78Native.T337.hshard_ok_114,
      T78Native.T337.hshard_ok_115,
      T78Native.T337.hshard_ok_116,
      T78Native.T337.hshard_ok_117,
      T78Native.T337.hshard_ok_118,
      T78Native.T337.hshard_ok_119]
